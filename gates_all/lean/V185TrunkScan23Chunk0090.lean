import V185TrunkScan23Chunk0089

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_533281 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 1, 9]
def baseStart_533281 : Nat := 118140960795 + 533281 * 2 ^ 59
def prefixEnd_533281 : Nat := 4983230072969 + 3 ^ 40 * 533281 * 2
def baseEnd_533281 : Nat := 91276492303477756444997

theorem tailTrace_533281 : CollatzResearch.WordTrace tailWord_533281 prefixEnd_533281 91276492303477756444997 := by
  unfold tailWord_533281
  simp only [CollatzResearch.WordTrace]
  refine ⟨19450355981021488988887697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12966903987347659325925131 19450355981021488988887697)
  ·
    refine ⟨14587766985766116741665773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19450355981021488988887697 14587766985766116741665773)
    ·
      refine ⟨5470412619662293778124665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14587766985766116741665773 5470412619662293778124665)
      ·
        refine ⟨4102809464746720333593499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5470412619662293778124665 4102809464746720333593499)
        ·
          refine ⟨6154214197120080500390249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102809464746720333593499 6154214197120080500390249)
          ·
            refine ⟨4615660647840060375292687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6154214197120080500390249 4615660647840060375292687)
            ·
              refine ⟨6923490971760090562939031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4615660647840060375292687 6923490971760090562939031)
              ·
                refine ⟨10385236457640135844408547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6923490971760090562939031 10385236457640135844408547)
                ·
                  refine ⟨15577854686460203766612821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10385236457640135844408547 15577854686460203766612821)
                  ·
                    refine ⟨91276492303477756444997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15577854686460203766612821 91276492303477756444997)
                    ·
                      rfl

theorem cell23_533281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_533281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533281 prefixEnd_533281 := by exact prefixLift 533281
  have htrace : WordTrace (prefixWord ++ tailWord_533281) baseStart_533281 baseEnd_533281 := by
    simpa [prefixWord, tailWord_533281, baseEnd_533281] using wordTrace_append hprefix tailTrace_533281
  have hstable : (prefixWord ++ tailWord_533281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533281).length < 2 ^ (prefixWord ++ tailWord_533281).sum := by decide
  have hdescent : baseEnd_533281 < baseStart_533281 := by decide
  rcases family_descends (prefixWord ++ tailWord_533281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533302 : List Nat := [5, 1, 2, 2, 2, 1, 3, 7]
def baseStart_533302 : Nat := 118140960795 + 533302 * 2 ^ 59
def prefixEnd_533302 : Nat := 4983230072969 + 3 ^ 40 * 533302 * 2
def baseEnd_533302 : Nat := 10142231852006581006385

theorem tailTrace_533302 : CollatzResearch.WordTrace tailWord_533302 prefixEnd_533302 10142231852006581006385 := by
  unfold tailWord_533302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1215695119621588098462635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12967414609296939716934773 1215695119621588098462635)
  ·
    refine ⟨1823542679432382147693953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1215695119621588098462635 1823542679432382147693953)
    ·
      refine ⟨1367657009574286610770465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1823542679432382147693953 1367657009574286610770465)
      ·
        refine ⟨1025742757180714958077849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1367657009574286610770465 1025742757180714958077849)
        ·
          refine ⟨769307067885536218558387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1025742757180714958077849 769307067885536218558387)
          ·
            refine ⟨1153960601828304327837581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769307067885536218558387 1153960601828304327837581)
            ·
              refine ⟨432735225685614122939093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1153960601828304327837581 432735225685614122939093)
              ·
                refine ⟨10142231852006581006385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 432735225685614122939093 10142231852006581006385)
                ·
                  rfl

theorem cell23_533302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_533302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533302 prefixEnd_533302 := by exact prefixLift 533302
  have htrace : WordTrace (prefixWord ++ tailWord_533302) baseStart_533302 baseEnd_533302 := by
    simpa [prefixWord, tailWord_533302, baseEnd_533302] using wordTrace_append hprefix tailTrace_533302
  have hstable : (prefixWord ++ tailWord_533302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533302).length < 2 ^ (prefixWord ++ tailWord_533302).sum := by decide
  have hdescent : baseEnd_533302 < baseStart_533302 := by decide
  rcases family_descends (prefixWord ++ tailWord_533302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533313 : List Nat := [1, 2, 5, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_533313 : Nat := 118140960795 + 533313 * 2 ^ 59
def prefixEnd_533313 : Nat := 4983230072969 + 3 ^ 40 * 533313 * 2
def baseEnd_533313 : Nat := 273845908291377144134845

theorem tailTrace_533313 : CollatzResearch.WordTrace tailWord_533313 prefixEnd_533313 273845908291377144134845 := by
  unfold tailWord_533313
  simp only [CollatzResearch.WordTrace]
  refine ⟨19451523116905558454052593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12967682077937038969368395 19451523116905558454052593)
  ·
    refine ⟨14588642337679168840539445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19451523116905558454052593 14588642337679168840539445)
    ·
      refine ⟨1367685219157422078800573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14588642337679168840539445 1367685219157422078800573)
      ·
        refine ⟨512881957184033279550215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1367685219157422078800573 512881957184033279550215)
        ·
          refine ⟨769322935776049919325323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512881957184033279550215 769322935776049919325323)
          ·
            refine ⟨1153984403664074878987985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769322935776049919325323 1153984403664074878987985)
            ·
              refine ⟨865488302748056159240989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1153984403664074878987985 865488302748056159240989)
              ·
                refine ⟨324558113530521059715371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 865488302748056159240989 324558113530521059715371)
                ·
                  refine ⟨486837170295781589573057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324558113530521059715371 486837170295781589573057)
                  ·
                    refine ⟨365127877721836192179793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 486837170295781589573057 365127877721836192179793)
                    ·
                      refine ⟨273845908291377144134845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365127877721836192179793 273845908291377144134845)
                      ·
                        rfl

theorem cell23_533313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_533313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533313 prefixEnd_533313 := by exact prefixLift 533313
  have htrace : WordTrace (prefixWord ++ tailWord_533313) baseStart_533313 baseEnd_533313 := by
    simpa [prefixWord, tailWord_533313, baseEnd_533313] using wordTrace_append hprefix tailTrace_533313
  have hstable : (prefixWord ++ tailWord_533313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533313).length < 2 ^ (prefixWord ++ tailWord_533313).sum := by decide
  have hdescent : baseEnd_533313 < baseStart_533313 := by decide
  rcases family_descends (prefixWord ++ tailWord_533313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533329 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 2, 1, 3]
def baseStart_533329 : Nat := 118140960795 + 533329 * 2 ^ 59
def prefixEnd_533329 : Nat := 4983230072969 + 3 ^ 40 * 533329 * 2
def baseEnd_533329 : Nat := 273854123981849081534771

theorem tailTrace_533329 : CollatzResearch.WordTrace tailWord_533329 prefixEnd_533329 273854123981849081534771 := by
  unfold tailWord_533329
  simp only [CollatzResearch.WordTrace]
  refine ⟨19452106684847593186635041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12968071123231728791090027 19452106684847593186635041)
  ·
    refine ⟨14589080013635694889976281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19452106684847593186635041 14589080013635694889976281)
    ·
      refine ⟨10941810010226771167482211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14589080013635694889976281 10941810010226771167482211)
      ·
        refine ⟨16412715015340156751223317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10941810010226771167482211 16412715015340156751223317)
        ·
          refine ⟨769346016344069847713593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16412715015340156751223317 769346016344069847713593)
          ·
            refine ⟨577009512258052385785195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769346016344069847713593 577009512258052385785195)
            ·
              refine ⟨865514268387078578677793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577009512258052385785195 865514268387078578677793)
              ·
                refine ⟨649135701290308934008345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865514268387078578677793 649135701290308934008345)
                ·
                  refine ⟨486851775967731700506259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 649135701290308934008345 486851775967731700506259)
                  ·
                    refine ⟨730277663951597550759389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486851775967731700506259 730277663951597550759389)
                    ·
                      refine ⟨273854123981849081534771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 730277663951597550759389 273854123981849081534771)
                      ·
                        rfl

theorem cell23_533329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_533329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533329 prefixEnd_533329 := by exact prefixLift 533329
  have htrace : WordTrace (prefixWord ++ tailWord_533329) baseStart_533329 baseEnd_533329 := by
    simpa [prefixWord, tailWord_533329, baseEnd_533329] using wordTrace_append hprefix tailTrace_533329
  have hstable : (prefixWord ++ tailWord_533329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533329).length < 2 ^ (prefixWord ++ tailWord_533329).sum := by decide
  have hdescent : baseEnd_533329 < baseStart_533329 := by decide
  rcases family_descends (prefixWord ++ tailWord_533329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533346 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_533346 : Nat := 118140960795 + 533346 * 2 ^ 59
def prefixEnd_533346 : Nat := 4983230072969 + 3 ^ 40 * 533346 * 2
def baseEnd_533346 : Nat := 273862853152975515022193

theorem tailTrace_533346 : CollatzResearch.WordTrace tailWord_533346 prefixEnd_533346 273862853152975515022193 := by
  unfold tailWord_533346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4863181681446501272500973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12968484483857336726669261 4863181681446501272500973)
  ·
    refine ⟨1823693130542437977187865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4863181681446501272500973 1823693130542437977187865)
    ·
      refine ⟨1367769847906828482890899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1823693130542437977187865 1367769847906828482890899)
      ·
        refine ⟨2051654771860242724336349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1367769847906828482890899 2051654771860242724336349)
        ·
          refine ⟨769370539447591021626131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2051654771860242724336349 769370539447591021626131)
          ·
            refine ⟨1154055809171386532439197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769370539447591021626131 1154055809171386532439197)
            ·
              refine ⟨432770928439269949664699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1154055809171386532439197 432770928439269949664699)
              ·
                refine ⟨649156392658904924497049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432770928439269949664699 649156392658904924497049)
                ·
                  refine ⟨486867294494178693372787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 649156392658904924497049 486867294494178693372787)
                  ·
                    refine ⟨730300941741268040059181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486867294494178693372787 730300941741268040059181)
                    ·
                      refine ⟨273862853152975515022193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 730300941741268040059181 273862853152975515022193)
                      ·
                        rfl

theorem cell23_533346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_533346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533346 prefixEnd_533346 := by exact prefixLift 533346
  have htrace : WordTrace (prefixWord ++ tailWord_533346) baseStart_533346 baseEnd_533346 := by
    simpa [prefixWord, tailWord_533346, baseEnd_533346] using wordTrace_append hprefix tailTrace_533346
  have hstable : (prefixWord ++ tailWord_533346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533346).length < 2 ^ (prefixWord ++ tailWord_533346).sum := by decide
  have hdescent : baseEnd_533346 < baseStart_533346 := by decide
  rcases family_descends (prefixWord ++ tailWord_533346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533352 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_533352 : Nat := 118140960795 + 533352 * 2 ^ 59
def prefixEnd_533352 : Nat := 4983230072969 + 3 ^ 40 * 533352 * 2
def baseEnd_533352 : Nat := 273865934036902491547165

theorem tailTrace_533352 : CollatzResearch.WordTrace tailWord_533352 prefixEnd_533352 273865934036902491547165 := by
  unfold tailWord_533352
  simp only [CollatzResearch.WordTrace]
  refine ⟨9726472781882134057361155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12968630375842845409814873 9726472781882134057361155)
  ·
    refine ⟨14589709172823201086041733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9726472781882134057361155 14589709172823201086041733)
    ·
      refine ⟨2735570469904350203632825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14589709172823201086041733 2735570469904350203632825)
      ·
        refine ⟨2051677852428262652724619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2735570469904350203632825 2051677852428262652724619)
        ·
          refine ⟨3077516778642393979086929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2051677852428262652724619 3077516778642393979086929)
          ·
            refine ⟨2308137583981795484315197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3077516778642393979086929 2308137583981795484315197)
            ·
              refine ⟨865551593993173306618199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2308137583981795484315197 865551593993173306618199)
              ·
                refine ⟨1298327390989759959927299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865551593993173306618199 1298327390989759959927299)
                ·
                  refine ⟨1947491086484639939890949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298327390989759959927299 1947491086484639939890949)
                  ·
                    refine ⟨365154578715869988729553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1947491086484639939890949 365154578715869988729553)
                    ·
                      refine ⟨273865934036902491547165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365154578715869988729553 273865934036902491547165)
                      ·
                        rfl

theorem cell23_533352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_533352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533352 prefixEnd_533352 := by exact prefixLift 533352
  have htrace : WordTrace (prefixWord ++ tailWord_533352) baseStart_533352 baseEnd_533352 := by
    simpa [prefixWord, tailWord_533352, baseEnd_533352] using wordTrace_append hprefix tailTrace_533352
  have hstable : (prefixWord ++ tailWord_533352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533352).length < 2 ^ (prefixWord ++ tailWord_533352).sum := by decide
  have hdescent : baseEnd_533352 < baseStart_533352 := by decide
  rcases family_descends (prefixWord ++ tailWord_533352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533368 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 4, 3, 3]
def baseStart_533368 : Nat := 118140960795 + 533368 * 2 ^ 59
def prefixEnd_533368 : Nat := 4983230072969 + 3 ^ 40 * 533368 * 2
def baseEnd_533368 : Nat := 273874149727374428947091

theorem tailTrace_533368 : CollatzResearch.WordTrace tailWord_533368 prefixEnd_533368 273874149727374428947091 := by
  unfold tailWord_533368
  simp only [CollatzResearch.WordTrace]
  refine ⟨9726764565853151423652379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12969019421137535231536505 9726764565853151423652379)
  ·
    refine ⟨14590146848779727135478569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9726764565853151423652379 14590146848779727135478569)
    ·
      refine ⟨10942610136584795351608927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14590146848779727135478569 10942610136584795351608927)
      ·
        refine ⟨16413915204877193027413391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10942610136584795351608927 16413915204877193027413391)
        ·
          refine ⟨24620872807315789541120087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16413915204877193027413391 24620872807315789541120087)
          ·
            refine ⟨36931309210973684311680131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24620872807315789541120087 36931309210973684311680131)
            ·
              refine ⟨55396963816460526467520197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36931309210973684311680131 55396963816460526467520197)
              ·
                refine ⟨10386930715586348712660037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55396963816460526467520197 10386930715586348712660037)
                ·
                  refine ⟨1947549509172440383623757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10386930715586348712660037 1947549509172440383623757)
                  ·
                    refine ⟨730331065939665143858909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1947549509172440383623757 730331065939665143858909)
                    ·
                      refine ⟨273874149727374428947091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 730331065939665143858909 273874149727374428947091)
                      ·
                        rfl

theorem cell23_533368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_533368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533368 prefixEnd_533368 := by exact prefixLift 533368
  have htrace : WordTrace (prefixWord ++ tailWord_533368) baseStart_533368 baseEnd_533368 := by
    simpa [prefixWord, tailWord_533368, baseEnd_533368] using wordTrace_append hprefix tailTrace_533368
  have hstable : (prefixWord ++ tailWord_533368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533368).length < 2 ^ (prefixWord ++ tailWord_533368).sum := by decide
  have hdescent : baseEnd_533368 < baseStart_533368 := by decide
  rcases family_descends (prefixWord ++ tailWord_533368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533375 : List Nat := [1, 1, 2, 2, 1, 1, 7, 3, 5]
def baseStart_533375 : Nat := 118140960795 + 533375 * 2 ^ 59
def prefixEnd_533375 : Nat := 4983230072969 + 3 ^ 40 * 533375 * 2
def baseEnd_533375 : Nat := 30430860454661766839951

theorem tailTrace_533375 : CollatzResearch.WordTrace tailWord_533375 prefixEnd_533375 30430860454661766839951 := by
  unfold tailWord_533375
  simp only [CollatzResearch.WordTrace]
  refine ⟨19453784442680943042809579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12969189628453962028539719 19453784442680943042809579)
  ·
    refine ⟨29180676664021414564214369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19453784442680943042809579 29180676664021414564214369)
    ·
      refine ⟨21885507498016060923160777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29180676664021414564214369 21885507498016060923160777)
      ·
        refine ⟨16414130623512045692370583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21885507498016060923160777 16414130623512045692370583)
        ·
          refine ⟨24621195935268068538555875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16414130623512045692370583 24621195935268068538555875)
          ·
            refine ⟨36931793902902102807833813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24621195935268068538555875 36931793902902102807833813)
            ·
              refine ⟨865588919599268034558605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36931793902902102807833813 865588919599268034558605)
              ·
                refine ⟨324595844849725512959477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 865588919599268034558605 324595844849725512959477)
                ·
                  refine ⟨30430860454661766839951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324595844849725512959477 30430860454661766839951)
                  ·
                    rfl

theorem cell23_533375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 5].length) (baseStart_533375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533375 prefixEnd_533375 := by exact prefixLift 533375
  have htrace : WordTrace (prefixWord ++ tailWord_533375) baseStart_533375 baseEnd_533375 := by
    simpa [prefixWord, tailWord_533375, baseEnd_533375] using wordTrace_append hprefix tailTrace_533375
  have hstable : (prefixWord ++ tailWord_533375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533375).length < 2 ^ (prefixWord ++ tailWord_533375).sum := by decide
  have hdescent : baseEnd_533375 < baseStart_533375 := by decide
  rcases family_descends (prefixWord ++ tailWord_533375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533388 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_533388 : Nat := 118140960795 + 533388 * 2 ^ 59
def prefixEnd_533388 : Nat := 4983230072969 + 3 ^ 40 * 533388 * 2
def baseEnd_533388 : Nat := 91294806446821450232333

theorem tailTrace_533388 : CollatzResearch.WordTrace tailWord_533388 prefixEnd_533388 91294806446821450232333 := by
  unfold tailWord_533388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9727129295816923131516409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12969505727755897508688545 9727129295816923131516409)
  ·
    refine ⟨7295346971862692348637307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9727129295816923131516409 7295346971862692348637307)
    ·
      refine ⟨10943020457794038522955961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7295346971862692348637307 10943020457794038522955961)
      ·
        refine ⟨8207265343345528892216971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10943020457794038522955961 8207265343345528892216971)
        ·
          refine ⟨12310898015018293338325457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8207265343345528892216971 12310898015018293338325457)
          ·
            refine ⟨9233173511263720003744093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12310898015018293338325457 9233173511263720003744093)
            ·
              refine ⟨3462440066723895001404035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9233173511263720003744093 3462440066723895001404035)
              ·
                refine ⟨5193660100085842502106053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462440066723895001404035 5193660100085842502106053)
                ·
                  refine ⟨973811268766095469144885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5193660100085842502106053 973811268766095469144885)
                  ·
                    refine ⟨91294806446821450232333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 973811268766095469144885 91294806446821450232333)
                    ·
                      rfl

theorem cell23_533388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_533388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533388 prefixEnd_533388 := by exact prefixLift 533388
  have htrace : WordTrace (prefixWord ++ tailWord_533388) baseStart_533388 baseEnd_533388 := by
    simpa [prefixWord, tailWord_533388, baseEnd_533388] using wordTrace_append hprefix tailTrace_533388
  have hstable : (prefixWord ++ tailWord_533388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533388).length < 2 ^ (prefixWord ++ tailWord_533388).sum := by decide
  have hdescent : baseEnd_533388 < baseStart_533388 := by decide
  rcases family_descends (prefixWord ++ tailWord_533388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533408 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_533408 : Nat := 118140960795 + 533408 * 2 ^ 59
def prefixEnd_533408 : Nat := 4983230072969 + 3 ^ 40 * 533408 * 2
def baseEnd_533408 : Nat := 273894688953554272446907

theorem tailTrace_533408 : CollatzResearch.WordTrace tailWord_533408 prefixEnd_533408 273894688953554272446907 := by
  unfold tailWord_533408
  simp only [CollatzResearch.WordTrace]
  refine ⟨9727494025780694839380439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12969992034374259785840585 9727494025780694839380439)
  ·
    refine ⟨14591241038671042259070659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9727494025780694839380439 14591241038671042259070659)
    ·
      refine ⟨21886861558006563388605989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14591241038671042259070659 21886861558006563388605989)
      ·
        refine ⟨4103786542126230635363623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21886861558006563388605989 4103786542126230635363623)
        ·
          refine ⟨6155679813189345953045435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4103786542126230635363623 6155679813189345953045435)
          ·
            refine ⟨9233519719784018929568153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6155679813189345953045435 9233519719784018929568153)
            ·
              refine ⟨6925139789838014197176115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9233519719784018929568153 6925139789838014197176115)
              ·
                refine ⟨10387709684757021295764173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6925139789838014197176115 10387709684757021295764173)
                ·
                  refine ⟨3895391131783882985911565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10387709684757021295764173 3895391131783882985911565)
                  ·
                    refine ⟨1460771674418956119716837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3895391131783882985911565 1460771674418956119716837)
                    ·
                      refine ⟨273894688953554272446907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1460771674418956119716837 273894688953554272446907)
                      ·
                        rfl

theorem cell23_533408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_533408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533408 prefixEnd_533408 := by exact prefixLift 533408
  have htrace : WordTrace (prefixWord ++ tailWord_533408) baseStart_533408 baseEnd_533408 := by
    simpa [prefixWord, tailWord_533408, baseEnd_533408] using wordTrace_append hprefix tailTrace_533408
  have hstable : (prefixWord ++ tailWord_533408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533408).length < 2 ^ (prefixWord ++ tailWord_533408).sum := by decide
  have hdescent : baseEnd_533408 < baseStart_533408 := by decide
  rcases family_descends (prefixWord ++ tailWord_533408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533465 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 6]
def baseStart_533465 : Nat := 118140960795 + 533465 * 2 ^ 59
def prefixEnd_533465 : Nat := 4983230072969 + 3 ^ 40 * 533465 * 2
def baseEnd_533465 : Nat := 30435995261206727714905

theorem tailTrace_533465 : CollatzResearch.WordTrace tailWord_533465 prefixEnd_533465 30435995261206727714905 := by
  unfold tailWord_533465
  simp only [CollatzResearch.WordTrace]
  refine ⟨19457067012354888413585849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12971378008236592275723899 19457067012354888413585849)
  ·
    refine ⟨14592800259266166310189387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19457067012354888413585849 14592800259266166310189387)
    ·
      refine ⟨21889200388899249465284081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14592800259266166310189387 21889200388899249465284081)
      ·
        refine ⟨16416900291674437098963061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21889200388899249465284081 16416900291674437098963061)
        ·
          refine ⟨1539084402344478478027787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16416900291674437098963061 1539084402344478478027787)
          ·
            refine ⟨2308626603516717717041681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539084402344478478027787 2308626603516717717041681)
            ·
              refine ⟨1731469952637538287781261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2308626603516717717041681 1731469952637538287781261)
              ·
                refine ⟨649301232239076857917973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1731469952637538287781261 649301232239076857917973)
                ·
                  refine ⟨30435995261206727714905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 649301232239076857917973 30435995261206727714905)
                  ·
                    rfl

theorem cell23_533465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 6].length) (baseStart_533465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533465 prefixEnd_533465 := by exact prefixLift 533465
  have htrace : WordTrace (prefixWord ++ tailWord_533465) baseStart_533465 baseEnd_533465 := by
    simpa [prefixWord, tailWord_533465, baseEnd_533465] using wordTrace_append hprefix tailTrace_533465
  have hstable : (prefixWord ++ tailWord_533465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533465).length < 2 ^ (prefixWord ++ tailWord_533465).sum := by decide
  have hdescent : baseEnd_533465 < baseStart_533465 := by decide
  rcases family_descends (prefixWord ++ tailWord_533465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533479 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_533479 : Nat := 118140960795 + 533479 * 2 ^ 59
def prefixEnd_533479 : Nat := 4983230072969 + 3 ^ 40 * 533479 * 2
def baseEnd_533479 : Nat := 273931146080023494659081

theorem tailTrace_533479 : CollatzResearch.WordTrace tailWord_533479 prefixEnd_533479 273931146080023494659081 := by
  unfold tailWord_533479
  simp only [CollatzResearch.WordTrace]
  refine ⟨19457577634304168804595491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12971718422869445869730327 19457577634304168804595491)
  ·
    refine ⟨29186366451456253206893237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19457577634304168804595491 29186366451456253206893237)
    ·
      refine ⟨2736221854824023738146241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29186366451456253206893237 2736221854824023738146241)
      ·
        refine ⟨2052166391118017803609681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2736221854824023738146241 2052166391118017803609681)
        ·
          refine ⟨1539124793338513352707261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2052166391118017803609681 1539124793338513352707261)
          ·
            refine ⟨577171797501942507265223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1539124793338513352707261 577171797501942507265223)
            ·
              refine ⟨865757696252913760897835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577171797501942507265223 865757696252913760897835)
              ·
                refine ⟨1298636544379370641346753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865757696252913760897835 1298636544379370641346753)
                ·
                  refine ⟨973977408284527981010065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1298636544379370641346753 973977408284527981010065)
                  ·
                    refine ⟨730483056213395985757549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 973977408284527981010065 730483056213395985757549)
                    ·
                      refine ⟨273931146080023494659081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 730483056213395985757549 273931146080023494659081)
                      ·
                        rfl

theorem cell23_533479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_533479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533479 prefixEnd_533479 := by exact prefixLift 533479
  have htrace : WordTrace (prefixWord ++ tailWord_533479) baseStart_533479 baseEnd_533479 := by
    simpa [prefixWord, tailWord_533479, baseEnd_533479] using wordTrace_append hprefix tailTrace_533479
  have hstable : (prefixWord ++ tailWord_533479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533479).length < 2 ^ (prefixWord ++ tailWord_533479).sum := by decide
  have hdescent : baseEnd_533479 < baseStart_533479 := by decide
  rcases family_descends (prefixWord ++ tailWord_533479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533486 : List Nat := [4, 1, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_533486 : Nat := 118140960795 + 533486 * 2 ^ 59
def prefixEnd_533486 : Nat := 4983230072969 + 3 ^ 40 * 533486 * 2
def baseEnd_533486 : Nat := 91311580148201655757183

theorem tailTrace_533486 : CollatzResearch.WordTrace tailWord_533486 prefixEnd_533486 91311580148201655757183 := by
  unfold tailWord_533486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2432229118159851125012539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12971888630185872666733541 2432229118159851125012539)
  ·
    refine ⟨3648343677239776687518809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2432229118159851125012539 3648343677239776687518809)
    ·
      refine ⟨2736257757929832515639107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3648343677239776687518809 2736257757929832515639107)
      ·
        refine ⟨4104386636894748773458661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2736257757929832515639107 4104386636894748773458661)
        ·
          refine ⟨769572494417765395023499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4104386636894748773458661 769572494417765395023499)
          ·
            refine ⟨1154358741626648092535249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769572494417765395023499 1154358741626648092535249)
            ·
              refine ⟨865769056219986069401437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1154358741626648092535249 865769056219986069401437)
              ·
                refine ⟨324663396082494776025539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 865769056219986069401437 324663396082494776025539)
                ·
                  refine ⟨486995094123742164038309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324663396082494776025539 486995094123742164038309)
                  ·
                    refine ⟨91311580148201655757183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 486995094123742164038309 91311580148201655757183)
                    ·
                      rfl

theorem cell23_533486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_533486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533486 prefixEnd_533486 := by exact prefixLift 533486
  have htrace : WordTrace (prefixWord ++ tailWord_533486) baseStart_533486 baseEnd_533486 := by
    simpa [prefixWord, tailWord_533486, baseEnd_533486] using wordTrace_append hprefix tailTrace_533486
  have hstable : (prefixWord ++ tailWord_533486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533486).length < 2 ^ (prefixWord ++ tailWord_533486).sum := by decide
  have hdescent : baseEnd_533486 < baseStart_533486 := by decide
  rcases family_descends (prefixWord ++ tailWord_533486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533488 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_533488 : Nat := 118140960795 + 533488 * 2 ^ 59
def prefixEnd_533488 : Nat := 4983230072969 + 3 ^ 40 * 533488 * 2
def baseEnd_533488 : Nat := 273935767405913959446539

theorem tailTrace_533488 : CollatzResearch.WordTrace tailWord_533488 prefixEnd_533488 273935767405913959446539 := by
  unfold tailWord_533488
  simp only [CollatzResearch.WordTrace]
  refine ⟨9728952945635781670836559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12971937260847708894448745 9728952945635781670836559)
  ·
    refine ⟨14593429418453672506254839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9728952945635781670836559 14593429418453672506254839)
    ·
      refine ⟨21890144127680508759382259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14593429418453672506254839 21890144127680508759382259)
      ·
        refine ⟨32835216191520763139073389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21890144127680508759382259 32835216191520763139073389)
        ·
          refine ⟨12313206071820286177152521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32835216191520763139073389 12313206071820286177152521)
          ·
            refine ⟨9234904553865214632864391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12313206071820286177152521 9234904553865214632864391)
            ·
              refine ⟨13852356830797821949296587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9234904553865214632864391 13852356830797821949296587)
              ·
                refine ⟨20778535246196732923944881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13852356830797821949296587 20778535246196732923944881)
                ·
                  refine ⟨15583901434647549692958661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20778535246196732923944881 15583901434647549692958661)
                  ·
                    refine ⟨2921981518996415567429749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15583901434647549692958661 2921981518996415567429749)
                    ·
                      refine ⟨273935767405913959446539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2921981518996415567429749 273935767405913959446539)
                      ·
                        rfl

theorem cell23_533488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_533488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533488 prefixEnd_533488 := by exact prefixLift 533488
  have htrace : WordTrace (prefixWord ++ tailWord_533488) baseStart_533488 baseEnd_533488 := by
    simpa [prefixWord, tailWord_533488, baseEnd_533488] using wordTrace_append hprefix tailTrace_533488
  have hstable : (prefixWord ++ tailWord_533488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533488).length < 2 ^ (prefixWord ++ tailWord_533488).sum := by decide
  have hdescent : baseEnd_533488 < baseStart_533488 := by decide
  rcases family_descends (prefixWord ++ tailWord_533488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533509 : List Nat := [1, 3, 1, 1, 2, 3, 1, 6, 1, 1, 3]
def baseStart_533509 : Nat := 118140960795 + 533509 * 2 ^ 59
def prefixEnd_533509 : Nat := 4983230072969 + 3 ^ 40 * 533509 * 2
def baseEnd_533509 : Nat := 273946550499658377283943

theorem tailTrace_533509 : CollatzResearch.WordTrace tailWord_533509 prefixEnd_533509 273946550499658377283943 := by
  unfold tailWord_533509
  simp only [CollatzResearch.WordTrace]
  refine ⟨19458671824195483928187581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12972447882796989285458387 19458671824195483928187581)
  ·
    refine ⟨7297001934073306473070343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19458671824195483928187581 7297001934073306473070343)
    ·
      refine ⟨10945502901109959709605515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7297001934073306473070343 10945502901109959709605515)
      ·
        refine ⟨16418254351664939564408273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10945502901109959709605515 16418254351664939564408273)
        ·
          refine ⟨12313690763748704673306205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16418254351664939564408273 12313690763748704673306205)
          ·
            refine ⟨4617634036405764252489827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12313690763748704673306205 4617634036405764252489827)
            ·
              refine ⟨6926451054608646378734741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4617634036405764252489827 6926451054608646378734741)
              ·
                refine ⟨324677393184780299003191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6926451054608646378734741 324677393184780299003191)
                ·
                  refine ⟨487016089777170448504787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324677393184780299003191 487016089777170448504787)
                  ·
                    refine ⟨730524134665755672757181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 487016089777170448504787 730524134665755672757181)
                    ·
                      refine ⟨273946550499658377283943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 730524134665755672757181 273946550499658377283943)
                      ·
                        rfl

theorem cell23_533509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 1, 1, 3].length) (baseStart_533509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533509 prefixEnd_533509 := by exact prefixLift 533509
  have htrace : WordTrace (prefixWord ++ tailWord_533509) baseStart_533509 baseEnd_533509 := by
    simpa [prefixWord, tailWord_533509, baseEnd_533509] using wordTrace_append hprefix tailTrace_533509
  have hstable : (prefixWord ++ tailWord_533509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533509).length < 2 ^ (prefixWord ++ tailWord_533509).sum := by decide
  have hdescent : baseEnd_533509 < baseStart_533509 := by decide
  rcases family_descends (prefixWord ++ tailWord_533509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533543 : List Nat := [1, 1, 7, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_533543 : Nat := 118140960795 + 533543 * 2 ^ 59
def prefixEnd_533543 : Nat := 4983230072969 + 3 ^ 40 * 533543 * 2
def baseEnd_533543 : Nat := 273964008841911244258787

theorem tailTrace_533543 : CollatzResearch.WordTrace tailWord_533543 prefixEnd_533543 273964008841911244258787 := by
  unfold tailWord_533543
  simp only [CollatzResearch.WordTrace]
  refine ⟨19459911906072307734925283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12973274604048205156616855 19459911906072307734925283)
  ·
    refine ⟨29189867859108461602387925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19459911906072307734925283 29189867859108461602387925)
    ·
      refine ⟨684137527947854568805967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 29189867859108461602387925 684137527947854568805967)
      ·
        refine ⟨1026206291921781853208951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684137527947854568805967 1026206291921781853208951)
        ·
          refine ⟨1539309437882672779813427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026206291921781853208951 1539309437882672779813427)
          ·
            refine ⟨2308964156824009169720141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539309437882672779813427 2308964156824009169720141)
            ·
              refine ⟨865861558809003438645053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2308964156824009169720141 865861558809003438645053)
              ·
                refine ⟨324698084553376289491895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 865861558809003438645053 324698084553376289491895)
                ·
                  refine ⟨487047126830064434237843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324698084553376289491895 487047126830064434237843)
                  ·
                    refine ⟨730570690245096651356765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 487047126830064434237843 730570690245096651356765)
                    ·
                      refine ⟨273964008841911244258787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 730570690245096651356765 273964008841911244258787)
                      ·
                        rfl

theorem cell23_533543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_533543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533543 prefixEnd_533543 := by exact prefixLift 533543
  have htrace : WordTrace (prefixWord ++ tailWord_533543) baseStart_533543 baseEnd_533543 := by
    simpa [prefixWord, tailWord_533543, baseEnd_533543] using wordTrace_append hprefix tailTrace_533543
  have hstable : (prefixWord ++ tailWord_533543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533543).length < 2 ^ (prefixWord ++ tailWord_533543).sum := by decide
  have hdescent : baseEnd_533543 < baseStart_533543 := by decide
  rcases family_descends (prefixWord ++ tailWord_533543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533552 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 3]
def baseStart_533552 : Nat := 118140960795 + 533552 * 2 ^ 59
def prefixEnd_533552 : Nat := 4983230072969 + 3 ^ 40 * 533552 * 2
def baseEnd_533552 : Nat := 273968630167801709046245

theorem tailTrace_533552 : CollatzResearch.WordTrace tailWord_533552 prefixEnd_533552 273968630167801709046245 := by
  unfold tailWord_533552
  simp only [CollatzResearch.WordTrace]
  refine ⟨9730120081519851136001455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12973493442026468181335273 9730120081519851136001455)
  ·
    refine ⟨14595180122279776704002183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9730120081519851136001455 14595180122279776704002183)
    ·
      refine ⟨21892770183419665056003275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14595180122279776704002183 21892770183419665056003275)
      ·
        refine ⟨32839155275129497584004913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21892770183419665056003275 32839155275129497584004913)
        ·
          refine ⟨24629366456347123188003685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32839155275129497584004913 24629366456347123188003685)
          ·
            refine ⟨4618006210565085597750691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24629366456347123188003685 4618006210565085597750691)
            ·
              refine ⟨6927009315847628396626037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618006210565085597750691 6927009315847628396626037)
              ·
                refine ⟨649407123360715162183691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6927009315847628396626037 649407123360715162183691)
                ·
                  refine ⟨974110685041072743275537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649407123360715162183691 974110685041072743275537)
                  ·
                    refine ⟨730583013780804557456653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 974110685041072743275537 730583013780804557456653)
                    ·
                      refine ⟨273968630167801709046245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 730583013780804557456653 273968630167801709046245)
                      ·
                        rfl

theorem cell23_533552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 3].length) (baseStart_533552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533552 prefixEnd_533552 := by exact prefixLift 533552
  have htrace : WordTrace (prefixWord ++ tailWord_533552) baseStart_533552 baseEnd_533552 := by
    simpa [prefixWord, tailWord_533552, baseEnd_533552] using wordTrace_append hprefix tailTrace_533552
  have hstable : (prefixWord ++ tailWord_533552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533552).length < 2 ^ (prefixWord ++ tailWord_533552).sum := by decide
  have hdescent : baseEnd_533552 < baseStart_533552 := by decide
  rcases family_descends (prefixWord ++ tailWord_533552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533582 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_533582 : Nat := 118140960795 + 533582 * 2 ^ 59
def prefixEnd_533582 : Nat := 4983230072969 + 3 ^ 40 * 533582 * 2
def baseEnd_533582 : Nat := 273984034587436591671107

theorem tailTrace_533582 : CollatzResearch.WordTrace tailWord_533582 prefixEnd_533582 273984034587436591671107 := by
  unfold tailWord_533582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2432666794116377174449375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12974222901954011597063333 2432666794116377174449375)
  ·
    refine ⟨3649000191174565761674063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2432666794116377174449375 3649000191174565761674063)
    ·
      refine ⟨5473500286761848642511095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3649000191174565761674063 5473500286761848642511095)
      ·
        refine ⟨8210250430142772963766643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5473500286761848642511095 8210250430142772963766643)
        ·
          refine ⟨12315375645214159445649965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8210250430142772963766643 12315375645214159445649965)
          ·
            refine ⟨4618265866955309792118737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12315375645214159445649965 4618265866955309792118737)
            ·
              refine ⟨3463699400216482344089053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4618265866955309792118737 3463699400216482344089053)
              ·
                refine ⟨1298887275081180879033395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3463699400216482344089053 1298887275081180879033395)
                ·
                  refine ⟨1948330912621771318550093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298887275081180879033395 1948330912621771318550093)
                  ·
                    refine ⟨730624092233164244456285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1948330912621771318550093 730624092233164244456285)
                    ·
                      refine ⟨273984034587436591671107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 730624092233164244456285 273984034587436591671107)
                      ·
                        rfl

theorem cell23_533582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_533582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533582 prefixEnd_533582 := by exact prefixLift 533582
  have htrace : WordTrace (prefixWord ++ tailWord_533582) baseStart_533582 baseEnd_533582 := by
    simpa [prefixWord, tailWord_533582, baseEnd_533582] using wordTrace_append hprefix tailTrace_533582
  have hstable : (prefixWord ++ tailWord_533582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533582).length < 2 ^ (prefixWord ++ tailWord_533582).sum := by decide
  have hdescent : baseEnd_533582 < baseStart_533582 := by decide
  rcases family_descends (prefixWord ++ tailWord_533582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533586 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_533586 : Nat := 118140960795 + 533586 * 2 ^ 59
def prefixEnd_533586 : Nat := 4983230072969 + 3 ^ 40 * 533586 * 2
def baseEnd_533586 : Nat := 273986088510054576021089

theorem tailTrace_533586 : CollatzResearch.WordTrace tailWord_533586 prefixEnd_533586 273986088510054576021089 := by
  unfold tailWord_533586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4865370061229131519685153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12974320163277684052493741 4865370061229131519685153)
  ·
    refine ⟨3649027545921848639763865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4865370061229131519685153 3649027545921848639763865)
    ·
      refine ⟨2736770659441386479822899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3649027545921848639763865 2736770659441386479822899)
      ·
        refine ⟨4105155989162079719734349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2736770659441386479822899 4105155989162079719734349)
        ·
          refine ⟨1539433495935779894900381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4105155989162079719734349 1539433495935779894900381)
          ·
            refine ⟨577287560975917460587643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1539433495935779894900381 577287560975917460587643)
            ·
              refine ⟨865931341463876190881465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577287560975917460587643 865931341463876190881465)
              ·
                refine ⟨649448506097907143161099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865931341463876190881465 649448506097907143161099)
                ·
                  refine ⟨974172759146860714741649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649448506097907143161099 974172759146860714741649)
                  ·
                    refine ⟨730629569360145536056237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 974172759146860714741649 730629569360145536056237)
                    ·
                      refine ⟨273986088510054576021089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 730629569360145536056237 273986088510054576021089)
                      ·
                        rfl

theorem cell23_533586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_533586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533586 prefixEnd_533586 := by exact prefixLift 533586
  have htrace : WordTrace (prefixWord ++ tailWord_533586) baseStart_533586 baseEnd_533586 := by
    simpa [prefixWord, tailWord_533586, baseEnd_533586] using wordTrace_append hprefix tailTrace_533586
  have hstable : (prefixWord ++ tailWord_533586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533586).length < 2 ^ (prefixWord ++ tailWord_533586).sum := by decide
  have hdescent : baseEnd_533586 < baseStart_533586 := by decide
  rcases family_descends (prefixWord ++ tailWord_533586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533615 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 2, 6]
def baseStart_533615 : Nat := 118140960795 + 533615 * 2 ^ 59
def prefixEnd_533615 : Nat := 4983230072969 + 3 ^ 40 * 533615 * 2
def baseEnd_533615 : Nat := 91333659816344987519485

theorem tailTrace_533615 : CollatzResearch.WordTrace tailWord_533615 prefixEnd_533615 91333659816344987519485 := by
  unfold tailWord_533615
  simp only [CollatzResearch.WordTrace]
  refine ⟨19462537961811464031546299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12975025307874309354364199 19462537961811464031546299)
  ·
    refine ⟨29193806942717196047319449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19462537961811464031546299 29193806942717196047319449)
    ·
      refine ⟨21895355207037897035489587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29193806942717196047319449 21895355207037897035489587)
      ·
        refine ⟨32843032810556845553234381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21895355207037897035489587 32843032810556845553234381)
        ·
          refine ⟨12316137303958817082462893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32843032810556845553234381 12316137303958817082462893)
          ·
            refine ⟨4618551488984556405923585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12316137303958817082462893 4618551488984556405923585)
            ·
              refine ⟨3463913616738417304442689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4618551488984556405923585 3463913616738417304442689)
              ·
                refine ⟨2597935212553812978332017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3463913616738417304442689 2597935212553812978332017)
                ·
                  refine ⟨1948451409415359733749013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2597935212553812978332017 1948451409415359733749013)
                  ·
                    refine ⟨91333659816344987519485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1948451409415359733749013 91333659816344987519485)
                    ·
                      rfl

theorem cell23_533615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_533615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533615 prefixEnd_533615 := by exact prefixLift 533615
  have htrace : WordTrace (prefixWord ++ tailWord_533615) baseStart_533615 baseEnd_533615 := by
    simpa [prefixWord, tailWord_533615, baseEnd_533615] using wordTrace_append hprefix tailTrace_533615
  have hstable : (prefixWord ++ tailWord_533615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533615).length < 2 ^ (prefixWord ++ tailWord_533615).sum := by decide
  have hdescent : baseEnd_533615 < baseStart_533615 := by decide
  rcases family_descends (prefixWord ++ tailWord_533615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533622 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_533622 : Nat := 118140960795 + 533622 * 2 ^ 59
def prefixEnd_533622 : Nat := 4983230072969 + 3 ^ 40 * 533622 * 2
def baseEnd_533622 : Nat := 274004573813616435170923

theorem tailTrace_533622 : CollatzResearch.WordTrace tailWord_533622 prefixEnd_533622 274004573813616435170923 := by
  unfold tailWord_533622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216424579549131514190695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12975195515190736151367413 1216424579549131514190695)
  ·
    refine ⟨1824636869323697271286043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1216424579549131514190695 1824636869323697271286043)
    ·
      refine ⟨2736955303985545906929065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1824636869323697271286043 2736955303985545906929065)
      ·
        refine ⟨2052716477989159430196799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2736955303985545906929065 2052716477989159430196799)
        ·
          refine ⟨3079074716983739145295199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2052716477989159430196799 3079074716983739145295199)
          ·
            refine ⟨4618612075475608717942799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3079074716983739145295199 4618612075475608717942799)
            ·
              refine ⟨6927918113213413076914199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618612075475608717942799 6927918113213413076914199)
              ·
                refine ⟨10391877169820119615371299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6927918113213413076914199 10391877169820119615371299)
                ·
                  refine ⟨15587815754730179423056949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10391877169820119615371299 15587815754730179423056949)
                  ·
                    refine ⟨1461357727005954320911589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15587815754730179423056949 1461357727005954320911589)
                    ·
                      refine ⟨274004573813616435170923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1461357727005954320911589 274004573813616435170923)
                      ·
                        rfl

theorem cell23_533622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_533622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533622 prefixEnd_533622 := by exact prefixLift 533622
  have htrace : WordTrace (prefixWord ++ tailWord_533622) baseStart_533622 baseEnd_533622 := by
    simpa [prefixWord, tailWord_533622, baseEnd_533622] using wordTrace_append hprefix tailTrace_533622
  have hstable : (prefixWord ++ tailWord_533622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533622).length < 2 ^ (prefixWord ++ tailWord_533622).sum := by decide
  have hdescent : baseEnd_533622 < baseStart_533622 := by decide
  rcases family_descends (prefixWord ++ tailWord_533622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533639 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 6, 2, 2]
def baseStart_533639 : Nat := 118140960795 + 533639 * 2 ^ 59
def prefixEnd_533639 : Nat := 4983230072969 + 3 ^ 40 * 533639 * 2
def baseEnd_533639 : Nat := 274013302984742868658345

theorem tailTrace_533639 : CollatzResearch.WordTrace tailWord_533639 prefixEnd_533639 274013302984742868658345 := by
  unfold tailWord_533639
  simp only [CollatzResearch.WordTrace]
  refine ⟨19463413313724516130419971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12975608875816344086946647 19463413313724516130419971)
  ·
    refine ⟨29195119970586774195629957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19463413313724516130419971 29195119970586774195629957)
    ·
      refine ⟨5474084994485020161680617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29195119970586774195629957 5474084994485020161680617)
      ·
        refine ⟨4105563745863765121260463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5474084994485020161680617 4105563745863765121260463)
        ·
          refine ⟨6158345618795647681890695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4105563745863765121260463 6158345618795647681890695)
          ·
            refine ⟨9237518428193471522836043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6158345618795647681890695 9237518428193471522836043)
            ·
              refine ⟨13856277642290207284254065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9237518428193471522836043 13856277642290207284254065)
              ·
                refine ⟨10392208231717655463190549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13856277642290207284254065 10392208231717655463190549)
                ·
                  refine ⟨487134760861765099837057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10392208231717655463190549 487134760861765099837057)
                  ·
                    refine ⟨365351070646323824877793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 487134760861765099837057 365351070646323824877793)
                    ·
                      refine ⟨274013302984742868658345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365351070646323824877793 274013302984742868658345)
                      ·
                        rfl

theorem cell23_533639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_533639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533639 prefixEnd_533639 := by exact prefixLift 533639
  have htrace : WordTrace (prefixWord ++ tailWord_533639) baseStart_533639 baseEnd_533639 := by
    simpa [prefixWord, tailWord_533639, baseEnd_533639] using wordTrace_append hprefix tailTrace_533639
  have hstable : (prefixWord ++ tailWord_533639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533639).length < 2 ^ (prefixWord ++ tailWord_533639).sum := by decide
  have hdescent : baseEnd_533639 < baseStart_533639 := by decide
  rcases family_descends (prefixWord ++ tailWord_533639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533642 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_533642 : Nat := 118140960795 + 533642 * 2 ^ 59
def prefixEnd_533642 : Nat := 4983230072969 + 3 ^ 40 * 533642 * 2
def baseEnd_533642 : Nat := 274014843426706356920831

theorem tailTrace_533642 : CollatzResearch.WordTrace tailWord_533642 prefixEnd_533642 274014843426706356920831 := by
  unfold tailWord_533642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4865880683178411910694795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12975681821809098428519453 4865880683178411910694795)
  ·
    refine ⟨7298821024767617866042193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4865880683178411910694795 7298821024767617866042193)
    ·
      refine ⟨5474115768575713399531645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7298821024767617866042193 5474115768575713399531645)
      ·
        refine ⟨2052793413215892524824367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5474115768575713399531645 2052793413215892524824367)
        ·
          refine ⟨3079190119823838787236551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2052793413215892524824367 3079190119823838787236551)
          ·
            refine ⟨4618785179735758180854827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3079190119823838787236551 4618785179735758180854827)
            ·
              refine ⟨6928177769603637271282241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618785179735758180854827 6928177769603637271282241)
              ·
                refine ⟨5196133327202727953461681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6928177769603637271282241 5196133327202727953461681)
                ·
                  refine ⟨3897099995402045965096261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5196133327202727953461681 3897099995402045965096261)
                  ·
                    refine ⟨730706249137883618455549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3897099995402045965096261 730706249137883618455549)
                    ·
                      refine ⟨274014843426706356920831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 730706249137883618455549 274014843426706356920831)
                      ·
                        rfl

theorem cell23_533642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_533642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533642 prefixEnd_533642 := by exact prefixLift 533642
  have htrace : WordTrace (prefixWord ++ tailWord_533642) baseStart_533642 baseEnd_533642 := by
    simpa [prefixWord, tailWord_533642, baseEnd_533642] using wordTrace_append hprefix tailTrace_533642
  have hstable : (prefixWord ++ tailWord_533642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533642).length < 2 ^ (prefixWord ++ tailWord_533642).sum := by decide
  have hdescent : baseEnd_533642 < baseStart_533642 := by decide
  rcases family_descends (prefixWord ++ tailWord_533642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533692 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_533692 : Nat := 118140960795 + 533692 * 2 ^ 59
def prefixEnd_533692 : Nat := 4983230072969 + 3 ^ 40 * 533692 * 2
def baseEnd_533692 : Nat := 91346839153143720431867

theorem tailTrace_533692 : CollatzResearch.WordTrace tailWord_533692 prefixEnd_533692 91346839153143720431867 := by
  unfold tailWord_533692
  simp only [CollatzResearch.WordTrace]
  refine ⟨9732673191266253091049665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12976897588355004121399553 9732673191266253091049665)
  ·
    refine ⟨7299504893449689818287249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9732673191266253091049665 7299504893449689818287249)
    ·
      refine ⟨5474628670087267363715437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7299504893449689818287249 5474628670087267363715437)
      ·
        refine ⟨2052985751282725261393289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5474628670087267363715437 2052985751282725261393289)
        ·
          refine ⟨1539739313462043946044967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2052985751282725261393289 1539739313462043946044967)
          ·
            refine ⟨2309608970193065919067451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539739313462043946044967 2309608970193065919067451)
            ·
              refine ⟨3464413455289598878601177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309608970193065919067451 3464413455289598878601177)
              ·
                refine ⟨2598310091467199158950883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3464413455289598878601177 2598310091467199158950883)
                ·
                  refine ⟨3897465137200798738426325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598310091467199158950883 3897465137200798738426325)
                  ·
                    refine ⟨91346839153143720431867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3897465137200798738426325 91346839153143720431867)
                    ·
                      rfl

theorem cell23_533692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_533692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533692 prefixEnd_533692 := by exact prefixLift 533692
  have htrace : WordTrace (prefixWord ++ tailWord_533692) baseStart_533692 baseEnd_533692 := by
    simpa [prefixWord, tailWord_533692, baseEnd_533692] using wordTrace_append hprefix tailTrace_533692
  have hstable : (prefixWord ++ tailWord_533692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533692).length < 2 ^ (prefixWord ++ tailWord_533692).sum := by decide
  have hdescent : baseEnd_533692 < baseStart_533692 := by decide
  rcases family_descends (prefixWord ++ tailWord_533692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533729 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_533729 : Nat := 118140960795 + 533729 * 2 ^ 59
def prefixEnd_533729 : Nat := 4983230072969 + 3 ^ 40 * 533729 * 2
def baseEnd_533729 : Nat := 274059516243647516532931

theorem tailTrace_533729 : CollatzResearch.WordTrace tailWord_533729 prefixEnd_533729 274059516243647516532931 := by
  unfold tailWord_533729
  simp only [CollatzResearch.WordTrace]
  refine ⟨19466695883398461501196241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12977797255598974334130827 19466695883398461501196241)
  ·
    refine ⟨14600021912548846125897181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19466695883398461501196241 14600021912548846125897181)
    ·
      refine ⟨5475008217205817297211443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14600021912548846125897181 5475008217205817297211443)
      ·
        refine ⟨8212512325808725945817165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5475008217205817297211443 8212512325808725945817165)
        ·
          refine ⟨3079692122178272229681437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8212512325808725945817165 3079692122178272229681437)
          ·
            refine ⟨1154884545816852086130539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3079692122178272229681437 1154884545816852086130539)
            ·
              refine ⟨1732326818725278129195809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154884545816852086130539 1732326818725278129195809)
              ·
                refine ⟨1299245114043958596896857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1732326818725278129195809 1299245114043958596896857)
                ·
                  refine ⟨974433835532968947672643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1299245114043958596896857 974433835532968947672643)
                  ·
                    refine ⟨1461650753299453421508965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 974433835532968947672643 1461650753299453421508965)
                    ·
                      refine ⟨274059516243647516532931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1461650753299453421508965 274059516243647516532931)
                      ·
                        rfl

theorem cell23_533729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_533729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533729 prefixEnd_533729 := by exact prefixLift 533729
  have htrace : WordTrace (prefixWord ++ tailWord_533729) baseStart_533729 baseEnd_533729 := by
    simpa [prefixWord, tailWord_533729, baseEnd_533729] using wordTrace_append hprefix tailTrace_533729
  have hstable : (prefixWord ++ tailWord_533729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533729).length < 2 ^ (prefixWord ++ tailWord_533729).sum := by decide
  have hdescent : baseEnd_533729 < baseStart_533729 := by decide
  rcases family_descends (prefixWord ++ tailWord_533729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533739 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 3, 4]
def baseStart_533739 : Nat := 118140960795 + 533739 * 2 ^ 59
def prefixEnd_533739 : Nat := 4983230072969 + 3 ^ 40 * 533739 * 2
def baseEnd_533739 : Nat := 91354883683397492469295

theorem tailTrace_533739 : CollatzResearch.WordTrace tailWord_533739 prefixEnd_533739 91354883683397492469295 := by
  unfold tailWord_533739
  simp only [CollatzResearch.WordTrace]
  refine ⟨19467060613362233209060271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12978040408908155472706847 19467060613362233209060271)
  ·
    refine ⟨29200590920043349813590407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19467060613362233209060271 29200590920043349813590407)
    ·
      refine ⟨43800886380065024720385611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29200590920043349813590407 43800886380065024720385611)
      ·
        refine ⟨65701329570097537080578417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43800886380065024720385611 65701329570097537080578417)
        ·
          refine ⟨49275997177573152810433813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65701329570097537080578417 49275997177573152810433813)
          ·
            refine ⟨2309812367698741537989085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49275997177573152810433813 2309812367698741537989085)
            ·
              refine ⟨866179637887028076745907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2309812367698741537989085 866179637887028076745907)
              ·
                refine ⟨1299269456830542115118861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866179637887028076745907 1299269456830542115118861)
                ·
                  refine ⟨487226046311453293169573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1299269456830542115118861 487226046311453293169573)
                  ·
                    refine ⟨91354883683397492469295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487226046311453293169573 91354883683397492469295)
                    ·
                      rfl

theorem cell23_533739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 4].length) (baseStart_533739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533739 prefixEnd_533739 := by exact prefixLift 533739
  have htrace : WordTrace (prefixWord ++ tailWord_533739) baseStart_533739 baseEnd_533739 := by
    simpa [prefixWord, tailWord_533739, baseEnd_533739] using wordTrace_append hprefix tailTrace_533739
  have hstable : (prefixWord ++ tailWord_533739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533739).length < 2 ^ (prefixWord ++ tailWord_533739).sum := by decide
  have hdescent : baseEnd_533739 < baseStart_533739 := by decide
  rcases family_descends (prefixWord ++ tailWord_533739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533742 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_533742 : Nat := 118140960795 + 533742 * 2 ^ 59
def prefixEnd_533742 : Nat := 4983230072969 + 3 ^ 40 * 533742 * 2
def baseEnd_533742 : Nat := 274066191492155965670371

theorem tailTrace_533742 : CollatzResearch.WordTrace tailWord_533742 prefixEnd_533742 274066191492155965670371 := by
  unfold tailWord_533742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433396254043920590177435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12978113354900909814279653 2433396254043920590177435)
  ·
    refine ⟨3650094381065880885266153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2433396254043920590177435 3650094381065880885266153)
    ·
      refine ⟨2737570785799410663949615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3650094381065880885266153 2737570785799410663949615)
      ·
        refine ⟨4106356178699115995924423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2737570785799410663949615 4106356178699115995924423)
        ·
          refine ⟨6159534268048673993886635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4106356178699115995924423 6159534268048673993886635)
          ·
            refine ⟨9239301402073010990829953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159534268048673993886635 9239301402073010990829953)
            ·
              refine ⟨6929476051554758243122465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9239301402073010990829953 6929476051554758243122465)
              ·
                refine ⟨5197107038666068682341849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6929476051554758243122465 5197107038666068682341849)
                ·
                  refine ⟨3897830278999551511756387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5197107038666068682341849 3897830278999551511756387)
                  ·
                    refine ⟨5846745418499327267634581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3897830278999551511756387 5846745418499327267634581)
                    ·
                      refine ⟨274066191492155965670371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5846745418499327267634581 274066191492155965670371)
                      ·
                        rfl

theorem cell23_533742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_533742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533742 prefixEnd_533742 := by exact prefixLift 533742
  have htrace : WordTrace (prefixWord ++ tailWord_533742) baseStart_533742 baseEnd_533742 := by
    simpa [prefixWord, tailWord_533742, baseEnd_533742] using wordTrace_append hprefix tailTrace_533742
  have hstable : (prefixWord ++ tailWord_533742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533742).length < 2 ^ (prefixWord ++ tailWord_533742).sum := by decide
  have hdescent : baseEnd_533742 < baseStart_533742 := by decide
  rcases family_descends (prefixWord ++ tailWord_533742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533796 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_533796 : Nat := 118140960795 + 533796 * 2 ^ 59
def prefixEnd_533796 : Nat := 4983230072969 + 3 ^ 40 * 533796 * 2
def baseEnd_533796 : Nat := 274093919447498754395123

theorem tailTrace_533796 : CollatzResearch.WordTrace tailWord_533796 prefixEnd_533796 274093919447498754395123 := by
  unfold tailWord_533796
  simp only [CollatzResearch.WordTrace]
  refine ⟨9734569787077865971942621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12979426382770487962590161 9734569787077865971942621)
  ·
    refine ⟨3650463670154199739478483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9734569787077865971942621 3650463670154199739478483)
    ·
      refine ⟨5475695505231299609217725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3650463670154199739478483 5475695505231299609217725)
      ·
        refine ⟨2053385814461737353456647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5475695505231299609217725 2053385814461737353456647)
        ·
          refine ⟨3080078721692606030184971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2053385814461737353456647 3080078721692606030184971)
          ·
            refine ⟨4620118082538909045277457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3080078721692606030184971 4620118082538909045277457)
            ·
              refine ⟨3465088561904181783958093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4620118082538909045277457 3465088561904181783958093)
              ·
                refine ⟨1299408210714068168984285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3465088561904181783958093 1299408210714068168984285)
                ·
                  refine ⟨487278079017775563369107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1299408210714068168984285 487278079017775563369107)
                  ·
                    refine ⟨730917118526663345053661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 487278079017775563369107 730917118526663345053661)
                    ·
                      refine ⟨274093919447498754395123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 730917118526663345053661 274093919447498754395123)
                      ·
                        rfl

theorem cell23_533796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_533796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533796 prefixEnd_533796 := by exact prefixLift 533796
  have htrace : WordTrace (prefixWord ++ tailWord_533796) baseStart_533796 baseEnd_533796 := by
    simpa [prefixWord, tailWord_533796, baseEnd_533796] using wordTrace_append hprefix tailTrace_533796
  have hstable : (prefixWord ++ tailWord_533796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533796).length < 2 ^ (prefixWord ++ tailWord_533796).sum := by decide
  have hdescent : baseEnd_533796 < baseStart_533796 := by decide
  rcases family_descends (prefixWord ++ tailWord_533796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533823 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 2, 3, 2]
def baseStart_533823 : Nat := 118140960795 + 533823 * 2 ^ 59
def prefixEnd_533823 : Nat := 4983230072969 + 3 ^ 40 * 533823 * 2
def baseEnd_533823 : Nat := 274107783425170148757499

theorem tailTrace_533823 : CollatzResearch.WordTrace tailWord_533823 prefixEnd_533823 274107783425170148757499 := by
  unfold tailWord_533823
  simp only [CollatzResearch.WordTrace]
  refine ⟨19470124345057915555118123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12980082896705277036745415 19470124345057915555118123)
  ·
    refine ⟨29205186517586873332677185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19470124345057915555118123 29205186517586873332677185)
    ·
      refine ⟨21903889888190154999507889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29205186517586873332677185 21903889888190154999507889)
      ·
        refine ⟨16427917416142616249630917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21903889888190154999507889 16427917416142616249630917)
        ·
          refine ⟨3080234515526740546805797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16427917416142616249630917 3080234515526740546805797)
          ·
            refine ⟨577543971661263852526087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3080234515526740546805797 577543971661263852526087)
            ·
              refine ⟨866315957491895778789131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577543971661263852526087 866315957491895778789131)
              ·
                refine ⟨1299473936237843668183697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866315957491895778789131 1299473936237843668183697)
                ·
                  refine ⟨974605452178382751137773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1299473936237843668183697 974605452178382751137773)
                  ·
                    refine ⟨365477044566893531676665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 974605452178382751137773 365477044566893531676665)
                    ·
                      refine ⟨274107783425170148757499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365477044566893531676665 274107783425170148757499)
                      ·
                        rfl

theorem cell23_533823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_533823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533823 prefixEnd_533823 := by exact prefixLift 533823
  have htrace : WordTrace (prefixWord ++ tailWord_533823) baseStart_533823 baseEnd_533823 := by
    simpa [prefixWord, tailWord_533823, baseEnd_533823] using wordTrace_append hprefix tailTrace_533823
  have hstable : (prefixWord ++ tailWord_533823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533823).length < 2 ^ (prefixWord ++ tailWord_533823).sum := by decide
  have hdescent : baseEnd_533823 < baseStart_533823 := by decide
  rcases family_descends (prefixWord ++ tailWord_533823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533832 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_533832 : Nat := 118140960795 + 533832 * 2 ^ 59
def prefixEnd_533832 : Nat := 4983230072969 + 3 ^ 40 * 533832 * 2
def baseEnd_533832 : Nat := 274112404751060613544957

theorem tailTrace_533832 : CollatzResearch.WordTrace tailWord_533832 prefixEnd_533832 274112404751060613544957 := by
  unfold tailWord_533832
  simp only [CollatzResearch.WordTrace]
  refine ⟨9735226301012655046097875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12980301734683540061463833 9735226301012655046097875)
  ·
    refine ⟨14602839451518982569146813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9735226301012655046097875 14602839451518982569146813)
    ·
      refine ⟨5476064794319618463430055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14602839451518982569146813 5476064794319618463430055)
      ·
        refine ⟨8214097191479427695145083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5476064794319618463430055 8214097191479427695145083)
        ·
          refine ⟨12321145787219141542717625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8214097191479427695145083 12321145787219141542717625)
          ·
            refine ⟨9240859340414356157038219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12321145787219141542717625 9240859340414356157038219)
            ·
              refine ⟨13861289010621534235557329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9240859340414356157038219 13861289010621534235557329)
              ·
                refine ⟨10395966757966150676667997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13861289010621534235557329 10395966757966150676667997)
                ·
                  refine ⟨3898487534237306503750499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10395966757966150676667997 3898487534237306503750499)
                  ·
                    refine ⟨5847731301355959755625749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3898487534237306503750499 5847731301355959755625749)
                    ·
                      refine ⟨274112404751060613544957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5847731301355959755625749 274112404751060613544957)
                      ·
                        rfl

theorem cell23_533832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_533832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533832 prefixEnd_533832 := by exact prefixLift 533832
  have htrace : WordTrace (prefixWord ++ tailWord_533832) baseStart_533832 baseEnd_533832 := by
    simpa [prefixWord, tailWord_533832, baseEnd_533832] using wordTrace_append hprefix tailTrace_533832
  have hstable : (prefixWord ++ tailWord_533832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533832).length < 2 ^ (prefixWord ++ tailWord_533832).sum := by decide
  have hdescent : baseEnd_533832 < baseStart_533832 := by decide
  rcases family_descends (prefixWord ++ tailWord_533832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533836 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 1, 1, 4]
def baseStart_533836 : Nat := 118140960795 + 533836 * 2 ^ 59
def prefixEnd_533836 : Nat := 4983230072969 + 3 ^ 40 * 533836 * 2
def baseEnd_533836 : Nat := 274114458673678597894939

theorem tailTrace_533836 : CollatzResearch.WordTrace tailWord_533836 prefixEnd_533836 274114458673678597894939 := by
  unfold tailWord_533836
  simp only [CollatzResearch.WordTrace]
  refine ⟨9735299247005409387670681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12980398996007212516894241 9735299247005409387670681)
  ·
    refine ⟨7301474435254057040753011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9735299247005409387670681 7301474435254057040753011)
    ·
      refine ⟨10952211652881085561129517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7301474435254057040753011 10952211652881085561129517)
      ·
        refine ⟨4107079369830407085423569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10952211652881085561129517 4107079369830407085423569)
        ·
          refine ⟨3080309527372805314067677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4107079369830407085423569 3080309527372805314067677)
          ·
            refine ⟨1155116072764801992775379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3080309527372805314067677 1155116072764801992775379)
            ·
              refine ⟨1732674109147202989163069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155116072764801992775379 1732674109147202989163069)
              ·
                refine ⟨649752790930201120936151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732674109147202989163069 649752790930201120936151)
                ·
                  refine ⟨974629186395301681404227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649752790930201120936151 974629186395301681404227)
                  ·
                    refine ⟨1461943779592952522106341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 974629186395301681404227 1461943779592952522106341)
                    ·
                      refine ⟨274114458673678597894939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1461943779592952522106341 274114458673678597894939)
                      ·
                        rfl

theorem cell23_533836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_533836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533836 prefixEnd_533836 := by exact prefixLift 533836
  have htrace : WordTrace (prefixWord ++ tailWord_533836) baseStart_533836 baseEnd_533836 := by
    simpa [prefixWord, tailWord_533836, baseEnd_533836] using wordTrace_append hprefix tailTrace_533836
  have hstable : (prefixWord ++ tailWord_533836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533836).length < 2 ^ (prefixWord ++ tailWord_533836).sum := by decide
  have hdescent : baseEnd_533836 < baseStart_533836 := by decide
  rcases family_descends (prefixWord ++ tailWord_533836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533863 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 1, 6]
def baseStart_533863 : Nat := 118140960795 + 533863 * 2 ^ 59
def prefixEnd_533863 : Nat := 4983230072969 + 3 ^ 40 * 533863 * 2
def baseEnd_533863 : Nat := 91376107550449997419105

theorem tailTrace_533863 : CollatzResearch.WordTrace tailWord_533863 prefixEnd_533863 91376107550449997419105 := by
  unfold tailWord_533863
  simp only [CollatzResearch.WordTrace]
  refine ⟨19471583264913002386574243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12981055509942001591049495 19471583264913002386574243)
  ·
    refine ⟨29207374897369503579861365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19471583264913002386574243 29207374897369503579861365)
    ·
      refine ⟨2738191396628390960612003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29207374897369503579861365 2738191396628390960612003)
      ·
        refine ⟨4107287094942586440918005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2738191396628390960612003 4107287094942586440918005)
        ·
          refine ⟨385058165150867478836063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4107287094942586440918005 385058165150867478836063)
          ·
            refine ⟨577587247726301218254095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385058165150867478836063 577587247726301218254095)
            ·
              refine ⟨866380871589451827381143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577587247726301218254095 866380871589451827381143)
              ·
                refine ⟨1299571307384177741071715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866380871589451827381143 1299571307384177741071715)
                ·
                  refine ⟨1949356961076266611607573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299571307384177741071715 1949356961076266611607573)
                  ·
                    refine ⟨91376107550449997419105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1949356961076266611607573 91376107550449997419105)
                    ·
                      rfl

theorem cell23_533863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_533863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533863 prefixEnd_533863 := by exact prefixLift 533863
  have htrace : WordTrace (prefixWord ++ tailWord_533863) baseStart_533863 baseEnd_533863 := by
    simpa [prefixWord, tailWord_533863, baseEnd_533863] using wordTrace_append hprefix tailTrace_533863
  have hstable : (prefixWord ++ tailWord_533863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533863).length < 2 ^ (prefixWord ++ tailWord_533863).sum := by decide
  have hdescent : baseEnd_533863 < baseStart_533863 := by decide
  rcases family_descends (prefixWord ++ tailWord_533863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533866 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_533866 : Nat := 118140960795 + 533866 * 2 ^ 59
def prefixEnd_533866 : Nat := 4983230072969 + 3 ^ 40 * 533866 * 2
def baseEnd_533866 : Nat := 274129863093313480519801

theorem tailTrace_533866 : CollatzResearch.WordTrace tailWord_533866 prefixEnd_533866 274129863093313480519801 := by
  unfold tailWord_533866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867923170975533474733363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12981128455934755932622301 4867923170975533474733363)
  ·
    refine ⟨7301884756463300212100045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4867923170975533474733363 7301884756463300212100045)
    ·
      refine ⟨2738206783673737579537517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7301884756463300212100045 2738206783673737579537517)
      ·
        refine ⟨1026827543877651592326569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2738206783673737579537517 1026827543877651592326569)
        ·
          refine ⟨770120657908238694244927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1026827543877651592326569 770120657908238694244927)
          ·
            refine ⟨1155180986862358041367391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770120657908238694244927 1155180986862358041367391)
            ·
              refine ⟨1732771480293537062051087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155180986862358041367391 1732771480293537062051087)
              ·
                refine ⟨2599157220440305593076631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732771480293537062051087 2599157220440305593076631)
                ·
                  refine ⟨3898735830660458389614947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2599157220440305593076631 3898735830660458389614947)
                  ·
                    refine ⟨5848103745990687584422421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3898735830660458389614947 5848103745990687584422421)
                    ·
                      refine ⟨274129863093313480519801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5848103745990687584422421 274129863093313480519801)
                      ·
                        rfl

theorem cell23_533866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_533866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533866 prefixEnd_533866 := by exact prefixLift 533866
  have htrace : WordTrace (prefixWord ++ tailWord_533866) baseStart_533866 baseEnd_533866 := by
    simpa [prefixWord, tailWord_533866, baseEnd_533866] using wordTrace_append hprefix tailTrace_533866
  have hstable : (prefixWord ++ tailWord_533866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533866).length < 2 ^ (prefixWord ++ tailWord_533866).sum := by decide
  have hdescent : baseEnd_533866 < baseStart_533866 := by decide
  rcases family_descends (prefixWord ++ tailWord_533866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533870 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_533870 : Nat := 118140960795 + 533870 * 2 ^ 59
def prefixEnd_533870 : Nat := 4983230072969 + 3 ^ 40 * 533870 * 2
def baseEnd_533870 : Nat := 274131917015931464869783

theorem tailTrace_533870 : CollatzResearch.WordTrace tailWord_533870 prefixEnd_533870 274131917015931464869783 := by
  unfold tailWord_533870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433979821985955322759883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12981225717258428388052709 2433979821985955322759883)
  ·
    refine ⟨3650969732978932984139825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2433979821985955322759883 3650969732978932984139825)
    ·
      refine ⟨2738227299734199738104869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3650969732978932984139825 2738227299734199738104869)
      ·
        refine ⟨513417618700162450894663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2738227299734199738104869 513417618700162450894663)
        ·
          refine ⟨770126428050243676341995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513417618700162450894663 770126428050243676341995)
          ·
            refine ⟨1155189642075365514512993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770126428050243676341995 1155189642075365514512993)
            ·
              refine ⟨866392231556524135884745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155189642075365514512993 866392231556524135884745)
              ·
                refine ⟨649794173667393101913559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866392231556524135884745 649794173667393101913559)
                ·
                  refine ⟨974691260501089652870339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649794173667393101913559 974691260501089652870339)
                  ·
                    refine ⟨1462036890751634479305509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 974691260501089652870339 1462036890751634479305509)
                    ·
                      refine ⟨274131917015931464869783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1462036890751634479305509 274131917015931464869783)
                      ·
                        rfl

theorem cell23_533870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_533870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533870 prefixEnd_533870 := by exact prefixLift 533870
  have htrace : WordTrace (prefixWord ++ tailWord_533870) baseStart_533870 baseEnd_533870 := by
    simpa [prefixWord, tailWord_533870, baseEnd_533870] using wordTrace_append hprefix tailTrace_533870
  have hstable : (prefixWord ++ tailWord_533870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533870).length < 2 ^ (prefixWord ++ tailWord_533870).sum := by decide
  have hdescent : baseEnd_533870 < baseStart_533870 := by decide
  rcases family_descends (prefixWord ++ tailWord_533870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533890 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_533890 : Nat := 118140960795 + 533890 * 2 ^ 59
def prefixEnd_533890 : Nat := 4983230072969 + 3 ^ 40 * 533890 * 2
def baseEnd_533890 : Nat := 274142186629021386619691

theorem tailTrace_533890 : CollatzResearch.WordTrace tailWord_533890 prefixEnd_533890 274142186629021386619691 := by
  unfold tailWord_533890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4868142008953796499451781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12981712023876790665204749 4868142008953796499451781)
  ·
    refine ⟨912776626678836843647209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4868142008953796499451781 912776626678836843647209)
    ·
      refine ⟨684582470009127632735407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 912776626678836843647209 684582470009127632735407)
      ·
        refine ⟨1026873705013691449103111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684582470009127632735407 1026873705013691449103111)
        ·
          refine ⟨1540310557520537173654667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026873705013691449103111 1540310557520537173654667)
          ·
            refine ⟨2310465836280805760482001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540310557520537173654667 2310465836280805760482001)
            ·
              refine ⟨1732849377210604320361501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2310465836280805760482001 1732849377210604320361501)
              ·
                refine ⟨649818516453976620135563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732849377210604320361501 649818516453976620135563)
                ·
                  refine ⟨974727774680964930203345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649818516453976620135563 974727774680964930203345)
                  ·
                    refine ⟨731045831010723697652509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 974727774680964930203345 731045831010723697652509)
                    ·
                      refine ⟨274142186629021386619691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 731045831010723697652509 274142186629021386619691)
                      ·
                        rfl

theorem cell23_533890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_533890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533890 prefixEnd_533890 := by exact prefixLift 533890
  have htrace : WordTrace (prefixWord ++ tailWord_533890) baseStart_533890 baseEnd_533890 := by
    simpa [prefixWord, tailWord_533890, baseEnd_533890] using wordTrace_append hprefix tailTrace_533890
  have hstable : (prefixWord ++ tailWord_533890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533890).length < 2 ^ (prefixWord ++ tailWord_533890).sum := by decide
  have hdescent : baseEnd_533890 < baseStart_533890 := by decide
  rcases family_descends (prefixWord ++ tailWord_533890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533960 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 2, 2, 2]
def baseStart_533960 : Nat := 118140960795 + 533960 * 2 ^ 59
def prefixEnd_533960 : Nat := 4983230072969 + 3 ^ 40 * 533960 * 2
def baseEnd_533960 : Nat := 274178130274836112744369

theorem tailTrace_533960 : CollatzResearch.WordTrace tailWord_533960 prefixEnd_533960 274178130274836112744369 := by
  unfold tailWord_533960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9737560572780793976427667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12983414097041058635236889 9737560572780793976427667)
  ·
    refine ⟨14606340859171190964641501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9737560572780793976427667 14606340859171190964641501)
    ·
      refine ⟨5477377822189196611740563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14606340859171190964641501 5477377822189196611740563)
      ·
        refine ⟨8216066733283794917610845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5477377822189196611740563 8216066733283794917610845)
        ·
          refine ⟨3081025024981423094104067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8216066733283794917610845 3081025024981423094104067)
          ·
            refine ⟨4621537537472134641156101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3081025024981423094104067 4621537537472134641156101)
            ·
              refine ⟨866538288276025245216769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4621537537472134641156101 866538288276025245216769)
              ·
                refine ⟨649903716207018933912577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866538288276025245216769 649903716207018933912577)
                ·
                  refine ⟨487427787155264200434433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 649903716207018933912577 487427787155264200434433)
                  ·
                    refine ⟨365570840366448150325825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 487427787155264200434433 365570840366448150325825)
                    ·
                      refine ⟨274178130274836112744369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365570840366448150325825 274178130274836112744369)
                      ·
                        rfl

theorem cell23_533960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_533960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533960 prefixEnd_533960 := by exact prefixLift 533960
  have htrace : WordTrace (prefixWord ++ tailWord_533960) baseStart_533960 baseEnd_533960 := by
    simpa [prefixWord, tailWord_533960, baseEnd_533960] using wordTrace_append hprefix tailTrace_533960
  have hstable : (prefixWord ++ tailWord_533960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533960).length < 2 ^ (prefixWord ++ tailWord_533960).sum := by decide
  have hdescent : baseEnd_533960 < baseStart_533960 := by decide
  rcases family_descends (prefixWord ++ tailWord_533960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534077 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_534077 : Nat := 118140960795 + 534077 * 2 ^ 59
def prefixEnd_534077 : Nat := 4983230072969 + 3 ^ 40 * 534077 * 2
def baseEnd_534077 : Nat := 91412735837137384993777

theorem tailTrace_534077 : CollatzResearch.WordTrace tailWord_534077 prefixEnd_534077 91412735837137384993777 := by
  unfold tailWord_534077
  simp only [CollatzResearch.WordTrace]
  refine ⟨19479388486137716934864485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12986258990758477956576323 19479388486137716934864485)
  ·
    refine ⟨3652385341150821925287091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19479388486137716934864485 3652385341150821925287091)
    ·
      refine ⟨5478578011726232887930637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3652385341150821925287091 5478578011726232887930637)
      ·
        refine ⟨2054466754397337332973989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5478578011726232887930637 2054466754397337332973989)
        ·
          refine ⟨385212516449500749932623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2054466754397337332973989 385212516449500749932623)
          ·
            refine ⟨577818774674251124898935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385212516449500749932623 577818774674251124898935)
            ·
              refine ⟨866728162011376687348403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577818774674251124898935 866728162011376687348403)
              ·
                refine ⟨1300092243017065031022605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866728162011376687348403 1300092243017065031022605)
                ·
                  refine ⟨487534591131399386633477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1300092243017065031022605 487534591131399386633477)
                  ·
                    refine ⟨91412735837137384993777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487534591131399386633477 91412735837137384993777)
                    ·
                      rfl

theorem cell23_534077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_534077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534077 prefixEnd_534077 := by exact prefixLift 534077
  have htrace : WordTrace (prefixWord ++ tailWord_534077) baseStart_534077 baseEnd_534077 := by
    simpa [prefixWord, tailWord_534077, baseEnd_534077] using wordTrace_append hprefix tailTrace_534077
  have hstable : (prefixWord ++ tailWord_534077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534077).length < 2 ^ (prefixWord ++ tailWord_534077).sum := by decide
  have hdescent : baseEnd_534077 < baseStart_534077 := by decide
  rcases family_descends (prefixWord ++ tailWord_534077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534103 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 1, 5]
def baseStart_534103 : Nat := 118140960795 + 534103 * 2 ^ 59
def prefixEnd_534103 : Nat := 4983230072969 + 3 ^ 40 * 534103 * 2
def baseEnd_534103 : Nat := 91417186002809684418737

theorem tailTrace_534103 : CollatzResearch.WordTrace tailWord_534103 prefixEnd_534103 91417186002809684418737 := by
  unfold tailWord_534103
  simp only [CollatzResearch.WordTrace]
  refine ⟨19480336784043523375310963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12986891189362348916873975 19480336784043523375310963)
  ·
    refine ⟨29220505176065285062966445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19480336784043523375310963 29220505176065285062966445)
    ·
      refine ⟨10957689441024481898612417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29220505176065285062966445 10957689441024481898612417)
      ·
        refine ⟨8218267080768361423959313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10957689441024481898612417 8218267080768361423959313)
        ·
          refine ⟨6163700310576271067969485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8218267080768361423959313 6163700310576271067969485)
          ·
            refine ⟨2311387616466101650488557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6163700310576271067969485 2311387616466101650488557)
            ·
              refine ⟨866770356174788118933209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2311387616466101650488557 866770356174788118933209)
              ·
                refine ⟨650077767131091089199907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866770356174788118933209 650077767131091089199907)
                ·
                  refine ⟨975116650696636633799861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650077767131091089199907 975116650696636633799861)
                  ·
                    refine ⟨91417186002809684418737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 975116650696636633799861 91417186002809684418737)
                    ·
                      rfl

theorem cell23_534103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_534103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534103 prefixEnd_534103 := by exact prefixLift 534103
  have htrace : WordTrace (prefixWord ++ tailWord_534103) baseStart_534103 baseEnd_534103 := by
    simpa [prefixWord, tailWord_534103, baseEnd_534103] using wordTrace_append hprefix tailTrace_534103
  have hstable : (prefixWord ++ tailWord_534103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534103).length < 2 ^ (prefixWord ++ tailWord_534103).sum := by decide
  have hdescent : baseEnd_534103 < baseStart_534103 := by decide
  rcases family_descends (prefixWord ++ tailWord_534103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534116 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_534116 : Nat := 118140960795 + 534116 * 2 ^ 59
def prefixEnd_534116 : Nat := 4983230072969 + 3 ^ 40 * 534116 * 2
def baseEnd_534116 : Nat := 91419411085645834131217

theorem tailTrace_534116 : CollatzResearch.WordTrace tailWord_534116 prefixEnd_534116 91419411085645834131217 := by
  unfold tailWord_534116
  simp only [CollatzResearch.WordTrace]
  refine ⟨9740405466498213297767101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12987207288664284397022801 9740405466498213297767101)
  ·
    refine ⟨3652652049936829986662663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9740405466498213297767101 3652652049936829986662663)
    ·
      refine ⟨5478978074905244979993995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3652652049936829986662663 5478978074905244979993995)
      ·
        refine ⟨8218467112357867469990993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5478978074905244979993995 8218467112357867469990993)
        ·
          refine ⟨6163850334268400602493245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8218467112357867469990993 6163850334268400602493245)
          ·
            refine ⟨2311443875350650225934967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6163850334268400602493245 2311443875350650225934967)
            ·
              refine ⟨3467165813025975338902451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311443875350650225934967 3467165813025975338902451)
              ·
                refine ⟨5200748719538963008353677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467165813025975338902451 5200748719538963008353677)
                ·
                  refine ⟨1950280769827111128132629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5200748719538963008353677 1950280769827111128132629)
                  ·
                    refine ⟨91419411085645834131217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1950280769827111128132629 91419411085645834131217)
                    ·
                      rfl

theorem cell23_534116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_534116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534116 prefixEnd_534116 := by exact prefixLift 534116
  have htrace : WordTrace (prefixWord ++ tailWord_534116) baseStart_534116 baseEnd_534116 := by
    simpa [prefixWord, tailWord_534116, baseEnd_534116] using wordTrace_append hprefix tailTrace_534116
  have hstable : (prefixWord ++ tailWord_534116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534116).length < 2 ^ (prefixWord ++ tailWord_534116).sum := by decide
  have hdescent : baseEnd_534116 < baseStart_534116 := by decide
  rcases family_descends (prefixWord ++ tailWord_534116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534134 : List Nat := [5, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_534134 : Nat := 118140960795 + 534134 * 2 ^ 59
def prefixEnd_534134 : Nat := 4983230072969 + 3 ^ 40 * 534134 * 2
def baseEnd_534134 : Nat := 274267475908718431968569

theorem tailTrace_534134 : CollatzResearch.WordTrace tailWord_534134 prefixEnd_534134 274267475908718431968569 := by
  unfold tailWord_534134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1217591715433200979355591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12987644964620810446459637 1217591715433200979355591)
  ·
    refine ⟨1826387573149801469033387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1217591715433200979355591 1826387573149801469033387)
    ·
      refine ⟨2739581359724702203550081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1826387573149801469033387 2739581359724702203550081)
      ·
        refine ⟨2054686019793526652662561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2739581359724702203550081 2054686019793526652662561)
        ·
          refine ⟨1541014514845144989496921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054686019793526652662561 1541014514845144989496921)
          ·
            refine ⟨1155760886133858742122691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1541014514845144989496921 1155760886133858742122691)
            ·
              refine ⟨1733641329200788113184037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155760886133858742122691 1733641329200788113184037)
              ·
                refine ⟨325057749225147771222007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1733641329200788113184037 325057749225147771222007)
                ·
                  refine ⟨487586623837721656833011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325057749225147771222007 487586623837721656833011)
                  ·
                    refine ⟨731379935756582485249517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 487586623837721656833011 731379935756582485249517)
                    ·
                      refine ⟨274267475908718431968569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 731379935756582485249517 274267475908718431968569)
                      ·
                        rfl

theorem cell23_534134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_534134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534134 prefixEnd_534134 := by exact prefixLift 534134
  have htrace : WordTrace (prefixWord ++ tailWord_534134) baseStart_534134 baseEnd_534134 := by
    simpa [prefixWord, tailWord_534134, baseEnd_534134] using wordTrace_append hprefix tailTrace_534134
  have hstable : (prefixWord ++ tailWord_534134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534134).length < 2 ^ (prefixWord ++ tailWord_534134).sum := by decide
  have hdescent : baseEnd_534134 < baseStart_534134 := by decide
  rcases family_descends (prefixWord ++ tailWord_534134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534140 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 3, 2, 2]
def baseStart_534140 : Nat := 118140960795 + 534140 * 2 ^ 59
def prefixEnd_534140 : Nat := 4983230072969 + 3 ^ 40 * 534140 * 2
def baseEnd_534140 : Nat := 274270556792645408493541

theorem tailTrace_534140 : CollatzResearch.WordTrace tailWord_534140 prefixEnd_534140 274270556792645408493541 := by
  unfold tailWord_534140
  simp only [CollatzResearch.WordTrace]
  refine ⟨9740843142454739347203937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12987790856606319129605249 9740843142454739347203937)
  ·
    refine ⟨7305632356841054510402953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9740843142454739347203937 7305632356841054510402953)
    ·
      refine ⟨5479224267630790882802215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7305632356841054510402953 5479224267630790882802215)
      ·
        refine ⟨8218836401446186324203323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5479224267630790882802215 8218836401446186324203323)
        ·
          refine ⟨12328254602169279486304985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8218836401446186324203323 12328254602169279486304985)
          ·
            refine ⟨9246190951626959614728739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12328254602169279486304985 9246190951626959614728739)
            ·
              refine ⟨13869286427440439422093109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9246190951626959614728739 13869286427440439422093109)
              ·
                refine ⟨1300245602572541195821229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13869286427440439422093109 1300245602572541195821229)
                ·
                  refine ⟨487592100964702948432961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1300245602572541195821229 487592100964702948432961)
                  ·
                    refine ⟨365694075723527211324721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 487592100964702948432961 365694075723527211324721)
                    ·
                      refine ⟨274270556792645408493541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365694075723527211324721 274270556792645408493541)
                      ·
                        rfl

theorem cell23_534140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_534140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534140 prefixEnd_534140 := by exact prefixLift 534140
  have htrace : WordTrace (prefixWord ++ tailWord_534140) baseStart_534140 baseEnd_534140 := by
    simpa [prefixWord, tailWord_534140, baseEnd_534140] using wordTrace_append hprefix tailTrace_534140
  have hstable : (prefixWord ++ tailWord_534140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534140).length < 2 ^ (prefixWord ++ tailWord_534140).sum := by decide
  have hdescent : baseEnd_534140 < baseStart_534140 := by decide
  rcases family_descends (prefixWord ++ tailWord_534140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534174 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_534174 : Nat := 118140960795 + 534174 * 2 ^ 59
def prefixEnd_534174 : Nat := 4983230072969 + 3 ^ 40 * 534174 * 2
def baseEnd_534174 : Nat := 274288015134898275468385

theorem tailTrace_534174 : CollatzResearch.WordTrace tailWord_534174 prefixEnd_534174 274288015134898275468385 := by
  unfold tailWord_534174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435365795848287812643197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12988617577857535000763717 2435365795848287812643197)
  ·
    refine ⟨913262173443107929741199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2435365795848287812643197 913262173443107929741199)
    ·
      refine ⟨1369893260164661894611799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 913262173443107929741199 1369893260164661894611799)
      ·
        refine ⟨2054839890246992841917699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1369893260164661894611799 2054839890246992841917699)
        ·
          refine ⟨3082259835370489262876549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054839890246992841917699 3082259835370489262876549)
          ·
            refine ⟨577923719131966736789353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3082259835370489262876549 577923719131966736789353)
            ·
              refine ⟨433442789348975052592015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577923719131966736789353 433442789348975052592015)
              ·
                refine ⟨650164184023462578888023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433442789348975052592015 650164184023462578888023)
                ·
                  refine ⟨975246276035193868332035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650164184023462578888023 975246276035193868332035)
                  ·
                    refine ⟨1462869414052790802498053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 975246276035193868332035 1462869414052790802498053)
                    ·
                      refine ⟨274288015134898275468385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1462869414052790802498053 274288015134898275468385)
                      ·
                        rfl

theorem cell23_534174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_534174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534174 prefixEnd_534174 := by exact prefixLift 534174
  have htrace : WordTrace (prefixWord ++ tailWord_534174) baseStart_534174 baseEnd_534174 := by
    simpa [prefixWord, tailWord_534174, baseEnd_534174] using wordTrace_append hprefix tailTrace_534174
  have hstable : (prefixWord ++ tailWord_534174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534174).length < 2 ^ (prefixWord ++ tailWord_534174).sum := by decide
  have hdescent : baseEnd_534174 < baseStart_534174 := by decide
  rcases family_descends (prefixWord ++ tailWord_534174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534177 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 1, 2, 3]
def baseStart_534177 : Nat := 118140960795 + 534177 * 2 ^ 59
def prefixEnd_534177 : Nat := 4983230072969 + 3 ^ 40 * 534177 * 2
def baseEnd_534177 : Nat := 274289555576861763730871

theorem tailTrace_534177 : CollatzResearch.WordTrace tailWord_534177 prefixEnd_534177 274289555576861763730871 := by
  unfold tailWord_534177
  simp only [CollatzResearch.WordTrace]
  refine ⟨19483035785775434013504785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12988690523850289342336523 19483035785775434013504785)
  ·
    refine ⟨14612276839331575510128589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19483035785775434013504785 14612276839331575510128589)
    ·
      refine ⟨5479603814749340816298221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14612276839331575510128589 5479603814749340816298221)
      ·
        refine ⟨2054851430531002806111833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5479603814749340816298221 2054851430531002806111833)
        ·
          refine ⟨1541138572898252104583875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054851430531002806111833 1541138572898252104583875)
          ·
            refine ⟨2311707859347378156875813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541138572898252104583875 2311707859347378156875813)
            ·
              refine ⟨433445223627633404414215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2311707859347378156875813 433445223627633404414215)
              ·
                refine ⟨650167835441450106621323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433445223627633404414215 650167835441450106621323)
                ·
                  refine ⟨975251753162175159931985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650167835441450106621323 975251753162175159931985)
                  ·
                    refine ⟨731438814871631369948989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 975251753162175159931985 731438814871631369948989)
                    ·
                      refine ⟨274289555576861763730871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 731438814871631369948989 274289555576861763730871)
                      ·
                        rfl

theorem cell23_534177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_534177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534177 prefixEnd_534177 := by exact prefixLift 534177
  have htrace : WordTrace (prefixWord ++ tailWord_534177) baseStart_534177 baseEnd_534177 := by
    simpa [prefixWord, tailWord_534177, baseEnd_534177] using wordTrace_append hprefix tailTrace_534177
  have hstable : (prefixWord ++ tailWord_534177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534177).length < 2 ^ (prefixWord ++ tailWord_534177).sum := by decide
  have hdescent : baseEnd_534177 < baseStart_534177 := by decide
  rcases family_descends (prefixWord ++ tailWord_534177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534184 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 4, 4]
def baseStart_534184 : Nat := 118140960795 + 534184 * 2 ^ 59
def prefixEnd_534184 : Nat := 4983230072969 + 3 ^ 40 * 534184 * 2
def baseEnd_534184 : Nat := 91431049980481078781113

theorem tailTrace_534184 : CollatzResearch.WordTrace tailWord_534184 prefixEnd_534184 91431049980481078781113 := by
  unfold tailWord_534184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9741645548375037104504803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12988860731166716139339737 9741645548375037104504803)
  ·
    refine ⟨14612468322562555656757205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9741645548375037104504803 14612468322562555656757205)
    ·
      refine ⟨342479726310059898205247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14612468322562555656757205 342479726310059898205247)
      ·
        refine ⟨513719589465089847307871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342479726310059898205247 513719589465089847307871)
        ·
          refine ⟨770579384197634770961807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513719589465089847307871 770579384197634770961807)
          ·
            refine ⟨1155869076296452156442711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770579384197634770961807 1155869076296452156442711)
            ·
              refine ⟨1733803614444678234664067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155869076296452156442711 1733803614444678234664067)
              ·
                refine ⟨2600705421667017351996101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733803614444678234664067 2600705421667017351996101)
                ·
                  refine ⟨487632266562565753499269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2600705421667017351996101 487632266562565753499269)
                  ·
                    refine ⟨91431049980481078781113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487632266562565753499269 91431049980481078781113)
                    ·
                      rfl

theorem cell23_534184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_534184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534184 prefixEnd_534184 := by exact prefixLift 534184
  have htrace : WordTrace (prefixWord ++ tailWord_534184) baseStart_534184 baseEnd_534184 := by
    simpa [prefixWord, tailWord_534184, baseEnd_534184] using wordTrace_append hprefix tailTrace_534184
  have hstable : (prefixWord ++ tailWord_534184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534184).length < 2 ^ (prefixWord ++ tailWord_534184).sum := by decide
  have hdescent : baseEnd_534184 < baseStart_534184 := by decide
  rcases family_descends (prefixWord ++ tailWord_534184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534207 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 2, 1, 3]
def baseStart_534207 : Nat := 118140960795 + 534207 * 2 ^ 59
def prefixEnd_534207 : Nat := 4983230072969 + 3 ^ 40 * 534207 * 2
def baseEnd_534207 : Nat := 274304959996496646355733

theorem tailTrace_534207 : CollatzResearch.WordTrace tailWord_534207 prefixEnd_534207 274304959996496646355733 := by
  unfold tailWord_534207
  simp only [CollatzResearch.WordTrace]
  refine ⟨19484129975666749137096875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12989419983777832758064583 19484129975666749137096875)
  ·
    refine ⟨29226194963500123705645313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19484129975666749137096875 29226194963500123705645313)
    ·
      refine ⟨21919646222625092779233985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29226194963500123705645313 21919646222625092779233985)
      ·
        refine ⟨16439734666968819584425489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21919646222625092779233985 16439734666968819584425489)
        ·
          refine ⟨12329801000226614688319117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16439734666968819584425489 12329801000226614688319117)
          ·
            refine ⟨4623675375084980508119669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12329801000226614688319117 4623675375084980508119669)
            ·
              refine ⟨433469566414216922636219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4623675375084980508119669 433469566414216922636219)
              ·
                refine ⟨650204349621325383954329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433469566414216922636219 650204349621325383954329)
                ·
                  refine ⟨487653262215994037965747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 650204349621325383954329 487653262215994037965747)
                  ·
                    refine ⟨731479893323991056948621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 487653262215994037965747 731479893323991056948621)
                    ·
                      refine ⟨274304959996496646355733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 731479893323991056948621 274304959996496646355733)
                      ·
                        rfl

theorem cell23_534207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_534207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534207 prefixEnd_534207 := by exact prefixLift 534207
  have htrace : WordTrace (prefixWord ++ tailWord_534207) baseStart_534207 baseEnd_534207 := by
    simpa [prefixWord, tailWord_534207, baseEnd_534207] using wordTrace_append hprefix tailTrace_534207
  have hstable : (prefixWord ++ tailWord_534207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534207).length < 2 ^ (prefixWord ++ tailWord_534207).sum := by decide
  have hdescent : baseEnd_534207 < baseStart_534207 := by decide
  rcases family_descends (prefixWord ++ tailWord_534207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534214 : List Nat := [6, 1, 2, 1, 1, 3, 2, 7]
def baseStart_534214 : Nat := 118140960795 + 534214 * 2 ^ 59
def prefixEnd_534214 : Nat := 4983230072969 + 3 ^ 40 * 534214 * 2
def baseEnd_534214 : Nat := 10159576087447337739563

theorem tailTrace_534214 : CollatzResearch.WordTrace tailWord_534214 prefixEnd_534214 10159576087447337739563 := by
  unfold tailWord_534214
  simp only [CollatzResearch.WordTrace]
  refine ⟨608887040207543416643803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12989590191094259555067797 608887040207543416643803)
  ·
    refine ⟨913330560311315124965705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 608887040207543416643803 913330560311315124965705)
    ·
      refine ⟨684997920233486343724279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 913330560311315124965705 684997920233486343724279)
      ·
        refine ⟨1027496880350229515586419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684997920233486343724279 1027496880350229515586419)
        ·
          refine ⟨1541245320525344273379629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027496880350229515586419 1541245320525344273379629)
          ·
            refine ⟨577966995197004102517361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1541245320525344273379629 577966995197004102517361)
            ·
              refine ⟨433475246397753076888021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577966995197004102517361 433475246397753076888021)
              ·
                refine ⟨10159576087447337739563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 433475246397753076888021 10159576087447337739563)
                ·
                  rfl

theorem cell23_534214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_534214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534214 prefixEnd_534214 := by exact prefixLift 534214
  have htrace : WordTrace (prefixWord ++ tailWord_534214) baseStart_534214 baseEnd_534214 := by
    simpa [prefixWord, tailWord_534214, baseEnd_534214] using wordTrace_append hprefix tailTrace_534214
  have hstable : (prefixWord ++ tailWord_534214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534214).length < 2 ^ (prefixWord ++ tailWord_534214).sum := by decide
  have hdescent : baseEnd_534214 < baseStart_534214 := by decide
  rcases family_descends (prefixWord ++ tailWord_534214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534233 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 5]
def baseStart_534233 : Nat := 118140960795 + 534233 * 2 ^ 59
def prefixEnd_534233 : Nat := 4983230072969 + 3 ^ 40 * 534233 * 2
def baseEnd_534233 : Nat := 274318310493513544630613

theorem tailTrace_534233 : CollatzResearch.WordTrace tailWord_534233 prefixEnd_534233 274318310493513544630613 := by
  unfold tailWord_534233
  simp only [CollatzResearch.WordTrace]
  refine ⟨19485078273572555577543353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12990052182381703718362235 19485078273572555577543353)
  ·
    refine ⟨14613808705179416683157515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19485078273572555577543353 14613808705179416683157515)
    ·
      refine ⟨21920713057769125024736273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14613808705179416683157515 21920713057769125024736273)
      ·
        refine ⟨16440534793326843768552205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21920713057769125024736273 16440534793326843768552205)
        ·
          refine ⟨6165200547497566413207077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16440534793326843768552205 6165200547497566413207077)
          ·
            refine ⟨1155975102655793702476327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6165200547497566413207077 1155975102655793702476327)
            ·
              refine ⟨1733962653983690553714491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155975102655793702476327 1733962653983690553714491)
              ·
                refine ⟨2600943980975535830571737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733962653983690553714491 2600943980975535830571737)
                ·
                  refine ⟨1950707985731651872928803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2600943980975535830571737 1950707985731651872928803)
                  ·
                    refine ⟨2926061978597477809393205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1950707985731651872928803 2926061978597477809393205)
                    ·
                      refine ⟨274318310493513544630613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2926061978597477809393205 274318310493513544630613)
                      ·
                        rfl

theorem cell23_534233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_534233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534233 prefixEnd_534233 := by exact prefixLift 534233
  have htrace : WordTrace (prefixWord ++ tailWord_534233) baseStart_534233 baseEnd_534233 := by
    simpa [prefixWord, tailWord_534233, baseEnd_534233] using wordTrace_append hprefix tailTrace_534233
  have hstable : (prefixWord ++ tailWord_534233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534233).length < 2 ^ (prefixWord ++ tailWord_534233).sum := by decide
  have hdescent : baseEnd_534233 < baseStart_534233 := by decide
  rcases family_descends (prefixWord ++ tailWord_534233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534256 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_534256 : Nat := 118140960795 + 534256 * 2 ^ 59
def prefixEnd_534256 : Nat := 4983230072969 + 3 ^ 40 * 534256 * 2
def baseEnd_534256 : Nat := 274330120548566954643007

theorem tailTrace_534256 : CollatzResearch.WordTrace tailWord_534256 prefixEnd_534256 274330120548566954643007 := by
  unfold tailWord_534256
  simp only [CollatzResearch.WordTrace]
  refine ⟨9742958576244615252815311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12990611434992820337087081 9742958576244615252815311)
  ·
    refine ⟨14614437864366922879222967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9742958576244615252815311 14614437864366922879222967)
    ·
      refine ⟨21921656796550384318834451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14614437864366922879222967 21921656796550384318834451)
      ·
        refine ⟨32882485194825576478251677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21921656796550384318834451 32882485194825576478251677)
        ·
          refine ⟨12330931948059591179344379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32882485194825576478251677 12330931948059591179344379)
          ·
            refine ⟨18496397922089386769016569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12330931948059591179344379 18496397922089386769016569)
            ·
              refine ⟨13872298441567040076762427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18496397922089386769016569 13872298441567040076762427)
              ·
                refine ⟨20808447662350560115143641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13872298441567040076762427 20808447662350560115143641)
                ·
                  refine ⟨15606335746762920086357731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20808447662350560115143641 15606335746762920086357731)
                  ·
                    refine ⟨23409503620144380129536597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15606335746762920086357731 23409503620144380129536597)
                    ·
                      refine ⟨274330120548566954643007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 23409503620144380129536597 274330120548566954643007)
                      ·
                        rfl

theorem cell23_534256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_534256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534256 prefixEnd_534256 := by exact prefixLift 534256
  have htrace : WordTrace (prefixWord ++ tailWord_534256) baseStart_534256 baseEnd_534256 := by
    simpa [prefixWord, tailWord_534256, baseEnd_534256] using wordTrace_append hprefix tailTrace_534256
  have hstable : (prefixWord ++ tailWord_534256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534256).length < 2 ^ (prefixWord ++ tailWord_534256).sum := by decide
  have hdescent : baseEnd_534256 < baseStart_534256 := by decide
  rcases family_descends (prefixWord ++ tailWord_534256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534263 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 3]
def baseStart_534263 : Nat := 118140960795 + 534263 * 2 ^ 59
def prefixEnd_534263 : Nat := 4983230072969 + 3 ^ 40 * 534263 * 2
def baseEnd_534263 : Nat := 274333714913148427255475

theorem tailTrace_534263 : CollatzResearch.WordTrace tailWord_534263 prefixEnd_534263 274333714913148427255475 := by
  unfold tailWord_534263
  simp only [CollatzResearch.WordTrace]
  refine ⟨19486172463463870701135443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12990781642309247134090295 19486172463463870701135443)
  ·
    refine ⟨29229258695195806051703165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19486172463463870701135443 29229258695195806051703165)
    ·
      refine ⟨10960972010698427269388687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29229258695195806051703165 10960972010698427269388687)
      ·
        refine ⟨16441458016047640904083031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10960972010698427269388687 16441458016047640904083031)
        ·
          refine ⟨24662187024071461356124547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16441458016047640904083031 24662187024071461356124547)
          ·
            refine ⟨36993280536107192034186821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24662187024071461356124547 36993280536107192034186821)
            ·
              refine ⟨6936240100520098506410029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36993280536107192034186821 6936240100520098506410029)
              ·
                refine ⟨2601090037695036939903761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6936240100520098506410029 2601090037695036939903761)
                ·
                  refine ⟨1950817528271277704927821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2601090037695036939903761 1950817528271277704927821)
                  ·
                    refine ⟨731556573101729139347933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950817528271277704927821 731556573101729139347933)
                    ·
                      refine ⟨274333714913148427255475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 731556573101729139347933 274333714913148427255475)
                      ·
                        rfl

theorem cell23_534263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_534263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534263 prefixEnd_534263 := by exact prefixLift 534263
  have htrace : WordTrace (prefixWord ++ tailWord_534263) baseStart_534263 baseEnd_534263 := by
    simpa [prefixWord, tailWord_534263, baseEnd_534263] using wordTrace_append hprefix tailTrace_534263
  have hstable : (prefixWord ++ tailWord_534263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534263).length < 2 ^ (prefixWord ++ tailWord_534263).sum := by decide
  have hdescent : baseEnd_534263 < baseStart_534263 := by decide
  rcases family_descends (prefixWord ++ tailWord_534263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534283 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 2, 5]
def baseStart_534283 : Nat := 118140960795 + 534283 * 2 ^ 59
def prefixEnd_534283 : Nat := 4983230072969 + 3 ^ 40 * 534283 * 2
def baseEnd_534283 : Nat := 91447994842079449668461

theorem tailTrace_534283 : CollatzResearch.WordTrace tailWord_534283 prefixEnd_534283 91447994842079449668461 := by
  unfold tailWord_534283
  simp only [CollatzResearch.WordTrace]
  refine ⟨19486901923391414116863503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12991267948927609411242335 19486901923391414116863503)
  ·
    refine ⟨29230352885087121175295255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19486901923391414116863503 29230352885087121175295255)
    ·
      refine ⟨43845529327630681762942883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29230352885087121175295255 43845529327630681762942883)
      ·
        refine ⟨65768293991446022644414325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43845529327630681762942883 65768293991446022644414325)
        ·
          refine ⟨6165777561698064622913843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65768293991446022644414325 6165777561698064622913843)
          ·
            refine ⟨9248666342547096934370765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6165777561698064622913843 9248666342547096934370765)
            ·
              refine ⟨3468249878455161350389037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9248666342547096934370765 3468249878455161350389037)
              ·
                refine ⟨1300593704420685506395889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3468249878455161350389037 1300593704420685506395889)
                ·
                  refine ⟨975445278315514129796917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1300593704420685506395889 975445278315514129796917)
                  ·
                    refine ⟨91447994842079449668461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 975445278315514129796917 91447994842079449668461)
                    ·
                      rfl

theorem cell23_534283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 5].length) (baseStart_534283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534283 prefixEnd_534283 := by exact prefixLift 534283
  have htrace : WordTrace (prefixWord ++ tailWord_534283) baseStart_534283 baseEnd_534283 := by
    simpa [prefixWord, tailWord_534283, baseEnd_534283] using wordTrace_append hprefix tailTrace_534283
  have hstable : (prefixWord ++ tailWord_534283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534283).length < 2 ^ (prefixWord ++ tailWord_534283).sum := by decide
  have hdescent : baseEnd_534283 < baseStart_534283 := by decide
  rcases family_descends (prefixWord ++ tailWord_534283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534293 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_534293 : Nat := 118140960795 + 534293 * 2 ^ 59
def prefixEnd_534293 : Nat := 4983230072969 + 3 ^ 40 * 534293 * 2
def baseEnd_534293 : Nat := 274349119332783309880337

theorem tailTrace_534293 : CollatzResearch.WordTrace tailWord_534293 prefixEnd_534293 274349119332783309880337 := by
  unfold tailWord_534293
  simp only [CollatzResearch.WordTrace]
  refine ⟨19487266653355185824727533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12991511102236790549818355 19487266653355185824727533)
  ·
    refine ⟨7307724995008194684272825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19487266653355185824727533 7307724995008194684272825)
    ·
      refine ⟨5480793746256146013204619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7307724995008194684272825 5480793746256146013204619)
      ·
        refine ⟨8221190619384219019806929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5480793746256146013204619 8221190619384219019806929)
        ·
          refine ⟨6165892964538164264855197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8221190619384219019806929 6165892964538164264855197)
          ·
            refine ⟨2312209861701811599320699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6165892964538164264855197 2312209861701811599320699)
            ·
              refine ⟨3468314792552717398981049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312209861701811599320699 3468314792552717398981049)
              ·
                refine ⟨2601236094414538049235787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3468314792552717398981049 2601236094414538049235787)
                ·
                  refine ⟨3901854141621807073853681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2601236094414538049235787 3901854141621807073853681)
                  ·
                    refine ⟨2926390606216355305390261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3901854141621807073853681 2926390606216355305390261)
                    ·
                      refine ⟨274349119332783309880337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2926390606216355305390261 274349119332783309880337)
                      ·
                        rfl

theorem cell23_534293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_534293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534293 prefixEnd_534293 := by exact prefixLift 534293
  have htrace : WordTrace (prefixWord ++ tailWord_534293) baseStart_534293 baseEnd_534293 := by
    simpa [prefixWord, tailWord_534293, baseEnd_534293] using wordTrace_append hprefix tailTrace_534293
  have hstable : (prefixWord ++ tailWord_534293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534293).length < 2 ^ (prefixWord ++ tailWord_534293).sum := by decide
  have hdescent : baseEnd_534293 < baseStart_534293 := by decide
  rcases family_descends (prefixWord ++ tailWord_534293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534330 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_534330 : Nat := 118140960795 + 534330 * 2 ^ 59
def prefixEnd_534330 : Nat := 4983230072969 + 3 ^ 40 * 534330 * 2
def baseEnd_534330 : Nat := 91456039372333221705889

theorem tailTrace_534330 : CollatzResearch.WordTrace tailWord_534330 prefixEnd_534330 91456039372333221705889 := by
  unfold tailWord_534330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872154038555285285956111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12992410769480760762549629 4872154038555285285956111)
  ·
    refine ⟨7308231057832927928934167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4872154038555285285956111 7308231057832927928934167)
    ·
      refine ⟨10962346586749391893401251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7308231057832927928934167 10962346586749391893401251)
      ·
        refine ⟨16443519880124087840101877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10962346586749391893401251 16443519880124087840101877)
        ·
          refine ⟨1541579988761633235009551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16443519880124087840101877 1541579988761633235009551)
          ·
            refine ⟨2312369983142449852514327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541579988761633235009551 2312369983142449852514327)
            ·
              refine ⟨3468554974713674778771491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312369983142449852514327 3468554974713674778771491)
              ·
                refine ⟨5202832462070512168157237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3468554974713674778771491 5202832462070512168157237)
                ·
                  refine ⟨487765543319110515764741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5202832462070512168157237 487765543319110515764741)
                  ·
                    refine ⟨91456039372333221705889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487765543319110515764741 91456039372333221705889)
                    ·
                      rfl

theorem cell23_534330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_534330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534330 prefixEnd_534330 := by exact prefixLift 534330
  have htrace : WordTrace (prefixWord ++ tailWord_534330) baseStart_534330 baseEnd_534330 := by
    simpa [prefixWord, tailWord_534330, baseEnd_534330] using wordTrace_append hprefix tailTrace_534330
  have hstable : (prefixWord ++ tailWord_534330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534330).length < 2 ^ (prefixWord ++ tailWord_534330).sum := by decide
  have hdescent : baseEnd_534330 < baseStart_534330 := by decide
  rcases family_descends (prefixWord ++ tailWord_534330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534364 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_534364 : Nat := 118140960795 + 534364 * 2 ^ 59
def prefixEnd_534364 : Nat := 4983230072969 + 3 ^ 40 * 534364 * 2
def baseEnd_534364 : Nat := 91461858819750844030837

theorem tailTrace_534364 : CollatzResearch.WordTrace tailWord_534364 prefixEnd_534364 91461858819750844030837 := by
  unfold tailWord_534364
  simp only [CollatzResearch.WordTrace]
  refine ⟨9744928118048982475281073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12993237490731976633708097 9744928118048982475281073)
  ·
    refine ⟨7308696088536736856460805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9744928118048982475281073 7308696088536736856460805)
    ·
      refine ⟨1370380516600638160586401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7308696088536736856460805 1370380516600638160586401)
      ·
        refine ⟨1027785387450478620439801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1370380516600638160586401 1027785387450478620439801)
        ·
          refine ⟨770839040587858965329851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027785387450478620439801 770839040587858965329851)
          ·
            refine ⟨1156258560881788447994777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770839040587858965329851 1156258560881788447994777)
            ·
              refine ⟨867193920661341335996083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156258560881788447994777 867193920661341335996083)
              ·
                refine ⟨1300790880992012003994125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867193920661341335996083 1300790880992012003994125)
                ·
                  refine ⟨487796580372004501497797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1300790880992012003994125 487796580372004501497797)
                  ·
                    refine ⟨91461858819750844030837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487796580372004501497797 91461858819750844030837)
                    ·
                      rfl

theorem cell23_534364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_534364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534364 prefixEnd_534364 := by exact prefixLift 534364
  have htrace : WordTrace (prefixWord ++ tailWord_534364) baseStart_534364 baseEnd_534364 := by
    simpa [prefixWord, tailWord_534364, baseEnd_534364] using wordTrace_append hprefix tailTrace_534364
  have hstable : (prefixWord ++ tailWord_534364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534364).length < 2 ^ (prefixWord ++ tailWord_534364).sum := by decide
  have hdescent : baseEnd_534364 < baseStart_534364 := by decide
  rcases family_descends (prefixWord ++ tailWord_534364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534397 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 2, 3, 2]
def baseStart_534397 : Nat := 118140960795 + 534397 * 2 ^ 59
def prefixEnd_534397 : Nat := 4983230072969 + 3 ^ 40 * 534397 * 2
def baseEnd_534397 : Nat := 274402521320850902979859

theorem tailTrace_534397 : CollatzResearch.WordTrace tailWord_534397 prefixEnd_534397 274402521320850902979859 := by
  unfold tailWord_534397
  simp only [CollatzResearch.WordTrace]
  refine ⟨19491059844978411586513445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12994039896652274391008963 19491059844978411586513445)
  ·
    refine ⟨3654573720933452172471271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19491059844978411586513445 3654573720933452172471271)
    ·
      refine ⟨5481860581400178258706907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3654573720933452172471271 5481860581400178258706907)
      ·
        refine ⟨8222790872100267388060361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5481860581400178258706907 8222790872100267388060361)
        ·
          refine ⟨6167093154075200541045271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8222790872100267388060361 6167093154075200541045271)
          ·
            refine ⟨9250639731112800811567907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6167093154075200541045271 9250639731112800811567907)
            ·
              refine ⟨13875959596669201217351861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9250639731112800811567907 13875959596669201217351861)
              ·
                refine ⟨1300871212187737614126737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13875959596669201217351861 1300871212187737614126737)
                ·
                  refine ⟨975653409140803210595053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1300871212187737614126737 975653409140803210595053)
                  ·
                    refine ⟨365870028427801203973145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 975653409140803210595053 365870028427801203973145)
                    ·
                      refine ⟨274402521320850902979859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365870028427801203973145 274402521320850902979859)
                      ·
                        rfl

theorem cell23_534397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_534397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534397 prefixEnd_534397 := by exact prefixLift 534397
  have htrace : WordTrace (prefixWord ++ tailWord_534397) baseStart_534397 baseEnd_534397 := by
    simpa [prefixWord, tailWord_534397, baseEnd_534397] using wordTrace_append hprefix tailTrace_534397
  have hstable : (prefixWord ++ tailWord_534397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534397).length < 2 ^ (prefixWord ++ tailWord_534397).sum := by decide
  have hdescent : baseEnd_534397 < baseStart_534397 := by decide
  rcases family_descends (prefixWord ++ tailWord_534397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534398 : List Nat := [4, 2, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_534398 : Nat := 118140960795 + 534398 * 2 ^ 59
def prefixEnd_534398 : Nat := 4983230072969 + 3 ^ 40 * 534398 * 2
def baseEnd_534398 : Nat := 91467678267168466355785

theorem tailTrace_534398 : CollatzResearch.WordTrace tailWord_534398 prefixEnd_534398 91467678267168466355785 := by
  unfold tailWord_534398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2436387039746848594662481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12994064211983192504866565 2436387039746848594662481)
  ·
    refine ⟨1827290279810136445996861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2436387039746848594662481 1827290279810136445996861)
    ·
      refine ⟨685233854928801167248823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1827290279810136445996861 685233854928801167248823)
      ·
        refine ⟨1027850782393201750873235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685233854928801167248823 1027850782393201750873235)
        ·
          refine ⟨1541776173589802626309853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027850782393201750873235 1541776173589802626309853)
          ·
            refine ⟨578166065096175984866195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1541776173589802626309853 578166065096175984866195)
            ·
              refine ⟨867249097644263977299293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578166065096175984866195 867249097644263977299293)
              ·
                refine ⟨325218411616598991487235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 867249097644263977299293 325218411616598991487235)
                ·
                  refine ⟨487827617424898487230853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325218411616598991487235 487827617424898487230853)
                  ·
                    refine ⟨91467678267168466355785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487827617424898487230853 91467678267168466355785)
                    ·
                      rfl

theorem cell23_534398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_534398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534398 prefixEnd_534398 := by exact prefixLift 534398
  have htrace : WordTrace (prefixWord ++ tailWord_534398) baseStart_534398 baseEnd_534398 := by
    simpa [prefixWord, tailWord_534398, baseEnd_534398] using wordTrace_append hprefix tailTrace_534398
  have hstable : (prefixWord ++ tailWord_534398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534398).length < 2 ^ (prefixWord ++ tailWord_534398).sum := by decide
  have hdescent : baseEnd_534398 < baseStart_534398 := by decide
  rcases family_descends (prefixWord ++ tailWord_534398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534421 : List Nat := [1, 3, 2, 1, 1, 3, 5, 2, 1, 1, 3]
def baseStart_534421 : Nat := 118140960795 + 534421 * 2 ^ 59
def prefixEnd_534421 : Nat := 4983230072969 + 3 ^ 40 * 534421 * 2
def baseEnd_534421 : Nat := 274414844856558809079749

theorem tailTrace_534421 : CollatzResearch.WordTrace tailWord_534421 prefixEnd_534421 274414844856558809079749 := by
  unfold tailWord_534421
  simp only [CollatzResearch.WordTrace]
  refine ⟨19491935196891463685387117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12994623464594309123591411 19491935196891463685387117)
  ·
    refine ⟨7309475698834298882020169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19491935196891463685387117 7309475698834298882020169)
    ·
      refine ⟨5482106774125724161515127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7309475698834298882020169 5482106774125724161515127)
      ·
        refine ⟨8223160161188586242272691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5482106774125724161515127 8223160161188586242272691)
        ·
          refine ⟨12334740241782879363409037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8223160161188586242272691 12334740241782879363409037)
          ·
            refine ⟨4625527590668579761278389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12334740241782879363409037 4625527590668579761278389)
            ·
              refine ⟨433643211625179352619849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4625527590668579761278389 433643211625179352619849)
              ·
                refine ⟨325232408718884514464887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433643211625179352619849 325232408718884514464887)
                ·
                  refine ⟨487848613078326771697331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325232408718884514464887 487848613078326771697331)
                  ·
                    refine ⟨731772919617490157545997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 487848613078326771697331 731772919617490157545997)
                    ·
                      refine ⟨274414844856558809079749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 731772919617490157545997 274414844856558809079749)
                      ·
                        rfl

theorem cell23_534421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_534421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534421 prefixEnd_534421 := by exact prefixLift 534421
  have htrace : WordTrace (prefixWord ++ tailWord_534421) baseStart_534421 baseEnd_534421 := by
    simpa [prefixWord, tailWord_534421, baseEnd_534421] using wordTrace_append hprefix tailTrace_534421
  have hstable : (prefixWord ++ tailWord_534421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534421).length < 2 ^ (prefixWord ++ tailWord_534421).sum := by decide
  have hdescent : baseEnd_534421 < baseStart_534421 := by decide
  rcases family_descends (prefixWord ++ tailWord_534421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534464 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 1, 2, 3]
def baseStart_534464 : Nat := 118140960795 + 534464 * 2 ^ 59
def prefixEnd_534464 : Nat := 4983230072969 + 3 ^ 40 * 534464 * 2
def baseEnd_534464 : Nat := 274436924524702140842051

theorem tailTrace_534464 : CollatzResearch.WordTrace tailWord_534464 prefixEnd_534464 274436924524702140842051 := by
  unfold tailWord_534464
  simp only [CollatzResearch.WordTrace]
  refine ⟨9746751767867841014601223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12995669023823788019468297 9746751767867841014601223)
  ·
    refine ⟨14620127651801761521901835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9746751767867841014601223 14620127651801761521901835)
    ·
      refine ⟨21930191477702642282852753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14620127651801761521901835 21930191477702642282852753)
      ·
        refine ⟨16447643608276981712139565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21930191477702642282852753 16447643608276981712139565)
        ·
          refine ⟨6167866353103868142052337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16447643608276981712139565 6167866353103868142052337)
          ·
            refine ⟨4625899764827901106539253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6167866353103868142052337 4625899764827901106539253)
            ·
              refine ⟨433678102952615728738055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4625899764827901106539253 433678102952615728738055)
              ·
                refine ⟨650517154428923593107083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433678102952615728738055 650517154428923593107083)
                ·
                  refine ⟨975775731643385389660625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650517154428923593107083 975775731643385389660625)
                  ·
                    refine ⟨731831798732539042245469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 975775731643385389660625 731831798732539042245469)
                    ·
                      refine ⟨274436924524702140842051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 731831798732539042245469 274436924524702140842051)
                      ·
                        rfl

theorem cell23_534464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_534464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534464 prefixEnd_534464 := by exact prefixLift 534464
  have htrace : WordTrace (prefixWord ++ tailWord_534464) baseStart_534464 baseEnd_534464 := by
    simpa [prefixWord, tailWord_534464, baseEnd_534464] using wordTrace_append hprefix tailTrace_534464
  have hstable : (prefixWord ++ tailWord_534464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534464).length < 2 ^ (prefixWord ++ tailWord_534464).sum := by decide
  have hdescent : baseEnd_534464 < baseStart_534464 := by decide
  rcases family_descends (prefixWord ++ tailWord_534464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534487 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 5, 3, 2]
def baseStart_534487 : Nat := 118140960795 + 534487 * 2 ^ 59
def prefixEnd_534487 : Nat := 4983230072969 + 3 ^ 40 * 534487 * 2
def baseEnd_534487 : Nat := 274448734579755550854445

theorem tailTrace_534487 : CollatzResearch.WordTrace tailWord_534487 prefixEnd_534487 274448734579755550854445 := by
  unfold tailWord_534487
  simp only [CollatzResearch.WordTrace]
  refine ⟨19494342414652356957289715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12996228276434904638193143 19494342414652356957289715)
  ·
    refine ⟨29241513621978535435934573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19494342414652356957289715 29241513621978535435934573)
    ·
      refine ⟨10965567608241950788475465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29241513621978535435934573 10965567608241950788475465)
      ·
        refine ⟨8224175706181463091356599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10965567608241950788475465 8224175706181463091356599)
        ·
          refine ⟨12336263559272194637034899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8224175706181463091356599 12336263559272194637034899)
          ·
            refine ⟨18504395338908291955552349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12336263559272194637034899 18504395338908291955552349)
            ·
              refine ⟨6939148252090609483332131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18504395338908291955552349 6939148252090609483332131)
              ·
                refine ⟨10408722378135914224998197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6939148252090609483332131 10408722378135914224998197)
                ·
                  refine ⟨975817722950241958593581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10408722378135914224998197 975817722950241958593581)
                  ·
                    refine ⟨365931646106340734472593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 975817722950241958593581 365931646106340734472593)
                    ·
                      refine ⟨274448734579755550854445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365931646106340734472593 274448734579755550854445)
                      ·
                        rfl

theorem cell23_534487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_534487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534487 prefixEnd_534487 := by exact prefixLift 534487
  have htrace : WordTrace (prefixWord ++ tailWord_534487) baseStart_534487 baseEnd_534487 := by
    simpa [prefixWord, tailWord_534487, baseEnd_534487] using wordTrace_append hprefix tailTrace_534487
  have hstable : (prefixWord ++ tailWord_534487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534487).length < 2 ^ (prefixWord ++ tailWord_534487).sum := by decide
  have hdescent : baseEnd_534487 < baseStart_534487 := by decide
  rcases family_descends (prefixWord ++ tailWord_534487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534500 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_534500 : Nat := 118140960795 + 534500 * 2 ^ 59
def prefixEnd_534500 : Nat := 4983230072969 + 3 ^ 40 * 534500 * 2
def baseEnd_534500 : Nat := 274455409828263999991885

theorem tailTrace_534500 : CollatzResearch.WordTrace tailWord_534500 prefixEnd_534500 274455409828263999991885 := by
  unfold tailWord_534500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9747408281802630088756477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12996544375736840118341969 9747408281802630088756477)
  ·
    refine ⟨3655278105675986283283679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9747408281802630088756477 3655278105675986283283679)
    ·
      refine ⟨5482917158513979424925519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3655278105675986283283679 5482917158513979424925519)
      ·
        refine ⟨8224375737770969137388279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5482917158513979424925519 8224375737770969137388279)
        ·
          refine ⟨12336563606656453706082419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8224375737770969137388279 12336563606656453706082419)
          ·
            refine ⟨18504845409984680559123629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12336563606656453706082419 18504845409984680559123629)
            ·
              refine ⟨6939317028744255209671361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18504845409984680559123629 6939317028744255209671361)
              ·
                refine ⟨5204487771558191407253521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6939317028744255209671361 5204487771558191407253521)
                ·
                  refine ⟨3903365828668643555440141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5204487771558191407253521 3903365828668643555440141)
                  ·
                    refine ⟨1463762185750741333290053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3903365828668643555440141 1463762185750741333290053)
                    ·
                      refine ⟨274455409828263999991885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1463762185750741333290053 274455409828263999991885)
                      ·
                        rfl

theorem cell23_534500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_534500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534500 prefixEnd_534500 := by exact prefixLift 534500
  have htrace : WordTrace (prefixWord ++ tailWord_534500) baseStart_534500 baseEnd_534500 := by
    simpa [prefixWord, tailWord_534500, baseEnd_534500] using wordTrace_append hprefix tailTrace_534500
  have hstable : (prefixWord ++ tailWord_534500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534500).length < 2 ^ (prefixWord ++ tailWord_534500).sum := by decide
  have hdescent : baseEnd_534500 < baseStart_534500 := by decide
  rcases family_descends (prefixWord ++ tailWord_534500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534504 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_534504 : Nat := 118140960795 + 534504 * 2 ^ 59
def prefixEnd_534504 : Nat := 4983230072969 + 3 ^ 40 * 534504 * 2
def baseEnd_534504 : Nat := 274457463750881984341867

theorem tailTrace_534504 : CollatzResearch.WordTrace tailWord_534504 prefixEnd_534504 274457463750881984341867 := by
  unfold tailWord_534504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9747481227795384430329283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12996641637060512573772377 9747481227795384430329283)
  ·
    refine ⟨14621221841693076645493925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9747481227795384430329283 14621221841693076645493925)
    ·
      refine ⟨2741479095317451871030111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14621221841693076645493925 2741479095317451871030111)
      ·
        refine ⟨4112218642976177806545167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2741479095317451871030111 4112218642976177806545167)
        ·
          refine ⟨6168327964464266709817751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4112218642976177806545167 6168327964464266709817751)
          ·
            refine ⟨9252491946696400064726627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6168327964464266709817751 9252491946696400064726627)
            ·
              refine ⟨13878737920044600097089941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9252491946696400064726627 13878737920044600097089941)
              ·
                refine ⟨650565840002090629551091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13878737920044600097089941 650565840002090629551091)
                ·
                  refine ⟨975848760003135944326637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650565840002090629551091 975848760003135944326637)
                  ·
                    refine ⟨365943285001175979122489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 975848760003135944326637 365943285001175979122489)
                    ·
                      refine ⟨274457463750881984341867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365943285001175979122489 274457463750881984341867)
                      ·
                        rfl

theorem cell23_534504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_534504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534504 prefixEnd_534504 := by exact prefixLift 534504
  have htrace : WordTrace (prefixWord ++ tailWord_534504) baseStart_534504 baseEnd_534504 := by
    simpa [prefixWord, tailWord_534504, baseEnd_534504] using wordTrace_append hprefix tailTrace_534504
  have hstable : (prefixWord ++ tailWord_534504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534504).length < 2 ^ (prefixWord ++ tailWord_534504).sum := by decide
  have hdescent : baseEnd_534504 < baseStart_534504 := by decide
  rcases family_descends (prefixWord ++ tailWord_534504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534520 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_534520 : Nat := 118140960795 + 534520 * 2 ^ 59
def prefixEnd_534520 : Nat := 4983230072969 + 3 ^ 40 * 534520 * 2
def baseEnd_534520 : Nat := 274465679441353921741793

theorem tailTrace_534520 : CollatzResearch.WordTrace tailWord_534520 prefixEnd_534520 274465679441353921741793 := by
  unfold tailWord_534520
  simp only [CollatzResearch.WordTrace]
  refine ⟨9747773011766401796620507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12997030682355202395494009 9747773011766401796620507)
  ·
    refine ⟨14621659517649602694930761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9747773011766401796620507 14621659517649602694930761)
    ·
      refine ⟨10966244638237202021198071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14621659517649602694930761 10966244638237202021198071)
      ·
        refine ⟨16449366957355803031797107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10966244638237202021198071 16449366957355803031797107)
        ·
          refine ⟨24674050436033704547695661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16449366957355803031797107 24674050436033704547695661)
          ·
            refine ⟨9252768913512639205385873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24674050436033704547695661 9252768913512639205385873)
            ·
              refine ⟨6939576685134479404039405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9252768913512639205385873 6939576685134479404039405)
              ·
                refine ⟨2602341256925429776514777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6939576685134479404039405 2602341256925429776514777)
                ·
                  refine ⟨1951755942694072332386083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2602341256925429776514777 1951755942694072332386083)
                  ·
                    refine ⟨2927633914041108498579125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1951755942694072332386083 2927633914041108498579125)
                    ·
                      refine ⟨274465679441353921741793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2927633914041108498579125 274465679441353921741793)
                      ·
                        rfl

theorem cell23_534520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_534520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534520 prefixEnd_534520 := by exact prefixLift 534520
  have htrace : WordTrace (prefixWord ++ tailWord_534520) baseStart_534520 baseEnd_534520 := by
    simpa [prefixWord, tailWord_534520, baseEnd_534520] using wordTrace_append hprefix tailTrace_534520
  have hstable : (prefixWord ++ tailWord_534520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534520).length < 2 ^ (prefixWord ++ tailWord_534520).sum := by decide
  have hdescent : baseEnd_534520 < baseStart_534520 := by decide
  rcases family_descends (prefixWord ++ tailWord_534520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534521 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 1, 3, 2]
def baseStart_534521 : Nat := 118140960795 + 534521 * 2 ^ 59
def prefixEnd_534521 : Nat := 4983230072969 + 3 ^ 40 * 534521 * 2
def baseEnd_534521 : Nat := 274466192922008417829289

theorem tailTrace_534521 : CollatzResearch.WordTrace tailWord_534521 prefixEnd_534521 274466192922008417829289 := by
  unfold tailWord_534521
  simp only [CollatzResearch.WordTrace]
  refine ⟨19495582496529180764027417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12997054997686120509351611 19495582496529180764027417)
  ·
    refine ⟨14621686872396885573020563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19495582496529180764027417 14621686872396885573020563)
    ·
      refine ⟨21932530308595328359530845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14621686872396885573020563 21932530308595328359530845)
      ·
        refine ⟨8224698865723248134824067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21932530308595328359530845 8224698865723248134824067)
        ·
          refine ⟨12337048298584872202236101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8224698865723248134824067 12337048298584872202236101)
          ·
            refine ⟨2313196555984663537919269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12337048298584872202236101 2313196555984663537919269)
            ·
              refine ⟨433724354247124413359863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2313196555984663537919269 433724354247124413359863)
              ·
                refine ⟨650586531370686620039795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433724354247124413359863 650586531370686620039795)
                ·
                  refine ⟨975879797056029930059693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650586531370686620039795 975879797056029930059693)
                  ·
                    refine ⟨365954923896011223772385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 975879797056029930059693 365954923896011223772385)
                    ·
                      refine ⟨274466192922008417829289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365954923896011223772385 274466192922008417829289)
                      ·
                        rfl

theorem cell23_534521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_534521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534521 prefixEnd_534521 := by exact prefixLift 534521
  have htrace : WordTrace (prefixWord ++ tailWord_534521) baseStart_534521 baseEnd_534521 := by
    simpa [prefixWord, tailWord_534521, baseEnd_534521] using wordTrace_append hprefix tailTrace_534521
  have hstable : (prefixWord ++ tailWord_534521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534521).length < 2 ^ (prefixWord ++ tailWord_534521).sum := by decide
  have hdescent : baseEnd_534521 < baseStart_534521 := by decide
  rcases family_descends (prefixWord ++ tailWord_534521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534557 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 7]
def baseStart_534557 : Nat := 118140960795 + 534557 * 2 ^ 59
def prefixEnd_534557 : Nat := 4983230072969 + 3 ^ 40 * 534557 * 2
def baseEnd_534557 : Nat := 30498297580618919664347

theorem tailTrace_534557 : CollatzResearch.WordTrace tailWord_534557 prefixEnd_534557 30498297580618919664347 := by
  unfold tailWord_534557
  simp only [CollatzResearch.WordTrace]
  refine ⟨19496895524398758912337925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12997930349599172608225283 19496895524398758912337925)
  ·
    refine ⟨3655667910824767296063361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19496895524398758912337925 3655667910824767296063361)
    ·
      refine ⟨2741750933118575472047521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3655667910824767296063361 2741750933118575472047521)
      ·
        refine ⟨2056313199838931604035641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2741750933118575472047521 2056313199838931604035641)
        ·
          refine ⟨1542234899879198703026731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2056313199838931604035641 1542234899879198703026731)
          ·
            refine ⟨2313352349818798054540097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542234899879198703026731 2313352349818798054540097)
            ·
              refine ⟨1735014262364098540905073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2313352349818798054540097 1735014262364098540905073)
              ·
                refine ⟨1301260696773073905678805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735014262364098540905073 1301260696773073905678805)
                ·
                  refine ⟨30498297580618919664347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1301260696773073905678805 30498297580618919664347)
                  ·
                    rfl

theorem cell23_534557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_534557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534557 prefixEnd_534557 := by exact prefixLift 534557
  have htrace : WordTrace (prefixWord ++ tailWord_534557) baseStart_534557 baseEnd_534557 := by
    simpa [prefixWord, tailWord_534557, baseEnd_534557] using wordTrace_append hprefix tailTrace_534557
  have hstable : (prefixWord ++ tailWord_534557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534557).length < 2 ^ (prefixWord ++ tailWord_534557).sum := by decide
  have hdescent : baseEnd_534557 < baseStart_534557 := by decide
  rcases family_descends (prefixWord ++ tailWord_534557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534600 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 2, 8]
def baseStart_534600 : Nat := 118140960795 + 534600 * 2 ^ 59
def prefixEnd_534600 : Nat := 4983230072969 + 3 ^ 40 * 534600 * 2
def baseEnd_534600 : Nat := 91502252631237869580475

theorem tailTrace_534600 : CollatzResearch.WordTrace tailWord_534600 prefixEnd_534600 91502252631237869580475 := by
  unfold tailWord_534600
  simp only [CollatzResearch.WordTrace]
  refine ⟨9749231931621488628076627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12998975908828651504102169 9749231931621488628076627)
  ·
    refine ⟨14623847897432232942114941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9749231931621488628076627 14623847897432232942114941)
    ·
      refine ⟨5483942961537087353293103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14623847897432232942114941 5483942961537087353293103)
      ·
        refine ⟨8225914442305631029939655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5483942961537087353293103 8225914442305631029939655)
        ·
          refine ⟨12338871663458446544909483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8225914442305631029939655 12338871663458446544909483)
          ·
            refine ⟨18508307495187669817364225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12338871663458446544909483 18508307495187669817364225)
            ·
              refine ⟨13881230621390752363023169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18508307495187669817364225 13881230621390752363023169)
              ·
                refine ⟨10410922966043064272267377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13881230621390752363023169 10410922966043064272267377)
                ·
                  refine ⟨7808192224532298204200533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10410922966043064272267377 7808192224532298204200533)
                  ·
                    refine ⟨91502252631237869580475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7808192224532298204200533 91502252631237869580475)
                    ·
                      rfl

theorem cell23_534600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_534600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534600 prefixEnd_534600 := by exact prefixLift 534600
  have htrace : WordTrace (prefixWord ++ tailWord_534600) baseStart_534600 baseEnd_534600 := by
    simpa [prefixWord, tailWord_534600, baseEnd_534600] using wordTrace_append hprefix tailTrace_534600
  have hstable : (prefixWord ++ tailWord_534600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534600).length < 2 ^ (prefixWord ++ tailWord_534600).sum := by decide
  have hdescent : baseEnd_534600 < baseStart_534600 := by decide
  rcases family_descends (prefixWord ++ tailWord_534600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534617 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 5, 4]
def baseStart_534617 : Nat := 118140960795 + 534617 * 2 ^ 59
def prefixEnd_534617 : Nat := 4983230072969 + 3 ^ 40 * 534617 * 2
def baseEnd_534617 : Nat := 91505162354946680742949

theorem tailTrace_534617 : CollatzResearch.WordTrace tailWord_534617 prefixEnd_534617 91505162354946680742949 := by
  unfold tailWord_534617
  simp only [CollatzResearch.WordTrace]
  refine ⟨19499083904181389159522105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12999389269454259439681403 19499083904181389159522105)
  ·
    refine ⟨14624312928136041869641579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19499083904181389159522105 14624312928136041869641579)
    ·
      refine ⟨21936469392204062804462369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14624312928136041869641579 21936469392204062804462369)
      ·
        refine ⟨16452352044153047103346777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21936469392204062804462369 16452352044153047103346777)
        ·
          refine ⟨12339264033114785327510083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16452352044153047103346777 12339264033114785327510083)
          ·
            refine ⟨18508896049672177991265125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12339264033114785327510083 18508896049672177991265125)
            ·
              refine ⟨3470418009313533373362211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18508896049672177991265125 3470418009313533373362211)
              ·
                refine ⟨5205627013970300060043317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470418009313533373362211 5205627013970300060043317)
                ·
                  refine ⟨488027532559715630629061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5205627013970300060043317 488027532559715630629061)
                  ·
                    refine ⟨91505162354946680742949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 488027532559715630629061 91505162354946680742949)
                    ·
                      rfl

theorem cell23_534617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 4].length) (baseStart_534617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534617 prefixEnd_534617 := by exact prefixLift 534617
  have htrace : WordTrace (prefixWord ++ tailWord_534617) baseStart_534617 baseEnd_534617 := by
    simpa [prefixWord, tailWord_534617, baseEnd_534617] using wordTrace_append hprefix tailTrace_534617
  have hstable : (prefixWord ++ tailWord_534617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534617).length < 2 ^ (prefixWord ++ tailWord_534617).sum := by decide
  have hdescent : baseEnd_534617 < baseStart_534617 := by decide
  rcases family_descends (prefixWord ++ tailWord_534617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534621 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_534621 : Nat := 118140960795 + 534621 * 2 ^ 59
def prefixEnd_534621 : Nat := 4983230072969 + 3 ^ 40 * 534621 * 2
def baseEnd_534621 : Nat := 91505846995819342192943

theorem tailTrace_534621 : CollatzResearch.WordTrace tailWord_534621 prefixEnd_534621 91505846995819342192943 := by
  unfold tailWord_534621
  simp only [CollatzResearch.WordTrace]
  refine ⟨19499229796166897842667717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12999486530777931895111811 19499229796166897842667717)
  ·
    refine ⟨3656105586781293345500197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19499229796166897842667717 3656105586781293345500197)
    ·
      refine ⟨685519797521492502281287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3656105586781293345500197 685519797521492502281287)
      ·
        refine ⟨1028279696282238753421931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685519797521492502281287 1028279696282238753421931)
        ·
          refine ⟨1542419544423358130132897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028279696282238753421931 1542419544423358130132897)
          ·
            refine ⟨1156814658317518597599673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1542419544423358130132897 1156814658317518597599673)
            ·
              refine ⟨867610993738138948199755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156814658317518597599673 867610993738138948199755)
              ·
                refine ⟨1301416490607208422299633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867610993738138948199755 1301416490607208422299633)
                ·
                  refine ⟨976062367955406316724725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1301416490607208422299633 976062367955406316724725)
                  ·
                    refine ⟨91505846995819342192943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 976062367955406316724725 91505846995819342192943)
                    ·
                      rfl

theorem cell23_534621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_534621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534621 prefixEnd_534621 := by exact prefixLift 534621
  have htrace : WordTrace (prefixWord ++ tailWord_534621) baseStart_534621 baseEnd_534621 := by
    simpa [prefixWord, tailWord_534621, baseEnd_534621] using wordTrace_append hprefix tailTrace_534621
  have hstable : (prefixWord ++ tailWord_534621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534621).length < 2 ^ (prefixWord ++ tailWord_534621).sum := by decide
  have hdescent : baseEnd_534621 < baseStart_534621 := by decide
  rcases family_descends (prefixWord ++ tailWord_534621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534624 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 4]
def baseStart_534624 : Nat := 118140960795 + 534624 * 2 ^ 59
def prefixEnd_534624 : Nat := 4983230072969 + 3 ^ 40 * 534624 * 2
def baseEnd_534624 : Nat := 274519081429421514841315

theorem tailTrace_534624 : CollatzResearch.WordTrace tailWord_534624 prefixEnd_534624 274519081429421514841315 := by
  unfold tailWord_534624
  simp only [CollatzResearch.WordTrace]
  refine ⟨9749669607578014677513463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12999559476770686236684617 9749669607578014677513463)
  ·
    refine ⟨14624504411367022016270195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9749669607578014677513463 14624504411367022016270195)
    ·
      refine ⟨21936756617050533024405293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14624504411367022016270195 21936756617050533024405293)
      ·
        refine ⟨8226283731393949884151985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21936756617050533024405293 8226283731393949884151985)
        ·
          refine ⟨6169712798545462413113989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8226283731393949884151985 6169712798545462413113989)
          ·
            refine ⟨1156821149727274202458873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6169712798545462413113989 1156821149727274202458873)
            ·
              refine ⟨867615862295455651844155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156821149727274202458873 867615862295455651844155)
              ·
                refine ⟨1301423793443183477766233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867615862295455651844155 1301423793443183477766233)
                ·
                  refine ⟨976067845082387608324675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1301423793443183477766233 976067845082387608324675)
                  ·
                    refine ⟨1464101767623581412487013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 976067845082387608324675 1464101767623581412487013)
                    ·
                      refine ⟨274519081429421514841315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1464101767623581412487013 274519081429421514841315)
                      ·
                        rfl

theorem cell23_534624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_534624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534624 prefixEnd_534624 := by exact prefixLift 534624
  have htrace : WordTrace (prefixWord ++ tailWord_534624) baseStart_534624 baseEnd_534624 := by
    simpa [prefixWord, tailWord_534624, baseEnd_534624] using wordTrace_append hprefix tailTrace_534624
  have hstable : (prefixWord ++ tailWord_534624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534624).length < 2 ^ (prefixWord ++ tailWord_534624).sum := by decide
  have hdescent : baseEnd_534624 < baseStart_534624 := by decide
  rcases family_descends (prefixWord ++ tailWord_534624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534627 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 3]
def baseStart_534627 : Nat := 118140960795 + 534627 * 2 ^ 59
def prefixEnd_534627 : Nat := 4983230072969 + 3 ^ 40 * 534627 * 2
def baseEnd_534627 : Nat := 274520621871385003103801

theorem tailTrace_534627 : CollatzResearch.WordTrace tailWord_534627 prefixEnd_534627 274520621871385003103801 := by
  unfold tailWord_534627
  simp only [CollatzResearch.WordTrace]
  refine ⟨19499448634145160867386135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12999632422763440578257423 19499448634145160867386135)
  ·
    refine ⟨29249172951217741301079203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19499448634145160867386135 29249172951217741301079203)
    ·
      refine ⟨43873759426826611951618805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29249172951217741301079203 43873759426826611951618805)
      ·
        refine ⟨4113164946264994870464263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43873759426826611951618805 4113164946264994870464263)
        ·
          refine ⟨6169747419397492305696395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113164946264994870464263 6169747419397492305696395)
          ·
            refine ⟨9254621129096238458544593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6169747419397492305696395 9254621129096238458544593)
            ·
              refine ⟨6940965846822178843908445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9254621129096238458544593 6940965846822178843908445)
              ·
                refine ⟨2602862192558317066465667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6940965846822178843908445 2602862192558317066465667)
                ·
                  refine ⟨3904293288837475599698501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2602862192558317066465667 3904293288837475599698501)
                  ·
                    refine ⟨732054991657026674943469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3904293288837475599698501 732054991657026674943469)
                    ·
                      refine ⟨274520621871385003103801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 732054991657026674943469 274520621871385003103801)
                      ·
                        rfl

theorem cell23_534627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_534627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534627 prefixEnd_534627 := by exact prefixLift 534627
  have htrace : WordTrace (prefixWord ++ tailWord_534627) baseStart_534627 baseEnd_534627 := by
    simpa [prefixWord, tailWord_534627, baseEnd_534627] using wordTrace_append hprefix tailTrace_534627
  have hstable : (prefixWord ++ tailWord_534627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534627).length < 2 ^ (prefixWord ++ tailWord_534627).sum := by decide
  have hdescent : baseEnd_534627 < baseStart_534627 := by decide
  rcases family_descends (prefixWord ++ tailWord_534627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534637 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_534637 : Nat := 118140960795 + 534637 * 2 ^ 59
def prefixEnd_534637 : Nat := 4983230072969 + 3 ^ 40 * 534637 * 2
def baseEnd_534637 : Nat := 274525756677929963978755

theorem tailTrace_534637 : CollatzResearch.WordTrace tailWord_534637 prefixEnd_534637 274525756677929963978755 := by
  unfold tailWord_534637
  simp only [CollatzResearch.WordTrace]
  refine ⟨19499813364108932575250165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12999875576072621716833443 19499813364108932575250165)
  ·
    refine ⟨1828107502885212428929703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19499813364108932575250165 1828107502885212428929703)
    ·
      refine ⟨2742161254327818643394555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1828107502885212428929703 2742161254327818643394555)
      ·
        refine ⟨4113241881491727965091833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742161254327818643394555 4113241881491727965091833)
        ·
          refine ⟨3084931411118795973818875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4113241881491727965091833 3084931411118795973818875)
          ·
            refine ⟨4627397116678193960728313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3084931411118795973818875 4627397116678193960728313)
            ·
              refine ⟨3470547837508645470546235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4627397116678193960728313 3470547837508645470546235)
              ·
                refine ⟨5205821756262968205819353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470547837508645470546235 5205821756262968205819353)
                ·
                  refine ⟨3904366317197226154364515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5205821756262968205819353 3904366317197226154364515)
                  ·
                    refine ⟨5856549475795839231546773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3904366317197226154364515 5856549475795839231546773)
                    ·
                      refine ⟨274525756677929963978755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5856549475795839231546773 274525756677929963978755)
                      ·
                        rfl

theorem cell23_534637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_534637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534637 prefixEnd_534637 := by exact prefixLift 534637
  have htrace : WordTrace (prefixWord ++ tailWord_534637) baseStart_534637 baseEnd_534637 := by
    simpa [prefixWord, tailWord_534637, baseEnd_534637] using wordTrace_append hprefix tailTrace_534637
  have hstable : (prefixWord ++ tailWord_534637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534637).length < 2 ^ (prefixWord ++ tailWord_534637).sum := by decide
  have hdescent : baseEnd_534637 < baseStart_534637 := by decide
  rcases family_descends (prefixWord ++ tailWord_534637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534647 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 6]
def baseStart_534647 : Nat := 118140960795 + 534647 * 2 ^ 59
def prefixEnd_534647 : Nat := 4983230072969 + 3 ^ 40 * 534647 * 2
def baseEnd_534647 : Nat := 30503432387163880539301

theorem tailTrace_534647 : CollatzResearch.WordTrace tailWord_534647 prefixEnd_534647 30503432387163880539301 := by
  unfold tailWord_534647
  simp only [CollatzResearch.WordTrace]
  refine ⟨19500178094072704283114195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13000118729381802855409463 19500178094072704283114195)
  ·
    refine ⟨29250267141109056424671293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19500178094072704283114195 29250267141109056424671293)
    ·
      refine ⟨10968850177915896159251735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29250267141109056424671293 10968850177915896159251735)
      ·
        refine ⟨16453275266873844238877603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10968850177915896159251735 16453275266873844238877603)
        ·
          refine ⟨24679912900310766358316405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16453275266873844238877603 24679912900310766358316405)
          ·
            refine ⟨2313741834404134346092163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24679912900310766358316405 2313741834404134346092163)
            ·
              refine ⟨3470612751606201519138245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313741834404134346092163 3470612751606201519138245)
              ·
                refine ⟨650739890926162784838421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3470612751606201519138245 650739890926162784838421)
                ·
                  refine ⟨30503432387163880539301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 650739890926162784838421 30503432387163880539301)
                  ·
                    rfl

theorem cell23_534647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 6].length) (baseStart_534647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534647 prefixEnd_534647 := by exact prefixLift 534647
  have htrace : WordTrace (prefixWord ++ tailWord_534647) baseStart_534647 baseEnd_534647 := by
    simpa [prefixWord, tailWord_534647, baseEnd_534647] using wordTrace_append hprefix tailTrace_534647
  have hstable : (prefixWord ++ tailWord_534647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534647).length < 2 ^ (prefixWord ++ tailWord_534647).sum := by decide
  have hdescent : baseEnd_534647 < baseStart_534647 := by decide
  rcases family_descends (prefixWord ++ tailWord_534647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534664 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 6]
def baseStart_534664 : Nat := 118140960795 + 534664 * 2 ^ 59
def prefixEnd_534664 : Nat := 4983230072969 + 3 ^ 40 * 534664 * 2
def baseEnd_534664 : Nat := 30504402295066817593459

theorem tailTrace_534664 : CollatzResearch.WordTrace tailWord_534664 prefixEnd_534664 30504402295066817593459 := by
  unfold tailWord_534664
  simp only [CollatzResearch.WordTrace]
  refine ⟨9750399067505558093241523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13000532090007410790988697 9750399067505558093241523)
  ·
    refine ⟨14625598601258337139862285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9750399067505558093241523 14625598601258337139862285)
    ·
      refine ⟨5484599475471876427448357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14625598601258337139862285 5484599475471876427448357)
      ·
        refine ⟨1028362401650976830146567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5484599475471876427448357 1028362401650976830146567)
        ·
          refine ⟨1542543602476465245219851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028362401650976830146567 1542543602476465245219851)
          ·
            refine ⟨2313815403714697867829777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542543602476465245219851 2313815403714697867829777)
            ·
              refine ⟨1735361552786023400872333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2313815403714697867829777 1735361552786023400872333)
              ·
                refine ⟨650760582294758775327125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1735361552786023400872333 650760582294758775327125)
                ·
                  refine ⟨30504402295066817593459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 650760582294758775327125 30504402295066817593459)
                  ·
                    rfl

theorem cell23_534664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 6].length) (baseStart_534664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534664 prefixEnd_534664 := by exact prefixLift 534664
  have htrace : WordTrace (prefixWord ++ tailWord_534664) baseStart_534664 baseEnd_534664 := by
    simpa [prefixWord, tailWord_534664, baseEnd_534664] using wordTrace_append hprefix tailTrace_534664
  have hstable : (prefixWord ++ tailWord_534664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534664).length < 2 ^ (prefixWord ++ tailWord_534664).sum := by decide
  have hdescent : baseEnd_534664 < baseStart_534664 := by decide
  rcases family_descends (prefixWord ++ tailWord_534664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534677 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_534677 : Nat := 118140960795 + 534677 * 2 ^ 59
def prefixEnd_534677 : Nat := 4983230072969 + 3 ^ 40 * 534677 * 2
def baseEnd_534677 : Nat := 91515431968036602492857

theorem tailTrace_534677 : CollatzResearch.WordTrace tailWord_534677 prefixEnd_534677 91515431968036602492857 := by
  unfold tailWord_534677
  simp only [CollatzResearch.WordTrace]
  refine ⟨19501272283964019406706285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13000848189309346271137523 19501272283964019406706285)
  ·
    refine ⟨7312977106486507277514857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19501272283964019406706285 7312977106486507277514857)
    ·
      refine ⟨5484732829864880458136143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7312977106486507277514857 5484732829864880458136143)
      ·
        refine ⟨8227099244797320687204215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5484732829864880458136143 8227099244797320687204215)
        ·
          refine ⟨12340648867195981030806323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8227099244797320687204215 12340648867195981030806323)
          ·
            refine ⟨18510973300793971546209485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12340648867195981030806323 18510973300793971546209485)
            ·
              refine ⟨6941614987797739329828557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18510973300793971546209485 6941614987797739329828557)
              ·
                refine ⟨2603105620424152248685709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6941614987797739329828557 2603105620424152248685709)
                ·
                  refine ⟨976164607659057093257141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2603105620424152248685709 976164607659057093257141)
                  ·
                    refine ⟨91515431968036602492857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 976164607659057093257141 91515431968036602492857)
                    ·
                      rfl

theorem cell23_534677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_534677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534677 prefixEnd_534677 := by exact prefixLift 534677
  have htrace : WordTrace (prefixWord ++ tailWord_534677) baseStart_534677 baseEnd_534677 := by
    simpa [prefixWord, tailWord_534677, baseEnd_534677] using wordTrace_append hprefix tailTrace_534677
  have hstable : (prefixWord ++ tailWord_534677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534677).length < 2 ^ (prefixWord ++ tailWord_534677).sum := by decide
  have hdescent : baseEnd_534677 < baseStart_534677 := by decide
  rcases family_descends (prefixWord ++ tailWord_534677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534698 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 6]
def baseStart_534698 : Nat := 118140960795 + 534698 * 2 ^ 59
def prefixEnd_534698 : Nat := 4983230072969 + 3 ^ 40 * 534698 * 2
def baseEnd_534698 : Nat := 30506342110872691701775

theorem tailTrace_534698 : CollatzResearch.WordTrace tailWord_534698 prefixEnd_534698 30506342110872691701775 := by
  unfold tailWord_534698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4875509554221984998305187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13001358811258626662147165 4875509554221984998305187)
  ·
    refine ⟨7313264331332977497457781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4875509554221984998305187 7313264331332977497457781)
    ·
      refine ⟨685618531062466640386667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7313264331332977497457781 685618531062466640386667)
      ·
        refine ⟨1028427796593699960580001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685618531062466640386667 1028427796593699960580001)
        ·
          refine ⟨771320847445274970435001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1028427796593699960580001 771320847445274970435001)
          ·
            refine ⟨578490635583956227826251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771320847445274970435001 578490635583956227826251)
            ·
              refine ⟨867735953375934341739377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578490635583956227826251 867735953375934341739377)
              ·
                refine ⟨650801965031950756304533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 867735953375934341739377 650801965031950756304533)
                ·
                  refine ⟨30506342110872691701775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 650801965031950756304533 30506342110872691701775)
                  ·
                    rfl

theorem cell23_534698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_534698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534698 prefixEnd_534698 := by exact prefixLift 534698
  have htrace : WordTrace (prefixWord ++ tailWord_534698) baseStart_534698 baseEnd_534698 := by
    simpa [prefixWord, tailWord_534698, baseEnd_534698] using wordTrace_append hprefix tailTrace_534698
  have hstable : (prefixWord ++ tailWord_534698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534698).length < 2 ^ (prefixWord ++ tailWord_534698).sum := by decide
  have hdescent : baseEnd_534698 < baseStart_534698 := by decide
  rcases family_descends (prefixWord ++ tailWord_534698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534731 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 3, 2, 2]
def baseStart_534731 : Nat := 118140960795 + 534731 * 2 ^ 59
def prefixEnd_534731 : Nat := 4983230072969 + 3 ^ 40 * 534731 * 2
def baseEnd_534731 : Nat := 274574023859452596203323

theorem tailTrace_534731 : CollatzResearch.WordTrace tailWord_534731 prefixEnd_534731 274574023859452596203323 := by
  unfold tailWord_534731
  simp only [CollatzResearch.WordTrace]
  refine ⟨19503241825768386629172047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13002161217178924419448031 19503241825768386629172047)
  ·
    refine ⟨29254862738652579943758071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19503241825768386629172047 29254862738652579943758071)
    ·
      refine ⟨43882294107978869915637107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29254862738652579943758071 43882294107978869915637107)
      ·
        refine ⟨65823441161968304873455661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43882294107978869915637107 65823441161968304873455661)
        ·
          refine ⟨24683790435738114327545873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65823441161968304873455661 24683790435738114327545873)
          ·
            refine ⟨18512842826803585745659405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24683790435738114327545873 18512842826803585745659405)
            ·
              refine ⟨6942316060051344654622277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18512842826803585745659405 6942316060051344654622277)
              ·
                refine ⟨1301684261259627122741677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6942316060051344654622277 1301684261259627122741677)
                ·
                  refine ⟨488131597972360171028129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1301684261259627122741677 488131597972360171028129)
                  ·
                    refine ⟨366098698479270128271097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 488131597972360171028129 366098698479270128271097)
                    ·
                      refine ⟨274574023859452596203323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366098698479270128271097 274574023859452596203323)
                      ·
                        rfl

theorem cell23_534731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 2, 2].length) (baseStart_534731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534731 prefixEnd_534731 := by exact prefixLift 534731
  have htrace : WordTrace (prefixWord ++ tailWord_534731) baseStart_534731 baseEnd_534731 := by
    simpa [prefixWord, tailWord_534731, baseEnd_534731] using wordTrace_append hprefix tailTrace_534731
  have hstable : (prefixWord ++ tailWord_534731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534731).length < 2 ^ (prefixWord ++ tailWord_534731).sum := by decide
  have hdescent : baseEnd_534731 < baseStart_534731 := by decide
  rcases family_descends (prefixWord ++ tailWord_534731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534742 : List Nat := [5, 2, 1, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_534742 : Nat := 118140960795 + 534742 * 2 ^ 59
def prefixEnd_534742 : Nat := 4983230072969 + 3 ^ 40 * 534742 * 2
def baseEnd_534742 : Nat := 274579672146652053165773

theorem tailTrace_534742 : CollatzResearch.WordTrace tailWord_534742 prefixEnd_534742 274579672146652053165773 := by
  unfold tailWord_534742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1218977689295533469238905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13002428685819023671881653 1218977689295533469238905)
  ·
    refine ⟨914233266971650101929179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1218977689295533469238905 914233266971650101929179)
    ·
      refine ⟨1371349900457475152893769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914233266971650101929179 1371349900457475152893769)
      ·
        refine ⟨1028512425343106364670327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1371349900457475152893769 1028512425343106364670327)
        ·
          refine ⟨1542768638014659547005491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028512425343106364670327 1542768638014659547005491)
          ·
            refine ⟨2314152957021989320508237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542768638014659547005491 2314152957021989320508237)
            ·
              refine ⟨867807358883245995190589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2314152957021989320508237 867807358883245995190589)
              ·
                refine ⟨325427759581217248196471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 867807358883245995190589 325427759581217248196471)
                ·
                  refine ⟨488141639371825872294707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325427759581217248196471 488141639371825872294707)
                  ·
                    refine ⟨732212459057738808442061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 488141639371825872294707 732212459057738808442061)
                    ·
                      refine ⟨274579672146652053165773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 732212459057738808442061 274579672146652053165773)
                      ·
                        rfl

theorem cell23_534742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_534742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534742 prefixEnd_534742 := by exact prefixLift 534742
  have htrace : WordTrace (prefixWord ++ tailWord_534742) baseStart_534742 baseEnd_534742 := by
    simpa [prefixWord, tailWord_534742, baseEnd_534742] using wordTrace_append hprefix tailTrace_534742
  have hstable : (prefixWord ++ tailWord_534742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534742).length < 2 ^ (prefixWord ++ tailWord_534742).sum := by decide
  have hdescent : baseEnd_534742 < baseStart_534742 := by decide
  rcases family_descends (prefixWord ++ tailWord_534742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534777 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_534777 : Nat := 118140960795 + 534777 * 2 ^ 59
def prefixEnd_534777 : Nat := 4983230072969 + 3 ^ 40 * 534777 * 2
def baseEnd_534777 : Nat := 274597643969559416228111

theorem tailTrace_534777 : CollatzResearch.WordTrace tailWord_534777 prefixEnd_534777 274597643969559416228111 := by
  unfold tailWord_534777
  simp only [CollatzResearch.WordTrace]
  refine ⟨19504919583601736485346585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13003279722401157656897723 19504919583601736485346585)
  ·
    refine ⟨14628689687701302364009939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19504919583601736485346585 14628689687701302364009939)
    ·
      refine ⟨21943034531551953546014909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14628689687701302364009939 21943034531551953546014909)
      ·
        refine ⟨8228637949331982579755591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21943034531551953546014909 8228637949331982579755591)
        ·
          refine ⟨12342956923997973869633387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8228637949331982579755591 12342956923997973869633387)
          ·
            refine ⟨18514435385996960804450081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12342956923997973869633387 18514435385996960804450081)
            ·
              refine ⟨13885826539497720603337561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18514435385996960804450081 13885826539497720603337561)
              ·
                refine ⟨10414369904623290452503171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13885826539497720603337561 10414369904623290452503171)
                ·
                  refine ⟨15621554856934935678754757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10414369904623290452503171 15621554856934935678754757)
                  ·
                    refine ⟨2929041535675300439766517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15621554856934935678754757 2929041535675300439766517)
                    ·
                      refine ⟨274597643969559416228111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2929041535675300439766517 274597643969559416228111)
                      ·
                        rfl

theorem cell23_534777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_534777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534777 prefixEnd_534777 := by exact prefixLift 534777
  have htrace : WordTrace (prefixWord ++ tailWord_534777) baseStart_534777 baseEnd_534777 := by
    simpa [prefixWord, tailWord_534777, baseEnd_534777] using wordTrace_append hprefix tailTrace_534777
  have hstable : (prefixWord ++ tailWord_534777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534777).length < 2 ^ (prefixWord ++ tailWord_534777).sum := by decide
  have hdescent : baseEnd_534777 < baseStart_534777 := by decide
  rcases family_descends (prefixWord ++ tailWord_534777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534844 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 7]
def baseStart_534844 : Nat := 118140960795 + 534844 * 2 ^ 59
def prefixEnd_534844 : Nat := 4983230072969 + 3 ^ 40 * 534844 * 2
def baseEnd_534844 : Nat := 30514671908156739343367

theorem tailTrace_534844 : CollatzResearch.WordTrace tailWord_534844 prefixEnd_534844 30514671908156739343367 := by
  unfold tailWord_534844
  simp only [CollatzResearch.WordTrace]
  refine ⟨9753681637179503464017793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13004908849572671285357057 9753681637179503464017793)
  ·
    refine ⟨7315261227884627598013345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9753681637179503464017793 7315261227884627598013345)
    ·
      refine ⟨5486445920913470698510009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7315261227884627598013345 5486445920913470698510009)
      ·
        refine ⟨4114834440685103023882507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5486445920913470698510009 4114834440685103023882507)
        ·
          refine ⟨6172251661027654535823761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4114834440685103023882507 6172251661027654535823761)
          ·
            refine ⟨4629188745770740901867821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6172251661027654535823761 4629188745770740901867821)
            ·
              refine ⟨1735945779664027838200433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4629188745770740901867821 1735945779664027838200433)
              ·
                refine ⟨1301959334748020878650325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735945779664027838200433 1301959334748020878650325)
                ·
                  refine ⟨30514671908156739343367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1301959334748020878650325 30514671908156739343367)
                  ·
                    rfl

theorem cell23_534844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_534844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534844 prefixEnd_534844 := by exact prefixLift 534844
  have htrace : WordTrace (prefixWord ++ tailWord_534844) baseStart_534844 baseEnd_534844 := by
    simpa [prefixWord, tailWord_534844, baseEnd_534844] using wordTrace_append hprefix tailTrace_534844
  have hstable : (prefixWord ++ tailWord_534844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534844).length < 2 ^ (prefixWord ++ tailWord_534844).sum := by decide
  have hdescent : baseEnd_534844 < baseStart_534844 := by decide
  rcases family_descends (prefixWord ++ tailWord_534844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534874 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_534874 : Nat := 118140960795 + 534874 * 2 ^ 59
def prefixEnd_534874 : Nat := 4983230072969 + 3 ^ 40 * 534874 * 2
def baseEnd_534874 : Nat := 91549150531015178905055

theorem tailTrace_534874 : CollatzResearch.WordTrace tailWord_534874 prefixEnd_534874 91549150531015178905055 := by
  unfold tailWord_534874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4877114366062580512906919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13005638309500214701085117 4877114366062580512906919)
  ·
    refine ⟨7315671549093870769360379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4877114366062580512906919 7315671549093870769360379)
    ·
      refine ⟨10973507323640806154040569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7315671549093870769360379 10973507323640806154040569)
      ·
        refine ⟨8230130492730604615530427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10973507323640806154040569 8230130492730604615530427)
        ·
          refine ⟨12345195739095906923295641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8230130492730604615530427 12345195739095906923295641)
          ·
            refine ⟨9258896804321930192471731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12345195739095906923295641 9258896804321930192471731)
            ·
              refine ⟨13888345206482895288707597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9258896804321930192471731 13888345206482895288707597)
              ·
                refine ⟨5208129452431085733265349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13888345206482895288707597 5208129452431085733265349)
                ·
                  refine ⟨976524272330828574987253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5208129452431085733265349 976524272330828574987253)
                  ·
                    refine ⟨91549150531015178905055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 976524272330828574987253 91549150531015178905055)
                    ·
                      rfl

theorem cell23_534874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_534874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534874 prefixEnd_534874 := by exact prefixLift 534874
  have htrace : WordTrace (prefixWord ++ tailWord_534874) baseStart_534874 baseEnd_534874 := by
    simpa [prefixWord, tailWord_534874, baseEnd_534874] using wordTrace_append hprefix tailTrace_534874
  have hstable : (prefixWord ++ tailWord_534874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534874).length < 2 ^ (prefixWord ++ tailWord_534874).sum := by decide
  have hdescent : baseEnd_534874 < baseStart_534874 := by decide
  rcases family_descends (prefixWord ++ tailWord_534874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534884 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_534884 : Nat := 118140960795 + 534884 * 2 ^ 59
def prefixEnd_534884 : Nat := 4983230072969 + 3 ^ 40 * 534884 * 2
def baseEnd_534884 : Nat := 274652586399590497590119

theorem tailTrace_534884 : CollatzResearch.WordTrace tailWord_534884 prefixEnd_534884 274652586399590497590119 := by
  unfold tailWord_534884
  simp only [CollatzResearch.WordTrace]
  refine ⟨9754411097107046879745853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13005881462809395839661137 9754411097107046879745853)
  ·
    refine ⟨3657904161415142579904695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9754411097107046879745853 3657904161415142579904695)
    ·
      refine ⟨5486856242122713869857043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3657904161415142579904695 5486856242122713869857043)
      ·
        refine ⟨8230284363184070804785565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5486856242122713869857043 8230284363184070804785565)
        ·
          refine ⟨3086356636194026551794587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8230284363184070804785565 3086356636194026551794587)
          ·
            refine ⟨4629534954291039827691881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086356636194026551794587 4629534954291039827691881)
            ·
              refine ⟨3472151215718279870768911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4629534954291039827691881 3472151215718279870768911)
              ·
                refine ⟨5208226823577419806153367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3472151215718279870768911 5208226823577419806153367)
                ·
                  refine ⟨7812340235366129709230051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5208226823577419806153367 7812340235366129709230051)
                  ·
                    refine ⟨11718510353049194563845077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7812340235366129709230051 11718510353049194563845077)
                    ·
                      refine ⟨274652586399590497590119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11718510353049194563845077 274652586399590497590119)
                      ·
                        rfl

theorem cell23_534884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_534884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534884 prefixEnd_534884 := by exact prefixLift 534884
  have htrace : WordTrace (prefixWord ++ tailWord_534884) baseStart_534884 baseEnd_534884 := by
    simpa [prefixWord, tailWord_534884, baseEnd_534884] using wordTrace_append hprefix tailTrace_534884
  have hstable : (prefixWord ++ tailWord_534884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534884).length < 2 ^ (prefixWord ++ tailWord_534884).sum := by decide
  have hdescent : baseEnd_534884 < baseStart_534884 := by decide
  rcases family_descends (prefixWord ++ tailWord_534884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534938 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_534938 : Nat := 118140960795 + 534938 * 2 ^ 59
def prefixEnd_534938 : Nat := 4983230072969 + 3 ^ 40 * 534938 * 2
def baseEnd_534938 : Nat := 91560104784977762104957

theorem tailTrace_534938 : CollatzResearch.WordTrace tailWord_534938 prefixEnd_534938 91560104784977762104957 := by
  unfold tailWord_534938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4877697934004615245489367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13007194490678973987971645 4877697934004615245489367)
  ·
    refine ⟨7316546901006922868234051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4877697934004615245489367 7316546901006922868234051)
    ·
      refine ⟨10974820351510384302351077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7316546901006922868234051 10974820351510384302351077)
      ·
        refine ⟨2057778815908197056690827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10974820351510384302351077 2057778815908197056690827)
        ·
          refine ⟨3086668223862295585036241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2057778815908197056690827 3086668223862295585036241)
          ·
            refine ⟨2315001167896721688777181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3086668223862295585036241 2315001167896721688777181)
            ·
              refine ⟨868125437961270633291443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2315001167896721688777181 868125437961270633291443)
              ·
                refine ⟨1302188156941905949937165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868125437961270633291443 1302188156941905949937165)
                ·
                  refine ⟨488320558853214731226437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1302188156941905949937165 488320558853214731226437)
                  ·
                    refine ⟨91560104784977762104957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 488320558853214731226437 91560104784977762104957)
                    ·
                      rfl

theorem cell23_534938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_534938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534938 prefixEnd_534938 := by exact prefixLift 534938
  have htrace : WordTrace (prefixWord ++ tailWord_534938) baseStart_534938 baseEnd_534938 := by
    simpa [prefixWord, tailWord_534938, baseEnd_534938] using wordTrace_append hprefix tailTrace_534938
  have hstable : (prefixWord ++ tailWord_534938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534938).length < 2 ^ (prefixWord ++ tailWord_534938).sum := by decide
  have hdescent : baseEnd_534938 < baseStart_534938 := by decide
  rcases family_descends (prefixWord ++ tailWord_534938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534965 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_534965 : Nat := 118140960795 + 534965 * 2 ^ 59
def prefixEnd_534965 : Nat := 4983230072969 + 3 ^ 40 * 534965 * 2
def baseEnd_534965 : Nat := 274694178332604680677247

theorem tailTrace_534965 : CollatzResearch.WordTrace tailWord_534965 prefixEnd_534965 274694178332604680677247 := by
  unfold tailWord_534965
  simp only [CollatzResearch.WordTrace]
  refine ⟨19511776506920644593190349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13007851004613763062126899 19511776506920644593190349)
  ·
    refine ⟨7316916190095241722446381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19511776506920644593190349 7316916190095241722446381)
    ·
      refine ⟨2743843571285715645917393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7316916190095241722446381 2743843571285715645917393)
      ·
        refine ⟨2057882678464286734438045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2743843571285715645917393 2057882678464286734438045)
        ·
          refine ⟨771706004424107525414267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2057882678464286734438045 771706004424107525414267)
          ·
            refine ⟨1157559006636161288121401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771706004424107525414267 1157559006636161288121401)
            ·
              refine ⟨868169254977120966091051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157559006636161288121401 868169254977120966091051)
              ·
                refine ⟨1302253882465681449136577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868169254977120966091051 1302253882465681449136577)
                ·
                  refine ⟨976690411849261086852433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1302253882465681449136577 976690411849261086852433)
                  ·
                    refine ⟨732517808886945815139325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 976690411849261086852433 732517808886945815139325)
                    ·
                      refine ⟨274694178332604680677247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 732517808886945815139325 274694178332604680677247)
                      ·
                        rfl

theorem cell23_534965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_534965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534965 prefixEnd_534965 := by exact prefixLift 534965
  have htrace : WordTrace (prefixWord ++ tailWord_534965) baseStart_534965 baseEnd_534965 := by
    simpa [prefixWord, tailWord_534965, baseEnd_534965] using wordTrace_append hprefix tailTrace_534965
  have hstable : (prefixWord ++ tailWord_534965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534965).length < 2 ^ (prefixWord ++ tailWord_534965).sum := by decide
  have hdescent : baseEnd_534965 < baseStart_534965 := by decide
  rcases family_descends (prefixWord ++ tailWord_534965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534998 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_534998 : Nat := 118140960795 + 534998 * 2 ^ 59
def prefixEnd_534998 : Nat := 4983230072969 + 3 ^ 40 * 534998 * 2
def baseEnd_534998 : Nat := 91570374398067683854865

theorem tailTrace_534998 : CollatzResearch.WordTrace tailWord_534998 prefixEnd_534998 91570374398067683854865 := by
  unfold tailWord_534998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1219561257237568201821353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13008653410534060819427765 1219561257237568201821353)
  ·
    refine ⟨914670942928176151366015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1219561257237568201821353 914670942928176151366015)
    ·
      refine ⟨1372006414392264227049023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914670942928176151366015 1372006414392264227049023)
      ·
        refine ⟨2058009621588396340573535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372006414392264227049023 2058009621588396340573535)
        ·
          refine ⟨3087014432382594510860303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058009621588396340573535 3087014432382594510860303)
          ·
            refine ⟨4630521648573891766290455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087014432382594510860303 4630521648573891766290455)
            ·
              refine ⟨6945782472860837649435683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4630521648573891766290455 6945782472860837649435683)
              ·
                refine ⟨10418673709291256474153525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6945782472860837649435683 10418673709291256474153525)
                ·
                  refine ⟨976750660246055294451893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10418673709291256474153525 976750660246055294451893)
                  ·
                    refine ⟨91570374398067683854865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 976750660246055294451893 91570374398067683854865)
                    ·
                      rfl

theorem cell23_534998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_534998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_534998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_534998 prefixEnd_534998 := by exact prefixLift 534998
  have htrace : WordTrace (prefixWord ++ tailWord_534998) baseStart_534998 baseEnd_534998 := by
    simpa [prefixWord, tailWord_534998, baseEnd_534998] using wordTrace_append hprefix tailTrace_534998
  have hstable : (prefixWord ++ tailWord_534998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534998).length < 2 ^ (prefixWord ++ tailWord_534998).sum := by decide
  have hdescent : baseEnd_534998 < baseStart_534998 := by decide
  rcases family_descends (prefixWord ++ tailWord_534998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535001 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 4]
def baseStart_535001 : Nat := 118140960795 + 535001 * 2 ^ 59
def prefixEnd_535001 : Nat := 4983230072969 + 3 ^ 40 * 535001 * 2
def baseEnd_535001 : Nat := 274712663636166539827081

theorem tailTrace_535001 : CollatzResearch.WordTrace tailWord_535001 prefixEnd_535001 274712663636166539827081 := by
  unfold tailWord_535001
  simp only [CollatzResearch.WordTrace]
  refine ⟨19513089534790222741500857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13008726356526815161000571 19513089534790222741500857)
  ·
    refine ⟨14634817151092667056125643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19513089534790222741500857 14634817151092667056125643)
    ·
      refine ⟨21952225726639000584188465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14634817151092667056125643 21952225726639000584188465)
      ·
        refine ⟨16464169294979250438141349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21952225726639000584188465 16464169294979250438141349)
        ·
          refine ⟨3087031742808609457151503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16464169294979250438141349 3087031742808609457151503)
          ·
            refine ⟨4630547614212914185727255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087031742808609457151503 4630547614212914185727255)
            ·
              refine ⟨6945821421319371278590883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4630547614212914185727255 6945821421319371278590883)
              ·
                refine ⟨10418732131979056917886325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6945821421319371278590883 10418732131979056917886325)
                ·
                  refine ⟨976756137373036586051843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10418732131979056917886325 976756137373036586051843)
                  ·
                    refine ⟨1465134206059554879077765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 976756137373036586051843 1465134206059554879077765)
                    ·
                      refine ⟨274712663636166539827081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1465134206059554879077765 274712663636166539827081)
                      ·
                        rfl

theorem cell23_535001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_535001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535001 prefixEnd_535001 := by exact prefixLift 535001
  have htrace : WordTrace (prefixWord ++ tailWord_535001) baseStart_535001 baseEnd_535001 := by
    simpa [prefixWord, tailWord_535001, baseEnd_535001] using wordTrace_append hprefix tailTrace_535001
  have hstable : (prefixWord ++ tailWord_535001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535001).length < 2 ^ (prefixWord ++ tailWord_535001).sum := by decide
  have hdescent : baseEnd_535001 < baseStart_535001 := by decide
  rcases family_descends (prefixWord ++ tailWord_535001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535018 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_535018 : Nat := 118140960795 + 535018 * 2 ^ 59
def prefixEnd_535018 : Nat := 4983230072969 + 3 ^ 40 * 535018 * 2
def baseEnd_535018 : Nat := 274721392807292973314503

theorem tailTrace_535018 : CollatzResearch.WordTrace tailWord_535018 prefixEnd_535018 274721392807292973314503 := by
  unfold tailWord_535018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4878427393932158661217427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13009139717152423096579805 4878427393932158661217427)
  ·
    refine ⟨7317641090898237991826141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4878427393932158661217427 7317641090898237991826141)
    ·
      refine ⟨2744115409086839246934803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7317641090898237991826141 2744115409086839246934803)
      ·
        refine ⟨4116173113630258870402205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2744115409086839246934803 4116173113630258870402205)
        ·
          refine ⟨1543564917611347076400827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4116173113630258870402205 1543564917611347076400827)
          ·
            refine ⟨2315347376417020614601241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543564917611347076400827 2315347376417020614601241)
            ·
              refine ⟨1736510532312765460950931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2315347376417020614601241 1736510532312765460950931)
              ·
                refine ⟨2604765798469148191426397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1736510532312765460950931 2604765798469148191426397)
                ·
                  refine ⟨976787174425930571784899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2604765798469148191426397 976787174425930571784899)
                  ·
                    refine ⟨1465180761638895857677349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 976787174425930571784899 1465180761638895857677349)
                    ·
                      refine ⟨274721392807292973314503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1465180761638895857677349 274721392807292973314503)
                      ·
                        rfl

theorem cell23_535018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_535018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535018 prefixEnd_535018 := by exact prefixLift 535018
  have htrace : WordTrace (prefixWord ++ tailWord_535018) baseStart_535018 baseEnd_535018 := by
    simpa [prefixWord, tailWord_535018, baseEnd_535018] using wordTrace_append hprefix tailTrace_535018
  have hstable : (prefixWord ++ tailWord_535018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535018).length < 2 ^ (prefixWord ++ tailWord_535018).sum := by decide
  have hdescent : baseEnd_535018 < baseStart_535018 := by decide
  rcases family_descends (prefixWord ++ tailWord_535018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535022 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_535022 : Nat := 118140960795 + 535022 * 2 ^ 59
def prefixEnd_535022 : Nat := 4983230072969 + 3 ^ 40 * 535022 * 2
def baseEnd_535022 : Nat := 274723446729910957664485

theorem tailTrace_535022 : CollatzResearch.WordTrace tailWord_535022 prefixEnd_535022 274723446729910957664485 := by
  unfold tailWord_535022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2439231933464267916001915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13009236978476095552010213 2439231933464267916001915)
  ·
    refine ⟨3658847900196401874002873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2439231933464267916001915 3658847900196401874002873)
    ·
      refine ⟨2744135925147301405502155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3658847900196401874002873 2744135925147301405502155)
      ·
        refine ⟨4116203887720952108253233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2744135925147301405502155 4116203887720952108253233)
        ·
          refine ⟨3087152915790714081189925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4116203887720952108253233 3087152915790714081189925)
          ·
            refine ⟨578841171710758890223111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3087152915790714081189925 578841171710758890223111)
            ·
              refine ⟨868261757566138335334667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578841171710758890223111 868261757566138335334667)
              ·
                refine ⟨1302392636349207503002001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868261757566138335334667 1302392636349207503002001)
                ·
                  refine ⟨976794477261905627251501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1302392636349207503002001 976794477261905627251501)
                  ·
                    refine ⟨366297928973214610219313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 976794477261905627251501 366297928973214610219313)
                    ·
                      refine ⟨274723446729910957664485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366297928973214610219313 274723446729910957664485)
                      ·
                        rfl

theorem cell23_535022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_535022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535022 prefixEnd_535022 := by exact prefixLift 535022
  have htrace : WordTrace (prefixWord ++ tailWord_535022) baseStart_535022 baseEnd_535022 := by
    simpa [prefixWord, tailWord_535022, baseEnd_535022] using wordTrace_append hprefix tailTrace_535022
  have hstable : (prefixWord ++ tailWord_535022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535022).length < 2 ^ (prefixWord ++ tailWord_535022).sum := by decide
  have hdescent : baseEnd_535022 < baseStart_535022 := by decide
  rcases family_descends (prefixWord ++ tailWord_535022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535041 : List Nat := [1, 2, 4, 1, 3, 2, 10]
def baseStart_535041 : Nat := 118140960795 + 535041 * 2 ^ 59
def prefixEnd_535041 : Nat := 4983230072969 + 3 ^ 40 * 535041 * 2
def baseEnd_535041 : Nat := 3391767936572177571937

theorem tailTrace_535041 : CollatzResearch.WordTrace tailWord_535041 prefixEnd_535041 3391767936572177571937 := by
  unfold tailWord_535041
  simp only [CollatzResearch.WordTrace]
  refine ⟨19514548454645309572956977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13009698969763539715304651 19514548454645309572956977)
  ·
    refine ⟨14635911340983982179717733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19514548454645309572956977 14635911340983982179717733)
    ·
      refine ⟨2744233376434496658697075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14635911340983982179717733 2744233376434496658697075)
      ·
        refine ⟨4116350064651744988045613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2744233376434496658697075 4116350064651744988045613)
        ·
          refine ⟨1543631274244404370517105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4116350064651744988045613 1543631274244404370517105)
          ·
            refine ⟨1157723455683303277887829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1543631274244404370517105 1157723455683303277887829)
            ·
              refine ⟨3391767936572177571937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1157723455683303277887829 3391767936572177571937)
              ·
                rfl

theorem cell23_535041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 10].length) (baseStart_535041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535041 prefixEnd_535041 := by exact prefixLift 535041
  have htrace : WordTrace (prefixWord ++ tailWord_535041) baseStart_535041 baseEnd_535041 := by
    simpa [prefixWord, tailWord_535041, baseEnd_535041] using wordTrace_append hprefix tailTrace_535041
  have hstable : (prefixWord ++ tailWord_535041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535041).length < 2 ^ (prefixWord ++ tailWord_535041).sum := by decide
  have hdescent : baseEnd_535041 < baseStart_535041 := by decide
  rcases family_descends (prefixWord ++ tailWord_535041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535046 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_535046 : Nat := 118140960795 + 535046 * 2 ^ 59
def prefixEnd_535046 : Nat := 4983230072969 + 3 ^ 40 * 535046 * 2
def baseEnd_535046 : Nat := 274735770265618863764375

theorem tailTrace_535046 : CollatzResearch.WordTrace tailWord_535046 prefixEnd_535046 274735770265618863764375 := by
  unfold tailWord_535046
  simp only [CollatzResearch.WordTrace]
  refine ⟨609835338113349857090281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13009820546418130284592661 609835338113349857090281)
  ·
    refine ⟨457376503585012392817711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 609835338113349857090281 457376503585012392817711)
    ·
      refine ⟨686064755377518589226567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457376503585012392817711 686064755377518589226567)
      ·
        refine ⟨1029097133066277883839851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686064755377518589226567 1029097133066277883839851)
        ·
          refine ⟨1543645699599416825759777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029097133066277883839851 1543645699599416825759777)
          ·
            refine ⟨1157734274699562619319833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1543645699599416825759777 1157734274699562619319833)
            ·
              refine ⟨868300706024671964489875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157734274699562619319833 868300706024671964489875)
              ·
                refine ⟨1302451059037007946734813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868300706024671964489875 1302451059037007946734813)
                ·
                  refine ⟨488419147138877980025555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1302451059037007946734813 488419147138877980025555)
                  ·
                    refine ⟨732628720708316970038333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 488419147138877980025555 732628720708316970038333)
                    ·
                      refine ⟨274735770265618863764375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 732628720708316970038333 274735770265618863764375)
                      ·
                        rfl

theorem cell23_535046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_535046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535046 prefixEnd_535046 := by exact prefixLift 535046
  have htrace : WordTrace (prefixWord ++ tailWord_535046) baseStart_535046 baseEnd_535046 := by
    simpa [prefixWord, tailWord_535046, baseEnd_535046] using wordTrace_append hprefix tailTrace_535046
  have hstable : (prefixWord ++ tailWord_535046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535046).length < 2 ^ (prefixWord ++ tailWord_535046).sum := by decide
  have hdescent : baseEnd_535046 < baseStart_535046 := by decide
  rcases family_descends (prefixWord ++ tailWord_535046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535052 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 3, 2, 2]
def baseStart_535052 : Nat := 118140960795 + 535052 * 2 ^ 59
def prefixEnd_535052 : Nat := 4983230072969 + 3 ^ 40 * 535052 * 2
def baseEnd_535052 : Nat := 274738851149545840289347

theorem tailTrace_535052 : CollatzResearch.WordTrace tailWord_535052 prefixEnd_535052 274738851149545840289347 := by
  unfold tailWord_535052
  simp only [CollatzResearch.WordTrace]
  refine ⟨9757474828802729225803705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13009966438403638967738273 9757474828802729225803705)
  ·
    refine ⟨7318106121602046919352779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9757474828802729225803705 7318106121602046919352779)
    ·
      refine ⟨10977159182403070379029169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7318106121602046919352779 10977159182403070379029169)
      ·
        refine ⟨8232869386802302784271877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10977159182403070379029169 8232869386802302784271877)
        ·
          refine ⟨1543663010025431772050977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8232869386802302784271877 1543663010025431772050977)
          ·
            refine ⟨1157747257519073829038233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1543663010025431772050977 1157747257519073829038233)
            ·
              refine ⟨868310443139305371778675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157747257519073829038233 868310443139305371778675)
              ·
                refine ⟨1302465664708958057668013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868310443139305371778675 1302465664708958057668013)
                ·
                  refine ⟨488424624265859271625505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1302465664708958057668013 488424624265859271625505)
                  ·
                    refine ⟨366318468199394453719129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 488424624265859271625505 366318468199394453719129)
                    ·
                      refine ⟨274738851149545840289347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366318468199394453719129 274738851149545840289347)
                      ·
                        rfl

theorem cell23_535052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_535052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535052 prefixEnd_535052 := by exact prefixLift 535052
  have htrace : WordTrace (prefixWord ++ tailWord_535052) baseStart_535052 baseEnd_535052 := by
    simpa [prefixWord, tailWord_535052, baseEnd_535052] using wordTrace_append hprefix tailTrace_535052
  have hstable : (prefixWord ++ tailWord_535052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535052).length < 2 ^ (prefixWord ++ tailWord_535052).sum := by decide
  have hdescent : baseEnd_535052 < baseStart_535052 := by decide
  rcases family_descends (prefixWord ++ tailWord_535052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535072 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 3]
def baseStart_535072 : Nat := 118140960795 + 535072 * 2 ^ 59
def prefixEnd_535072 : Nat := 4983230072969 + 3 ^ 40 * 535072 * 2
def baseEnd_535072 : Nat := 274749120762635762039255

theorem tailTrace_535072 : CollatzResearch.WordTrace tailWord_535072 prefixEnd_535072 274749120762635762039255 := by
  unfold tailWord_535072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9757839558766500933667735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13010452745022001244890313 9757839558766500933667735)
  ·
    refine ⟨14636759338149751400501603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9757839558766500933667735 14636759338149751400501603)
    ·
      refine ⟨21955139007224627100752405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14636759338149751400501603 21955139007224627100752405)
      ·
        refine ⟨1029147140963654395347769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21955139007224627100752405 1029147140963654395347769)
        ·
          refine ⟨771860355722740796510827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1029147140963654395347769 771860355722740796510827)
          ·
            refine ⟨1157790533584111194766241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771860355722740796510827 1157790533584111194766241)
            ·
              refine ⟨868342900188083396074681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157790533584111194766241 868342900188083396074681)
              ·
                refine ⟨651257175141062547056011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868342900188083396074681 651257175141062547056011)
                ·
                  refine ⟨976885762711593820584017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651257175141062547056011 976885762711593820584017)
                  ·
                    refine ⟨732664322033695365438013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 976885762711593820584017 732664322033695365438013)
                    ·
                      refine ⟨274749120762635762039255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 732664322033695365438013 274749120762635762039255)
                      ·
                        rfl

theorem cell23_535072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_535072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535072 prefixEnd_535072 := by exact prefixLift 535072
  have htrace : WordTrace (prefixWord ++ tailWord_535072) baseStart_535072 baseEnd_535072 := by
    simpa [prefixWord, tailWord_535072, baseEnd_535072] using wordTrace_append hprefix tailTrace_535072
  have hstable : (prefixWord ++ tailWord_535072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535072).length < 2 ^ (prefixWord ++ tailWord_535072).sum := by decide
  have hdescent : baseEnd_535072 < baseStart_535072 := by decide
  rcases family_descends (prefixWord ++ tailWord_535072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535092 : List Nat := [2, 5, 1, 3, 2, 1, 9]
def baseStart_535092 : Nat := 118140960795 + 535092 * 2 ^ 59
def prefixEnd_535092 : Nat := 4983230072969 + 3 ^ 40 * 535092 * 2
def baseEnd_535092 : Nat := 3392091239206489923323

theorem tailTrace_535092 : CollatzResearch.WordTrace tailWord_535092 prefixEnd_535092 3392091239206489923323 := by
  unfold tailWord_535092
  simp only [CollatzResearch.WordTrace]
  refine ⟨9758204288730272641531765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13010939051640363522042353 9758204288730272641531765)
  ·
    refine ⟨914831652068463060143603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9758204288730272641531765 914831652068463060143603)
    ·
      refine ⟨1372247478102694590215405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914831652068463060143603 1372247478102694590215405)
      ·
        refine ⟨514592804288510471330777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1372247478102694590215405 514592804288510471330777)
        ·
          refine ⟨385944603216382853498083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514592804288510471330777 385944603216382853498083)
          ·
            refine ⟨578916904824574280247125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385944603216382853498083 578916904824574280247125)
            ·
              refine ⟨3392091239206489923323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 578916904824574280247125 3392091239206489923323)
              ·
                rfl

theorem cell23_535092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 9].length) (baseStart_535092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535092 prefixEnd_535092 := by exact prefixLift 535092
  have htrace : WordTrace (prefixWord ++ tailWord_535092) baseStart_535092 baseEnd_535092 := by
    simpa [prefixWord, tailWord_535092, baseEnd_535092] using wordTrace_append hprefix tailTrace_535092
  have hstable : (prefixWord ++ tailWord_535092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535092).length < 2 ^ (prefixWord ++ tailWord_535092).sum := by decide
  have hdescent : baseEnd_535092 < baseStart_535092 := by decide
  rcases family_descends (prefixWord ++ tailWord_535092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535095 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 1, 3, 2]
def baseStart_535095 : Nat := 118140960795 + 535095 * 2 ^ 59
def prefixEnd_535095 : Nat := 4983230072969 + 3 ^ 40 * 535095 * 2
def baseEnd_535095 : Nat := 274760930817689172051649

theorem tailTrace_535095 : CollatzResearch.WordTrace tailWord_535095 prefixEnd_535095 274760930817689172051649 := by
  unfold tailWord_535095
  simp only [CollatzResearch.WordTrace]
  refine ⟨19516517996449676795422739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13011011997633117863615159 19516517996449676795422739)
  ·
    refine ⟨29274776994674515193134109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19516517996449676795422739 29274776994674515193134109)
    ·
      refine ⟨10978041373002943197425291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29274776994674515193134109 10978041373002943197425291)
      ·
        refine ⟨16467062059504414796137937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10978041373002943197425291 16467062059504414796137937)
        ·
          refine ⟨12350296544628311097103453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16467062059504414796137937 12350296544628311097103453)
          ·
            refine ⟨4631361204235616661413795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12350296544628311097103453 4631361204235616661413795)
            ·
              refine ⟨6947041806353424992120693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4631361204235616661413795 6947041806353424992120693)
              ·
                refine ⟨651285169345633593011315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6947041806353424992120693 651285169345633593011315)
                ·
                  refine ⟨976927754018450389516973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651285169345633593011315 976927754018450389516973)
                  ·
                    refine ⟨366347907756918896068865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 976927754018450389516973 366347907756918896068865)
                    ·
                      refine ⟨274760930817689172051649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366347907756918896068865 274760930817689172051649)
                      ·
                        rfl

theorem cell23_535095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_535095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535095 prefixEnd_535095 := by exact prefixLift 535095
  have htrace : WordTrace (prefixWord ++ tailWord_535095) baseStart_535095 baseEnd_535095 := by
    simpa [prefixWord, tailWord_535095, baseEnd_535095] using wordTrace_append hprefix tailTrace_535095
  have hstable : (prefixWord ++ tailWord_535095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535095).length < 2 ^ (prefixWord ++ tailWord_535095).sum := by decide
  have hdescent : baseEnd_535095 < baseStart_535095 := by decide
  rcases family_descends (prefixWord ++ tailWord_535095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535210 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_535210 : Nat := 118140960795 + 535210 * 2 ^ 59
def prefixEnd_535210 : Nat := 4983230072969 + 3 ^ 40 * 535210 * 2
def baseEnd_535210 : Nat := 274819981092956222113621

theorem tailTrace_535210 : CollatzResearch.WordTrace tailWord_535210 prefixEnd_535210 274819981092956222113621 := by
  unfold tailWord_535210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4880178097758262858964771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13013808260688700957239389 4880178097758262858964771)
  ·
    refine ⟨7320267146637394288447157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4880178097758262858964771 7320267146637394288447157)
    ·
      refine ⟨686275044997255714541921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7320267146637394288447157 686275044997255714541921)
      ·
        refine ⟨514706283747941785906441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686275044997255714541921 514706283747941785906441)
        ·
          refine ⟨386029712810956339429831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514706283747941785906441 386029712810956339429831)
          ·
            refine ⟨579044569216434509144747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386029712810956339429831 579044569216434509144747)
            ·
              refine ⟨868566853824651763717121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579044569216434509144747 868566853824651763717121)
              ·
                refine ⟨651425140368488822787841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868566853824651763717121 651425140368488822787841)
                ·
                  refine ⟨488568855276366617090881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 651425140368488822787841 488568855276366617090881)
                  ·
                    refine ⟨366426641457274962818161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 488568855276366617090881 366426641457274962818161)
                    ·
                      refine ⟨274819981092956222113621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366426641457274962818161 274819981092956222113621)
                      ·
                        rfl

theorem cell23_535210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_535210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535210 prefixEnd_535210 := by exact prefixLift 535210
  have htrace : WordTrace (prefixWord ++ tailWord_535210) baseStart_535210 baseEnd_535210 := by
    simpa [prefixWord, tailWord_535210, baseEnd_535210] using wordTrace_append hprefix tailTrace_535210
  have hstable : (prefixWord ++ tailWord_535210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535210).length < 2 ^ (prefixWord ++ tailWord_535210).sum := by decide
  have hdescent : baseEnd_535210 < baseStart_535210 := by decide
  rcases family_descends (prefixWord ++ tailWord_535210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535215 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 2, 4, 2]
def baseStart_535215 : Nat := 118140960795 + 535215 * 2 ^ 59
def prefixEnd_535215 : Nat := 4983230072969 + 3 ^ 40 * 535215 * 2
def baseEnd_535215 : Nat := 274822548496228702551097

theorem tailTrace_535215 : CollatzResearch.WordTrace tailWord_535215 prefixEnd_535215 274822548496228702551097 := by
  unfold tailWord_535215
  simp only [CollatzResearch.WordTrace]
  refine ⟨19520894756014937289791099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13013929837343291526527399 19520894756014937289791099)
  ·
    refine ⟨29281342134022405934686649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19520894756014937289791099 29281342134022405934686649)
    ·
      refine ⟨21961006600516804451014987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29281342134022405934686649 21961006600516804451014987)
      ·
        refine ⟨32941509900775206676522481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21961006600516804451014987 32941509900775206676522481)
        ·
          refine ⟨24706132425581405007391861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32941509900775206676522481 24706132425581405007391861)
          ·
            refine ⟨2316199914898256719442987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24706132425581405007391861 2316199914898256719442987)
            ·
              refine ⟨3474299872347385079164481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2316199914898256719442987 3474299872347385079164481)
              ·
                refine ⟨2605724904260538809373361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3474299872347385079164481 2605724904260538809373361)
                ·
                  refine ⟨1954293678195404107030021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2605724904260538809373361 1954293678195404107030021)
                  ·
                    refine ⟨366430064661638270068129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1954293678195404107030021 366430064661638270068129)
                    ·
                      refine ⟨274822548496228702551097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366430064661638270068129 274822548496228702551097)
                      ·
                        rfl

theorem cell23_535215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 4, 2].length) (baseStart_535215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535215 prefixEnd_535215 := by exact prefixLift 535215
  have htrace : WordTrace (prefixWord ++ tailWord_535215) baseStart_535215 baseEnd_535215 := by
    simpa [prefixWord, tailWord_535215, baseEnd_535215] using wordTrace_append hprefix tailTrace_535215
  have hstable : (prefixWord ++ tailWord_535215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535215).length < 2 ^ (prefixWord ++ tailWord_535215).sum := by decide
  have hdescent : baseEnd_535215 < baseStart_535215 := by decide
  rcases family_descends (prefixWord ++ tailWord_535215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535228 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_535228 : Nat := 118140960795 + 535228 * 2 ^ 59
def prefixEnd_535228 : Nat := 4983230072969 + 3 ^ 40 * 535228 * 2
def baseEnd_535228 : Nat := 274829223744737151688537

theorem tailTrace_535228 : CollatzResearch.WordTrace tailWord_535228 prefixEnd_535228 274829223744737151688537 := by
  unfold tailWord_535228
  simp only [CollatzResearch.WordTrace]
  refine ⟨9760684452483920255007169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13014245936645227006676225 9760684452483920255007169)
  ·
    refine ⟨7320513339362940191255377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9760684452483920255007169 7320513339362940191255377)
    ·
      refine ⟨5490385004522205143441533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7320513339362940191255377 5490385004522205143441533)
      ·
        refine ⟨2058894376695826928790575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5490385004522205143441533 2058894376695826928790575)
        ·
          refine ⟨3088341565043740393185863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058894376695826928790575 3088341565043740393185863)
          ·
            refine ⟨4632512347565610589778795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088341565043740393185863 4632512347565610589778795)
            ·
              refine ⟨6948768521348415884668193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632512347565610589778795 6948768521348415884668193)
              ·
                refine ⟨5211576391011311913501145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6948768521348415884668193 5211576391011311913501145)
                ·
                  refine ⟨3908682293258483935125859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5211576391011311913501145 3908682293258483935125859)
                  ·
                    refine ⟨5863023439887725902688789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3908682293258483935125859 5863023439887725902688789)
                    ·
                      refine ⟨274829223744737151688537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5863023439887725902688789 274829223744737151688537)
                      ·
                        rfl

theorem cell23_535228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_535228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535228 prefixEnd_535228 := by exact prefixLift 535228
  have htrace : WordTrace (prefixWord ++ tailWord_535228) baseStart_535228 baseEnd_535228 := by
    simpa [prefixWord, tailWord_535228, baseEnd_535228] using wordTrace_append hprefix tailTrace_535228
  have hstable : (prefixWord ++ tailWord_535228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535228).length < 2 ^ (prefixWord ++ tailWord_535228).sum := by decide
  have hdescent : baseEnd_535228 < baseStart_535228 := by decide
  rcases family_descends (prefixWord ++ tailWord_535228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535305 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 2, 6, 2]
def baseStart_535305 : Nat := 118140960795 + 535305 * 2 ^ 59
def prefixEnd_535305 : Nat := 4983230072969 + 3 ^ 40 * 535305 * 2
def baseEnd_535305 : Nat := 274868761755133350425683

theorem tailTrace_535305 : CollatzResearch.WordTrace tailWord_535305 prefixEnd_535305 274868761755133350425683 := by
  unfold tailWord_535305
  simp only [CollatzResearch.WordTrace]
  refine ⟨19524177325688882660567369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13016118217125921773711579 19524177325688882660567369)
  ·
    refine ⟨14643132994266661995425527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19524177325688882660567369 14643132994266661995425527)
    ·
      refine ⟨21964699491399992993138291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14643132994266661995425527 21964699491399992993138291)
      ·
        refine ⟨32947049237099989489707437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21964699491399992993138291 32947049237099989489707437)
        ·
          refine ⟨12355143463912496058640289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32947049237099989489707437 12355143463912496058640289)
          ·
            refine ⟨9266357597934372043980217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12355143463912496058640289 9266357597934372043980217)
            ·
              refine ⟨6949768198450779032985163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9266357597934372043980217 6949768198450779032985163)
              ·
                refine ⟨10424652297676168549477745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6949768198450779032985163 10424652297676168549477745)
                ·
                  refine ⟨7818489223257126412108309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10424652297676168549477745 7818489223257126412108309)
                  ·
                    refine ⟨366491682340177800567577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7818489223257126412108309 366491682340177800567577)
                    ·
                      refine ⟨274868761755133350425683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366491682340177800567577 274868761755133350425683)
                      ·
                        rfl

theorem cell23_535305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 6, 2].length) (baseStart_535305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535305 prefixEnd_535305 := by exact prefixLift 535305
  have htrace : WordTrace (prefixWord ++ tailWord_535305) baseStart_535305 baseEnd_535305 := by
    simpa [prefixWord, tailWord_535305, baseEnd_535305] using wordTrace_append hprefix tailTrace_535305
  have hstable : (prefixWord ++ tailWord_535305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535305).length < 2 ^ (prefixWord ++ tailWord_535305).sum := by decide
  have hdescent : baseEnd_535305 < baseStart_535305 := by decide
  rcases family_descends (prefixWord ++ tailWord_535305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535319 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 1, 5]
def baseStart_535319 : Nat := 118140960795 + 535319 * 2 ^ 59
def prefixEnd_535319 : Nat := 4983230072969 + 3 ^ 40 * 535319 * 2
def baseEnd_535319 : Nat := 91625316828098765216873

theorem tailTrace_535319 : CollatzResearch.WordTrace tailWord_535319 prefixEnd_535319 91625316828098765216873 := by
  unfold tailWord_535319
  simp only [CollatzResearch.WordTrace]
  refine ⟨19524687947638163051577011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13016458631758775367718007 19524687947638163051577011)
  ·
    refine ⟨29287031921457244577365517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19524687947638163051577011 29287031921457244577365517)
    ·
      refine ⟨10982636970546466716512069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29287031921457244577365517 10982636970546466716512069)
      ·
        refine ⟨2059244431977462509346013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10982636970546466716512069 2059244431977462509346013)
        ·
          refine ⟨772216661991548441004755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2059244431977462509346013 772216661991548441004755)
          ·
            refine ⟨1158324992987322661507133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772216661991548441004755 1158324992987322661507133)
            ·
              refine ⟨434371872370245998065175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1158324992987322661507133 434371872370245998065175)
              ·
                refine ⟨651557808555368997097763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434371872370245998065175 651557808555368997097763)
                ·
                  refine ⟨977336712833053495646645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651557808555368997097763 977336712833053495646645)
                  ·
                    refine ⟨91625316828098765216873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 977336712833053495646645 91625316828098765216873)
                    ·
                      rfl

theorem cell23_535319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_535319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535319 prefixEnd_535319 := by exact prefixLift 535319
  have htrace : WordTrace (prefixWord ++ tailWord_535319) baseStart_535319 baseEnd_535319 := by
    simpa [prefixWord, tailWord_535319, baseEnd_535319] using wordTrace_append hprefix tailTrace_535319
  have hstable : (prefixWord ++ tailWord_535319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535319).length < 2 ^ (prefixWord ++ tailWord_535319).sum := by decide
  have hdescent : baseEnd_535319 < baseStart_535319 := by decide
  rcases family_descends (prefixWord ++ tailWord_535319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535328 : List Nat := [2, 1, 1, 5, 1, 13]
def baseStart_535328 : Nat := 118140960795 + 535328 * 2 ^ 59
def prefixEnd_535328 : Nat := 4983230072969 + 3 ^ 40 * 535328 * 2
def baseEnd_535328 : Nat := 1131195768766200660239

theorem tailTrace_535328 : CollatzResearch.WordTrace tailWord_535328 prefixEnd_535328 1131195768766200660239 := by
  unfold tailWord_535328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762508102302778794327319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13016677469737038392436425 9762508102302778794327319)
  ·
    refine ⟨14643762153454168191490979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9762508102302778794327319 14643762153454168191490979)
    ·
      refine ⟨21965643230181252287236469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14643762153454168191490979 21965643230181252287236469)
      ·
        refine ⟨2059279052829492401928419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21965643230181252287236469 2059279052829492401928419)
        ·
          refine ⟨3088918579244238602892629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2059279052829492401928419 3088918579244238602892629)
          ·
            refine ⟨1131195768766200660239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 3088918579244238602892629 1131195768766200660239)
            ·
              rfl

theorem cell23_535328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 13].length) (baseStart_535328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535328 prefixEnd_535328 := by exact prefixLift 535328
  have htrace : WordTrace (prefixWord ++ tailWord_535328) baseStart_535328 baseEnd_535328 := by
    simpa [prefixWord, tailWord_535328, baseEnd_535328] using wordTrace_append hprefix tailTrace_535328
  have hstable : (prefixWord ++ tailWord_535328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535328).length < 2 ^ (prefixWord ++ tailWord_535328).sum := by decide
  have hdescent : baseEnd_535328 < baseStart_535328 := by decide
  rcases family_descends (prefixWord ++ tailWord_535328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535372 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 1, 3, 3]
def baseStart_535372 : Nat := 118140960795 + 535372 * 2 ^ 59
def prefixEnd_535372 : Nat := 4983230072969 + 3 ^ 40 * 535372 * 2
def baseEnd_535372 : Nat := 274903164958984588287875

theorem tailTrace_535372 : CollatzResearch.WordTrace tailWord_535372 prefixEnd_535372 274903164958984588287875 := by
  unfold tailWord_535372
  simp only [CollatzResearch.WordTrace]
  refine ⟨9763310508223076551628185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13017747344297435402170913 9763310508223076551628185)
  ·
    refine ⟨7322482881167307413721139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9763310508223076551628185 7322482881167307413721139)
    ·
      refine ⟨10983724321750961120581709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7322482881167307413721139 10983724321750961120581709)
      ·
        refine ⟨4118896620656610420218141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10983724321750961120581709 4118896620656610420218141)
        ·
          refine ⟨1544586232746228907581803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4118896620656610420218141 1544586232746228907581803)
          ·
            refine ⟨2316879349119343361372705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544586232746228907581803 2316879349119343361372705)
            ·
              refine ⟨1737659511839507521029529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2316879349119343361372705 1737659511839507521029529)
              ·
                refine ⟨1303244633879630640772147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1737659511839507521029529 1303244633879630640772147)
                ·
                  refine ⟨1954866950819445961158221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303244633879630640772147 1954866950819445961158221)
                  ·
                    refine ⟨733075106557292235434333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1954866950819445961158221 733075106557292235434333)
                    ·
                      refine ⟨274903164958984588287875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 733075106557292235434333 274903164958984588287875)
                      ·
                        rfl

theorem cell23_535372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_535372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535372 prefixEnd_535372 := by exact prefixLift 535372
  have htrace : WordTrace (prefixWord ++ tailWord_535372) baseStart_535372 baseEnd_535372 := by
    simpa [prefixWord, tailWord_535372, baseEnd_535372] using wordTrace_append hprefix tailTrace_535372
  have hstable : (prefixWord ++ tailWord_535372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535372).length < 2 ^ (prefixWord ++ tailWord_535372).sum := by decide
  have hdescent : baseEnd_535372 < baseStart_535372 := by decide
  rcases family_descends (prefixWord ++ tailWord_535372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535373 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_535373 : Nat := 118140960795 + 535373 * 2 ^ 59
def prefixEnd_535373 : Nat := 4983230072969 + 3 ^ 40 * 535373 * 2
def baseEnd_535373 : Nat := 274903678439639084375371

theorem tailTrace_535373 : CollatzResearch.WordTrace tailWord_535373 prefixEnd_535373 274903678439639084375371 := by
  unfold tailWord_535373
  simp only [CollatzResearch.WordTrace]
  refine ⟨19526657489442530274042773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13017771659628353516028515 19526657489442530274042773)
  ·
    refine ⟨915312069817618606595755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19526657489442530274042773 915312069817618606595755)
    ·
      refine ⟨1372968104726427909893633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 915312069817618606595755 1372968104726427909893633)
      ·
        refine ⟨1029726078544820932420225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1372968104726427909893633 1029726078544820932420225)
        ·
          refine ⟨772294558908615699315169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1029726078544820932420225 772294558908615699315169)
          ·
            refine ⟨579220919181461774486377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772294558908615699315169 579220919181461774486377)
            ·
              refine ⟨434415689386096330864783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579220919181461774486377 434415689386096330864783)
              ·
                refine ⟨651623534079144496297175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434415689386096330864783 651623534079144496297175)
                ·
                  refine ⟨977435301118716744445763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651623534079144496297175 977435301118716744445763)
                  ·
                    refine ⟨1466152951678075116668645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 977435301118716744445763 1466152951678075116668645)
                    ·
                      refine ⟨274903678439639084375371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1466152951678075116668645 274903678439639084375371)
                      ·
                        rfl

theorem cell23_535373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_535373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535373 prefixEnd_535373 := by exact prefixLift 535373
  have htrace : WordTrace (prefixWord ++ tailWord_535373) baseStart_535373 baseEnd_535373 := by
    simpa [prefixWord, tailWord_535373, baseEnd_535373] using wordTrace_append hprefix tailTrace_535373
  have hstable : (prefixWord ++ tailWord_535373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535373).length < 2 ^ (prefixWord ++ tailWord_535373).sum := by decide
  have hdescent : baseEnd_535373 < baseStart_535373 := by decide
  rcases family_descends (prefixWord ++ tailWord_535373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535406 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_535406 : Nat := 118140960795 + 535406 * 2 ^ 59
def prefixEnd_535406 : Nat := 4983230072969 + 3 ^ 40 * 535406 * 2
def baseEnd_535406 : Nat := 274920623301237455262719

theorem tailTrace_535406 : CollatzResearch.WordTrace tailWord_535406 prefixEnd_535406 274920623301237455262719 := by
  unfold tailWord_535406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2440982637290372113749259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13018574065548651273329381 2440982637290372113749259)
  ·
    refine ⟨3661473955935558170623889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2440982637290372113749259 3661473955935558170623889)
    ·
      refine ⟨2746105466951668627967917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3661473955935558170623889 2746105466951668627967917)
      ·
        refine ⟨1029789550106875735487969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2746105466951668627967917 1029789550106875735487969)
        ·
          refine ⟨772342162580156801615977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1029789550106875735487969 772342162580156801615977)
          ·
            refine ⟨579256621935117601211983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772342162580156801615977 579256621935117601211983)
            ·
              refine ⟨868884932902676401817975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579256621935117601211983 868884932902676401817975)
              ·
                refine ⟨1303327399354014602726963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868884932902676401817975 1303327399354014602726963)
                ·
                  refine ⟨1954991099031021904090445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303327399354014602726963 1954991099031021904090445)
                  ·
                    refine ⟨733121662136633214033917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1954991099031021904090445 733121662136633214033917)
                    ·
                      refine ⟨274920623301237455262719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 733121662136633214033917 274920623301237455262719)
                      ·
                        rfl

theorem cell23_535406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_535406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535406 prefixEnd_535406 := by exact prefixLift 535406
  have htrace : WordTrace (prefixWord ++ tailWord_535406) baseStart_535406 baseEnd_535406 := by
    simpa [prefixWord, tailWord_535406, baseEnd_535406] using wordTrace_append hprefix tailTrace_535406
  have hstable : (prefixWord ++ tailWord_535406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535406).length < 2 ^ (prefixWord ++ tailWord_535406).sum := by decide
  have hdescent : baseEnd_535406 < baseStart_535406 := by decide
  rcases family_descends (prefixWord ++ tailWord_535406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535415 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 3]
def baseStart_535415 : Nat := 118140960795 + 535415 * 2 ^ 59
def prefixEnd_535415 : Nat := 4983230072969 + 3 ^ 40 * 535415 * 2
def baseEnd_535415 : Nat := 274925244627127920050177

theorem tailTrace_535415 : CollatzResearch.WordTrace tailWord_535415 prefixEnd_535415 274925244627127920050177 := by
  unfold tailWord_535415
  simp only [CollatzResearch.WordTrace]
  refine ⟨19528189355290371447071699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13018792903526914298047799 19528189355290371447071699)
  ·
    refine ⟨29292284032935557170607549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19528189355290371447071699 29292284032935557170607549)
    ·
      refine ⟨10984606512350833938977831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29292284032935557170607549 10984606512350833938977831)
      ·
        refine ⟨16476909768526250908466747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10984606512350833938977831 16476909768526250908466747)
        ·
          refine ⟨24715364652789376362700121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16476909768526250908466747 24715364652789376362700121)
          ·
            refine ⟨18536523489592032272025091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24715364652789376362700121 18536523489592032272025091)
            ·
              refine ⟨27804785234388048408037637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18536523489592032272025091 27804785234388048408037637)
              ·
                refine ⟨5213397231447759076507057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27804785234388048408037637 5213397231447759076507057)
                ·
                  refine ⟨3910047923585819307380293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5213397231447759076507057 3910047923585819307380293)
                  ·
                    refine ⟨733133985672341120133805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3910047923585819307380293 733133985672341120133805)
                    ·
                      refine ⟨274925244627127920050177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 733133985672341120133805 274925244627127920050177)
                      ·
                        rfl

theorem cell23_535415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_535415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535415 prefixEnd_535415 := by exact prefixLift 535415
  have htrace : WordTrace (prefixWord ++ tailWord_535415) baseStart_535415 baseEnd_535415 := by
    simpa [prefixWord, tailWord_535415, baseEnd_535415] using wordTrace_append hprefix tailTrace_535415
  have hstable : (prefixWord ++ tailWord_535415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535415).length < 2 ^ (prefixWord ++ tailWord_535415).sum := by decide
  have hdescent : baseEnd_535415 < baseStart_535415 := by decide
  rcases family_descends (prefixWord ++ tailWord_535415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535429 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 4, 2, 2]
def baseStart_535429 : Nat := 118140960795 + 535429 * 2 ^ 59
def prefixEnd_535429 : Nat := 4983230072969 + 3 ^ 40 * 535429 * 2
def baseEnd_535429 : Nat := 274932433356290865275113

theorem tailTrace_535429 : CollatzResearch.WordTrace tailWord_535429 prefixEnd_535429 274932433356290865275113 := by
  unfold tailWord_535429
  simp only [CollatzResearch.WordTrace]
  refine ⟨19528699977239651838081341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13019133318159767892054227 19528699977239651838081341)
  ·
    refine ⟨7323262491464869439280503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19528699977239651838081341 7323262491464869439280503)
    ·
      refine ⟨10984893737197304158920755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7323262491464869439280503 10984893737197304158920755)
      ·
        refine ⟨16477340605795956238381133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10984893737197304158920755 16477340605795956238381133)
        ·
          refine ⟨6179002727173483589392925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16477340605795956238381133 6179002727173483589392925)
          ·
            refine ⟨2317126022690056346022347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6179002727173483589392925 2317126022690056346022347)
            ·
              refine ⟨3475689034035084519033521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317126022690056346022347 3475689034035084519033521)
              ·
                refine ⟨2606766775526313389275141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3475689034035084519033521 2606766775526313389275141)
                ·
                  refine ⟨488768770411183760489089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2606766775526313389275141 488768770411183760489089)
                  ·
                    refine ⟨366576577808387820366817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 488768770411183760489089 366576577808387820366817)
                    ·
                      refine ⟨274932433356290865275113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366576577808387820366817 274932433356290865275113)
                      ·
                        rfl

theorem cell23_535429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_535429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535429 prefixEnd_535429 := by exact prefixLift 535429
  have htrace : WordTrace (prefixWord ++ tailWord_535429) baseStart_535429 baseEnd_535429 := by
    simpa [prefixWord, tailWord_535429, baseEnd_535429] using wordTrace_append hprefix tailTrace_535429
  have hstable : (prefixWord ++ tailWord_535429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535429).length < 2 ^ (prefixWord ++ tailWord_535429).sum := by decide
  have hdescent : baseEnd_535429 < baseStart_535429 := by decide
  rcases family_descends (prefixWord ++ tailWord_535429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535432 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_535432 : Nat := 118140960795 + 535432 * 2 ^ 59
def prefixEnd_535432 : Nat := 4983230072969 + 3 ^ 40 * 535432 * 2
def baseEnd_535432 : Nat := 274933973798254353537599

theorem tailTrace_535432 : CollatzResearch.WordTrace tailWord_535432 prefixEnd_535432 274933973798254353537599 := by
  unfold tailWord_535432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9764404698114391675220275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13019206264152522233627033 9764404698114391675220275)
  ·
    refine ⟨14646607047171587512830413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9764404698114391675220275 14646607047171587512830413)
    ·
      refine ⟨5492477642689345317311405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14646607047171587512830413 5492477642689345317311405)
      ·
        refine ⟨2059679116008504493991777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5492477642689345317311405 2059679116008504493991777)
        ·
          refine ⟨1544759337006378370493833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2059679116008504493991777 1544759337006378370493833)
          ·
            refine ⟨1158569502754783777870375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544759337006378370493833 1158569502754783777870375)
            ·
              refine ⟨1737854254132175666805563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158569502754783777870375 1737854254132175666805563)
              ·
                refine ⟨2606781381198263500208345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737854254132175666805563 2606781381198263500208345)
                ·
                  refine ⟨1955086035898697625156259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2606781381198263500208345 1955086035898697625156259)
                  ·
                    refine ⟨2932629053848046437734389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1955086035898697625156259 2932629053848046437734389)
                    ·
                      refine ⟨274933973798254353537599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2932629053848046437734389 274933973798254353537599)
                      ·
                        rfl

theorem cell23_535432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_535432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535432 prefixEnd_535432 := by exact prefixLift 535432
  have htrace : WordTrace (prefixWord ++ tailWord_535432) baseStart_535432 baseEnd_535432 := by
    simpa [prefixWord, tailWord_535432, baseEnd_535432] using wordTrace_append hprefix tailTrace_535432
  have hstable : (prefixWord ++ tailWord_535432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535432).length < 2 ^ (prefixWord ++ tailWord_535432).sum := by decide
  have hdescent : baseEnd_535432 < baseStart_535432 := by decide
  rcases family_descends (prefixWord ++ tailWord_535432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535463 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_535463 : Nat := 118140960795 + 535463 * 2 ^ 59
def prefixEnd_535463 : Nat := 4983230072969 + 3 ^ 40 * 535463 * 2
def baseEnd_535463 : Nat := 274949891698543732249957

theorem tailTrace_535463 : CollatzResearch.WordTrace tailWord_535463 prefixEnd_535463 274949891698543732249957 := by
  unfold tailWord_535463
  simp only [CollatzResearch.WordTrace]
  refine ⟨19529940059116475644819043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13019960039410983763212695 19529940059116475644819043)
  ·
    refine ⟨29294910088674713467228565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19529940059116475644819043 29294910088674713467228565)
    ·
      refine ⟨1373198910406627193776339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29294910088674713467228565 1373198910406627193776339)
      ·
        refine ⟨2059798365609940790664509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1373198910406627193776339 2059798365609940790664509)
        ·
          refine ⟨772424387103727796499191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2059798365609940790664509 772424387103727796499191)
          ·
            refine ⟨1158636580655591694748787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772424387103727796499191 1158636580655591694748787)
            ·
              refine ⟨1737954870983387542123181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158636580655591694748787 1737954870983387542123181)
              ·
                refine ⟨651733076618770328296193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1737954870983387542123181 651733076618770328296193)
                ·
                  refine ⟨488799807464077746222145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 651733076618770328296193 488799807464077746222145)
                  ·
                    refine ⟨366599855598058309666609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 488799807464077746222145 366599855598058309666609)
                    ·
                      refine ⟨274949891698543732249957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366599855598058309666609 274949891698543732249957)
                      ·
                        rfl

theorem cell23_535463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_535463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535463 prefixEnd_535463 := by exact prefixLift 535463
  have htrace : WordTrace (prefixWord ++ tailWord_535463) baseStart_535463 baseEnd_535463 := by
    simpa [prefixWord, tailWord_535463, baseEnd_535463] using wordTrace_append hprefix tailTrace_535463
  have hstable : (prefixWord ++ tailWord_535463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535463).length < 2 ^ (prefixWord ++ tailWord_535463).sum := by decide
  have hdescent : baseEnd_535463 < baseStart_535463 := by decide
  rcases family_descends (prefixWord ++ tailWord_535463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535465 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 4, 5]
def baseStart_535465 : Nat := 118140960795 + 535465 * 2 ^ 59
def prefixEnd_535465 : Nat := 4983230072969 + 3 ^ 40 * 535465 * 2
def baseEnd_535465 : Nat := 91650306219950908141649

theorem tailTrace_535465 : CollatzResearch.WordTrace tailWord_535465 prefixEnd_535465 91650306219950908141649 := by
  unfold tailWord_535465
  simp only [CollatzResearch.WordTrace]
  refine ⟨19530013005109229986391849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13020008670072819990927899 19530013005109229986391849)
  ·
    refine ⟨14647509753831922489793887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19530013005109229986391849 14647509753831922489793887)
    ·
      refine ⟨21971264630747883734690831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14647509753831922489793887 21971264630747883734690831)
      ·
        refine ⟨32956896946121825602036247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21971264630747883734690831 32956896946121825602036247)
        ·
          refine ⟨49435345419182738403054371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32956896946121825602036247 49435345419182738403054371)
          ·
            refine ⟨74153018128774107604581557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49435345419182738403054371 74153018128774107604581557)
            ·
              refine ⟨6951845449572572587929521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74153018128774107604581557 6951845449572572587929521)
              ·
                refine ⟨5213884087179429440947141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6951845449572572587929521 5213884087179429440947141)
                ·
                  refine ⟨977603266346143020177589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5213884087179429440947141 977603266346143020177589)
                  ·
                    refine ⟨91650306219950908141649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 977603266346143020177589 91650306219950908141649)
                    ·
                      rfl

theorem cell23_535465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_535465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535465 prefixEnd_535465 := by exact prefixLift 535465
  have htrace : WordTrace (prefixWord ++ tailWord_535465) baseStart_535465 baseEnd_535465 := by
    simpa [prefixWord, tailWord_535465, baseEnd_535465] using wordTrace_append hprefix tailTrace_535465
  have hstable : (prefixWord ++ tailWord_535465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535465).length < 2 ^ (prefixWord ++ tailWord_535465).sum := by decide
  have hdescent : baseEnd_535465 < baseStart_535465 := by decide
  rcases family_descends (prefixWord ++ tailWord_535465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535482 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_535482 : Nat := 118140960795 + 535482 * 2 ^ 59
def prefixEnd_535482 : Nat := 4983230072969 + 3 ^ 40 * 535482 * 2
def baseEnd_535482 : Nat := 91653215943659719304123

theorem tailTrace_535482 : CollatzResearch.WordTrace tailWord_535482 prefixEnd_535482 91653215943659719304123 := by
  unfold tailWord_535482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4882658261511910472440175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13020422030698427926507133 4882658261511910472440175)
  ·
    refine ⟨7323987392267865708660263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4882658261511910472440175 7323987392267865708660263)
    ·
      refine ⟨10985981088401798562990395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7323987392267865708660263 10985981088401798562990395)
      ·
        refine ⟨16478971632602697844485593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10985981088401798562990395 16478971632602697844485593)
        ·
          refine ⟨12359228724452023383364195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16478971632602697844485593 12359228724452023383364195)
          ·
            refine ⟨18538843086678035075046293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12359228724452023383364195 18538843086678035075046293)
            ·
              refine ⟨869008269688032894142795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18538843086678035075046293 869008269688032894142795)
              ·
                refine ⟨1303512404532049341214193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869008269688032894142795 1303512404532049341214193)
                ·
                  refine ⟨977634303399037005910645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1303512404532049341214193 977634303399037005910645)
                  ·
                    refine ⟨91653215943659719304123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 977634303399037005910645 91653215943659719304123)
                    ·
                      rfl

theorem cell23_535482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_535482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535482 prefixEnd_535482 := by exact prefixLift 535482
  have htrace : WordTrace (prefixWord ++ tailWord_535482) baseStart_535482 baseEnd_535482 := by
    simpa [prefixWord, tailWord_535482, baseEnd_535482] using wordTrace_append hprefix tailTrace_535482
  have hstable : (prefixWord ++ tailWord_535482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535482).length < 2 ^ (prefixWord ++ tailWord_535482).sum := by decide
  have hdescent : baseEnd_535482 < baseStart_535482 := by decide
  rcases family_descends (prefixWord ++ tailWord_535482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535505 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_535505 : Nat := 118140960795 + 535505 * 2 ^ 59
def prefixEnd_535505 : Nat := 4983230072969 + 3 ^ 40 * 535505 * 2
def baseEnd_535505 : Nat := 274971457886032567924763

theorem tailTrace_535505 : CollatzResearch.WordTrace tailWord_535505 prefixEnd_535505 274971457886032567924763 := by
  unfold tailWord_535505
  simp only [CollatzResearch.WordTrace]
  refine ⟨19531471924964316817847969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13020981283309544545231979 19531471924964316817847969)
  ·
    refine ⟨14648603943723237613385977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19531471924964316817847969 14648603943723237613385977)
    ·
      refine ⟨10986452957792428210039483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14648603943723237613385977 10986452957792428210039483)
      ·
        refine ⟨16479679436688642315059225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10986452957792428210039483 16479679436688642315059225)
        ·
          refine ⟨12359759577516481736294419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16479679436688642315059225 12359759577516481736294419)
          ·
            refine ⟨18539639366274722604441629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12359759577516481736294419 18539639366274722604441629)
            ·
              refine ⟨6952364762353020976665611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18539639366274722604441629 6952364762353020976665611)
              ·
                refine ⟨10428547143529531464998417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6952364762353020976665611 10428547143529531464998417)
                ·
                  refine ⟨7821410357647148598748813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10428547143529531464998417 7821410357647148598748813)
                  ·
                    refine ⟨2933028884117680724530805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7821410357647148598748813 2933028884117680724530805)
                    ·
                      refine ⟨274971457886032567924763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2933028884117680724530805 274971457886032567924763)
                      ·
                        rfl

theorem cell23_535505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_535505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535505 prefixEnd_535505 := by exact prefixLift 535505
  have htrace : WordTrace (prefixWord ++ tailWord_535505) baseStart_535505 baseEnd_535505 := by
    simpa [prefixWord, tailWord_535505, baseEnd_535505] using wordTrace_append hprefix tailTrace_535505
  have hstable : (prefixWord ++ tailWord_535505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535505).length < 2 ^ (prefixWord ++ tailWord_535505).sum := by decide
  have hdescent : baseEnd_535505 < baseStart_535505 := by decide
  rcases family_descends (prefixWord ++ tailWord_535505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535562 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_535562 : Nat := 118140960795 + 535562 * 2 ^ 59
def prefixEnd_535562 : Nat := 4983230072969 + 3 ^ 40 * 535562 * 2
def baseEnd_535562 : Nat := 275000726283338844912001

theorem tailTrace_535562 : CollatzResearch.WordTrace tailWord_535562 prefixEnd_535562 275000726283338844912001 := by
  unfold tailWord_535562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4883387721439453888168235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13022367257171877035115293 4883387721439453888168235)
  ·
    refine ⟨7325081582159180832252353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4883387721439453888168235 7325081582159180832252353)
    ·
      refine ⟨5493811186619385624189265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7325081582159180832252353 5493811186619385624189265)
      ·
        refine ⟨4120358389964539218141949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5493811186619385624189265 4120358389964539218141949)
        ·
          refine ⟨1545134396236702206803231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4120358389964539218141949 1545134396236702206803231)
          ·
            refine ⟨2317701594355053310204847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545134396236702206803231 2317701594355053310204847)
            ·
              refine ⟨3476552391532579965307271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317701594355053310204847 3476552391532579965307271)
              ·
                refine ⟨5214828587298869947960907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476552391532579965307271 5214828587298869947960907)
                ·
                  refine ⟨7822242880948304921941361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5214828587298869947960907 7822242880948304921941361)
                  ·
                    refine ⟨5866682160711228691456021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7822242880948304921941361 5866682160711228691456021)
                    ·
                      refine ⟨275000726283338844912001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5866682160711228691456021 275000726283338844912001)
                      ·
                        rfl

theorem cell23_535562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_535562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535562 prefixEnd_535562 := by exact prefixLift 535562
  have htrace : WordTrace (prefixWord ++ tailWord_535562) baseStart_535562 baseEnd_535562 := by
    simpa [prefixWord, tailWord_535562, baseEnd_535562] using wordTrace_append hprefix tailTrace_535562
  have hstable : (prefixWord ++ tailWord_535562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535562).length < 2 ^ (prefixWord ++ tailWord_535562).sum := by decide
  have hdescent : baseEnd_535562 < baseStart_535562 := by decide
  rcases family_descends (prefixWord ++ tailWord_535562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535586 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_535586 : Nat := 118140960795 + 535586 * 2 ^ 59
def prefixEnd_535586 : Nat := 4983230072969 + 3 ^ 40 * 535586 * 2
def baseEnd_535586 : Nat := 275013049819046751011891

theorem tailTrace_535586 : CollatzResearch.WordTrace tailWord_535586 prefixEnd_535586 275013049819046751011891 := by
  unfold tailWord_535586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4883606559417716912886653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13022950825113911767697741 4883606559417716912886653)
  ·
    refine ⟨1831352459781643842332495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4883606559417716912886653 1831352459781643842332495)
    ·
      refine ⟨2747028689672465763498743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1831352459781643842332495 2747028689672465763498743)
      ·
        refine ⟨4120543034508698645248115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747028689672465763498743 4120543034508698645248115)
        ·
          refine ⟨6180814551763047967872173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120543034508698645248115 6180814551763047967872173)
          ·
            refine ⟨2317805456911142987952065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6180814551763047967872173 2317805456911142987952065)
            ·
              refine ⟨1738354092683357240964049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2317805456911142987952065 1738354092683357240964049)
              ·
                refine ⟨1303765569512517930723037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738354092683357240964049 1303765569512517930723037)
                ·
                  refine ⟨488912088567194224021139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1303765569512517930723037 488912088567194224021139)
                  ·
                    refine ⟨733368132850791336031709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 488912088567194224021139 733368132850791336031709)
                    ·
                      refine ⟨275013049819046751011891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 733368132850791336031709 275013049819046751011891)
                      ·
                        rfl

theorem cell23_535586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_535586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535586 prefixEnd_535586 := by exact prefixLift 535586
  have htrace : WordTrace (prefixWord ++ tailWord_535586) baseStart_535586 baseEnd_535586 := by
    simpa [prefixWord, tailWord_535586, baseEnd_535586] using wordTrace_append hprefix tailTrace_535586
  have hstable : (prefixWord ++ tailWord_535586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535586).length < 2 ^ (prefixWord ++ tailWord_535586).sum := by decide
  have hdescent : baseEnd_535586 < baseStart_535586 := by decide
  rcases family_descends (prefixWord ++ tailWord_535586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535589 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_535589 : Nat := 118140960795 + 535589 * 2 ^ 59
def prefixEnd_535589 : Nat := 4983230072969 + 3 ^ 40 * 535589 * 2
def baseEnd_535589 : Nat := 91671530087003413091459

theorem tailTrace_535589 : CollatzResearch.WordTrace tailWord_535589 prefixEnd_535589 91671530087003413091459 := by
  unfold tailWord_535589
  simp only [CollatzResearch.WordTrace]
  refine ⟨19534535656659999163905821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13023023771106666109270547 19534535656659999163905821)
  ·
    refine ⟨7325450871247499686464683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19534535656659999163905821 7325450871247499686464683)
    ·
      refine ⟨10988176306871249529697025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7325450871247499686464683 10988176306871249529697025)
      ·
        refine ⟨8241132230153437147272769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10988176306871249529697025 8241132230153437147272769)
        ·
          refine ⟨6180849172615077860454577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8241132230153437147272769 6180849172615077860454577)
          ·
            refine ⟨4635636879461308395340933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6180849172615077860454577 4635636879461308395340933)
            ·
              refine ⟨869181914898995324126425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4635636879461308395340933 869181914898995324126425)
              ·
                refine ⟨651886436174246493094819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869181914898995324126425 651886436174246493094819)
                ·
                  refine ⟨977829654261369739642229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651886436174246493094819 977829654261369739642229)
                  ·
                    refine ⟨91671530087003413091459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 977829654261369739642229 91671530087003413091459)
                    ·
                      rfl

theorem cell23_535589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_535589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535589 prefixEnd_535589 := by exact prefixLift 535589
  have htrace : WordTrace (prefixWord ++ tailWord_535589) baseStart_535589 baseEnd_535589 := by
    simpa [prefixWord, tailWord_535589, baseEnd_535589] using wordTrace_append hprefix tailTrace_535589
  have hstable : (prefixWord ++ tailWord_535589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535589).length < 2 ^ (prefixWord ++ tailWord_535589).sum := by decide
  have hdescent : baseEnd_535589 < baseStart_535589 := by decide
  rcases family_descends (prefixWord ++ tailWord_535589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535602 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_535602 : Nat := 118140960795 + 535602 * 2 ^ 59
def prefixEnd_535602 : Nat := 4983230072969 + 3 ^ 40 * 535602 * 2
def baseEnd_535602 : Nat := 91673755169839562803939

theorem tailTrace_535602 : CollatzResearch.WordTrace tailWord_535602 prefixEnd_535602 91673755169839562803939 := by
  unfold tailWord_535602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4883752451403225596032265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13023339870408601589419373 4883752451403225596032265)
  ·
    refine ⟨3662814338552419197024199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4883752451403225596032265 3662814338552419197024199)
    ·
      refine ⟨5494221507828628795536299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3662814338552419197024199 5494221507828628795536299)
      ·
        refine ⟨8241332261742943193304449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5494221507828628795536299 8241332261742943193304449)
        ·
          refine ⟨6180999196307207394978337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8241332261742943193304449 6180999196307207394978337)
          ·
            refine ⟨4635749397230405546233753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6180999196307207394978337 4635749397230405546233753)
            ·
              refine ⟨3476812047922804159675315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4635749397230405546233753 3476812047922804159675315)
              ·
                refine ⟨5215218071884206239512973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476812047922804159675315 5215218071884206239512973)
                ·
                  refine ⟨1955706776956577339817365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5215218071884206239512973 1955706776956577339817365)
                  ·
                    refine ⟨91673755169839562803939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1955706776956577339817365 91673755169839562803939)
                    ·
                      rfl

theorem cell23_535602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_535602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535602 prefixEnd_535602 := by exact prefixLift 535602
  have htrace : WordTrace (prefixWord ++ tailWord_535602) baseStart_535602 baseEnd_535602 := by
    simpa [prefixWord, tailWord_535602, baseEnd_535602] using wordTrace_append hprefix tailTrace_535602
  have hstable : (prefixWord ++ tailWord_535602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535602).length < 2 ^ (prefixWord ++ tailWord_535602).sum := by decide
  have hdescent : baseEnd_535602 < baseStart_535602 := by decide
  rcases family_descends (prefixWord ++ tailWord_535602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535606 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_535606 : Nat := 118140960795 + 535606 * 2 ^ 59
def prefixEnd_535606 : Nat := 4983230072969 + 3 ^ 40 * 535606 * 2
def baseEnd_535606 : Nat := 91674439810712224253933

theorem tailTrace_535606 : CollatzResearch.WordTrace tailWord_535606 prefixEnd_535606 91674439810712224253933 := by
  unfold tailWord_535606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220947231099900691704667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13023437131732274044849781 1220947231099900691704667)
  ·
    refine ⟨1831420846649851037557001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1220947231099900691704667 1831420846649851037557001)
    ·
      refine ⟨1373565634987388278167751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1831420846649851037557001 1373565634987388278167751)
      ·
        refine ⟨2060348452481082417251627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1373565634987388278167751 2060348452481082417251627)
        ·
          refine ⟨3090522678721623625877441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060348452481082417251627 3090522678721623625877441)
          ·
            refine ⟨2317892009041217719408081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3090522678721623625877441 2317892009041217719408081)
            ·
              refine ⟨1738419006780913289556061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2317892009041217719408081 1738419006780913289556061)
              ·
                refine ⟨651907127542842483583523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1738419006780913289556061 651907127542842483583523)
                ·
                  refine ⟨977860691314263725375285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651907127542842483583523 977860691314263725375285)
                  ·
                    refine ⟨91674439810712224253933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 977860691314263725375285 91674439810712224253933)
                    ·
                      rfl

theorem cell23_535606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_535606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535606 prefixEnd_535606 := by exact prefixLift 535606
  have htrace : WordTrace (prefixWord ++ tailWord_535606) baseStart_535606 baseEnd_535606 := by
    simpa [prefixWord, tailWord_535606, baseEnd_535606] using wordTrace_append hprefix tailTrace_535606
  have hstable : (prefixWord ++ tailWord_535606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535606).length < 2 ^ (prefixWord ++ tailWord_535606).sum := by decide
  have hdescent : baseEnd_535606 < baseStart_535606 := by decide
  rcases family_descends (prefixWord ++ tailWord_535606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535619 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 2, 4]
def baseStart_535619 : Nat := 118140960795 + 535619 * 2 ^ 59
def prefixEnd_535619 : Nat := 4983230072969 + 3 ^ 40 * 535619 * 2
def baseEnd_535619 : Nat := 91676664893548373966413

theorem tailTrace_535619 : CollatzResearch.WordTrace tailWord_535619 prefixEnd_535619 91676664893548373966413 := by
  unfold tailWord_535619
  simp only [CollatzResearch.WordTrace]
  refine ⟨19535629846551314287497911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13023753231034209524998607 19535629846551314287497911)
  ·
    refine ⟨29303444769826971431246867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19535629846551314287497911 29303444769826971431246867)
    ·
      refine ⟨43955167154740457146870301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29303444769826971431246867 43955167154740457146870301)
      ·
        refine ⟨16483187683027671430076363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43955167154740457146870301 16483187683027671430076363)
        ·
          refine ⟨24724781524541507145114545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16483187683027671430076363 24724781524541507145114545)
          ·
            refine ⟨18543586143406130358835909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24724781524541507145114545 18543586143406130358835909)
            ·
              refine ⟨3476922401888649442281733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18543586143406130358835909 3476922401888649442281733)
              ·
                refine ⟨651922950354121770427825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3476922401888649442281733 651922950354121770427825)
                ·
                  refine ⟨488942212765591327820869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 651922950354121770427825 488942212765591327820869)
                  ·
                    refine ⟨91676664893548373966413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 488942212765591327820869 91676664893548373966413)
                    ·
                      rfl

theorem cell23_535619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 4].length) (baseStart_535619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535619 prefixEnd_535619 := by exact prefixLift 535619
  have htrace : WordTrace (prefixWord ++ tailWord_535619) baseStart_535619 baseEnd_535619 := by
    simpa [prefixWord, tailWord_535619, baseEnd_535619] using wordTrace_append hprefix tailTrace_535619
  have hstable : (prefixWord ++ tailWord_535619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535619).length < 2 ^ (prefixWord ++ tailWord_535619).sum := by decide
  have hdescent : baseEnd_535619 < baseStart_535619 := by decide
  rcases family_descends (prefixWord ++ tailWord_535619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535672 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_535672 : Nat := 118140960795 + 535672 * 2 ^ 59
def prefixEnd_535672 : Nat := 4983230072969 + 3 ^ 40 * 535672 * 2
def baseEnd_535672 : Nat := 275057209155333414536495

theorem tailTrace_535672 : CollatzResearch.WordTrace tailWord_535672 prefixEnd_535672 275057209155333414536495 := by
  unfold tailWord_535672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768781457679652169588635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13025041943572869559451513 9768781457679652169588635)
  ·
    refine ⟨14653172186519478254382953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9768781457679652169588635 14653172186519478254382953)
    ·
      refine ⟨10989879139889608690787215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14653172186519478254382953 10989879139889608690787215)
      ·
        refine ⟨16484818709834413036180823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10989879139889608690787215 16484818709834413036180823)
        ·
          refine ⟨24727228064751619554271235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16484818709834413036180823 24727228064751619554271235)
          ·
            refine ⟨37090842097127429331406853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24727228064751619554271235 37090842097127429331406853)
            ·
              refine ⟨6954532893211392999638785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37090842097127429331406853 6954532893211392999638785)
              ·
                refine ⟨5215899669908544749729089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6954532893211392999638785 5215899669908544749729089)
                ·
                  refine ⟨3911924752431408562296817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5215899669908544749729089 3911924752431408562296817)
                  ·
                    refine ⟨2933943564323556421722613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3911924752431408562296817 2933943564323556421722613)
                    ·
                      refine ⟨275057209155333414536495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2933943564323556421722613 275057209155333414536495)
                      ·
                        rfl

theorem cell23_535672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_535672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535672 prefixEnd_535672 := by exact prefixLift 535672
  have htrace : WordTrace (prefixWord ++ tailWord_535672) baseStart_535672 baseEnd_535672 := by
    simpa [prefixWord, tailWord_535672, baseEnd_535672] using wordTrace_append hprefix tailTrace_535672
  have hstable : (prefixWord ++ tailWord_535672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535672).length < 2 ^ (prefixWord ++ tailWord_535672).sum := by decide
  have hdescent : baseEnd_535672 < baseStart_535672 := by decide
  rcases family_descends (prefixWord ++ tailWord_535672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535769 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 2, 5]
def baseStart_535769 : Nat := 118140960795 + 535769 * 2 ^ 59
def prefixEnd_535769 : Nat := 4983230072969 + 3 ^ 40 * 535769 * 2
def baseEnd_535769 : Nat := 91702338926273178341183

theorem tailTrace_535769 : CollatzResearch.WordTrace tailWord_535769 prefixEnd_535769 91702338926273178341183 := by
  unfold tailWord_535769
  simp only [CollatzResearch.WordTrace]
  refine ⟨19541100796007889905458361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13027400530671926603638907 19541100796007889905458361)
  ·
    refine ⟨14655825597005917429093771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19541100796007889905458361 14655825597005917429093771)
    ·
      refine ⟨21983738395508876143640657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14655825597005917429093771 21983738395508876143640657)
      ·
        refine ⟨16487803796631657107730493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21983738395508876143640657 16487803796631657107730493)
        ·
          refine ⟨6182926423736871415398935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16487803796631657107730493 6182926423736871415398935)
          ·
            refine ⟨9274389635605307123098403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6182926423736871415398935 9274389635605307123098403)
            ·
              refine ⟨13911584453407960684647605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9274389635605307123098403 13911584453407960684647605)
              ·
                refine ⟨1304211042506996314185713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13911584453407960684647605 1304211042506996314185713)
                ·
                  refine ⟨978158281880247235639285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1304211042506996314185713 978158281880247235639285)
                  ·
                    refine ⟨91702338926273178341183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 978158281880247235639285 91702338926273178341183)
                    ·
                      rfl

theorem cell23_535769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_535769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535769 prefixEnd_535769 := by exact prefixLift 535769
  have htrace : WordTrace (prefixWord ++ tailWord_535769) baseStart_535769 baseEnd_535769 := by
    simpa [prefixWord, tailWord_535769, baseEnd_535769] using wordTrace_append hprefix tailTrace_535769
  have hstable : (prefixWord ++ tailWord_535769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535769).length < 2 ^ (prefixWord ++ tailWord_535769).sum := by decide
  have hdescent : baseEnd_535769 < baseStart_535769 := by decide
  rcases family_descends (prefixWord ++ tailWord_535769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535786 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_535786 : Nat := 118140960795 + 535786 * 2 ^ 59
def prefixEnd_535786 : Nat := 4983230072969 + 3 ^ 40 * 535786 * 2
def baseEnd_535786 : Nat := 91705248649981989503657

theorem tailTrace_535786 : CollatzResearch.WordTrace tailWord_535786 prefixEnd_535786 91705248649981989503657 := by
  unfold tailWord_535786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885430209236575452206803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13027813891297534539218141 4885430209236575452206803)
  ·
    refine ⟨7328145313854863178310205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4885430209236575452206803 7328145313854863178310205)
    ·
      refine ⟨2748054492695573691866327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7328145313854863178310205 2748054492695573691866327)
      ·
        refine ⟨4122081739043360537799491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2748054492695573691866327 4122081739043360537799491)
        ·
          refine ⟨6183122608565040806699237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4122081739043360537799491 6183122608565040806699237)
          ·
            refine ⟨1159335489105945151256107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6183122608565040806699237 1159335489105945151256107)
            ·
              refine ⟨1739003233658917726884161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159335489105945151256107 1739003233658917726884161)
              ·
                refine ⟨1304252425244188295163121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1739003233658917726884161 1304252425244188295163121)
                ·
                  refine ⟨978189318933141221372341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1304252425244188295163121 978189318933141221372341)
                  ·
                    refine ⟨91705248649981989503657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 978189318933141221372341 91705248649981989503657)
                    ·
                      rfl

theorem cell23_535786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_535786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535786 prefixEnd_535786 := by exact prefixLift 535786
  have htrace : WordTrace (prefixWord ++ tailWord_535786) baseStart_535786 baseEnd_535786 := by
    simpa [prefixWord, tailWord_535786, baseEnd_535786] using wordTrace_append hprefix tailTrace_535786
  have hstable : (prefixWord ++ tailWord_535786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535786).length < 2 ^ (prefixWord ++ tailWord_535786).sum := by decide
  have hdescent : baseEnd_535786 < baseStart_535786 := by decide
  rcases family_descends (prefixWord ++ tailWord_535786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535893 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_535893 : Nat := 118140960795 + 535893 * 2 ^ 59
def prefixEnd_535893 : Nat := 4983230072969 + 3 ^ 40 * 535893 * 2
def baseEnd_535893 : Nat := 91723562793325683290993

theorem tailTrace_535893 : CollatzResearch.WordTrace tailWord_535893 prefixEnd_535893 91723562793325683290993 := by
  unfold tailWord_535893
  simp only [CollatzResearch.WordTrace]
  refine ⟨19545623447558659082972333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13030415631705772721981555 19545623447558659082972333)
  ·
    refine ⟨7329608792834497156114625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19545623447558659082972333 7329608792834497156114625)
    ·
      refine ⟨5497206594625872867085969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7329608792834497156114625 5497206594625872867085969)
      ·
        refine ⟨4122904945969404650314477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5497206594625872867085969 4122904945969404650314477)
        ·
          refine ⟨1546089354738526743867929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4122904945969404650314477 1546089354738526743867929)
          ·
            refine ⟨1159567016053895057900947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1546089354738526743867929 1159567016053895057900947)
            ·
              refine ⟨1739350524080842586851421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159567016053895057900947 1739350524080842586851421)
              ·
                refine ⟨652256446530315970069283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1739350524080842586851421 652256446530315970069283)
                ·
                  refine ⟨978384669795473955103925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652256446530315970069283 978384669795473955103925)
                  ·
                    refine ⟨91723562793325683290993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 978384669795473955103925 91723562793325683290993)
                    ·
                      rfl

theorem cell23_535893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_535893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535893 prefixEnd_535893 := by exact prefixLift 535893
  have htrace : WordTrace (prefixWord ++ tailWord_535893) baseStart_535893 baseEnd_535893 := by
    simpa [prefixWord, tailWord_535893, baseEnd_535893] using wordTrace_append hprefix tailTrace_535893
  have hstable : (prefixWord ++ tailWord_535893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535893).length < 2 ^ (prefixWord ++ tailWord_535893).sum := by decide
  have hdescent : baseEnd_535893 < baseStart_535893 := by decide
  rcases family_descends (prefixWord ++ tailWord_535893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535916 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_535916 : Nat := 118140960795 + 535916 * 2 ^ 59
def prefixEnd_535916 : Nat := 4983230072969 + 3 ^ 40 * 535916 * 2
def baseEnd_535916 : Nat := 275182498435030459885373

theorem tailTrace_535916 : CollatzResearch.WordTrace tailWord_535916 prefixEnd_535916 275182498435030459885373 := by
  unfold tailWord_535916
  simp only [CollatzResearch.WordTrace]
  refine ⟨9773231163237667005529801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13030974884316889340706401 9773231163237667005529801)
  ·
    refine ⟨7329923372428250254147351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9773231163237667005529801 7329923372428250254147351)
    ·
      refine ⟨10994885058642375381221027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7329923372428250254147351 10994885058642375381221027)
      ·
        refine ⟨16492327587963563071831541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10994885058642375381221027 16492327587963563071831541)
        ·
          refine ⟨1546155711371584037984207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16492327587963563071831541 1546155711371584037984207)
          ·
            refine ⟨2319233567057376056976311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546155711371584037984207 2319233567057376056976311)
            ·
              refine ⟨3478850350586064085464467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2319233567057376056976311 3478850350586064085464467)
              ·
                refine ⟨5218275525879096128196701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478850350586064085464467 5218275525879096128196701)
                ·
                  refine ⟨1956853322204661048073763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5218275525879096128196701 1956853322204661048073763)
                  ·
                    refine ⟨2935279983306991572110645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1956853322204661048073763 2935279983306991572110645)
                    ·
                      refine ⟨275182498435030459885373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2935279983306991572110645 275182498435030459885373)
                      ·
                        rfl

theorem cell23_535916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_535916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535916 prefixEnd_535916 := by exact prefixLift 535916
  have htrace : WordTrace (prefixWord ++ tailWord_535916) baseStart_535916 baseEnd_535916 := by
    simpa [prefixWord, tailWord_535916, baseEnd_535916] using wordTrace_append hprefix tailTrace_535916
  have hstable : (prefixWord ++ tailWord_535916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535916).length < 2 ^ (prefixWord ++ tailWord_535916).sum := by decide
  have hdescent : baseEnd_535916 < baseStart_535916 := by decide
  rcases family_descends (prefixWord ++ tailWord_535916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535919 : List Nat := [1, 1, 2, 1, 3, 1, 4, 10]
def baseStart_535919 : Nat := 118140960795 + 535919 * 2 ^ 59
def prefixEnd_535919 : Nat := 4983230072969 + 3 ^ 40 * 535919 * 2
def baseEnd_535919 : Nat := 10192001439888664746217

theorem tailTrace_535919 : CollatzResearch.WordTrace tailWord_535919 prefixEnd_535919 10192001439888664746217 := by
  unfold tailWord_535919
  simp only [CollatzResearch.WordTrace]
  refine ⟨19546571745464465523418811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13031047830309643682279207 19546571745464465523418811)
  ·
    refine ⟨29319857618196698285128217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19546571745464465523418811 29319857618196698285128217)
    ·
      refine ⟨21989893213647523713846163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29319857618196698285128217 21989893213647523713846163)
      ·
        refine ⟨32984839820471285570769245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21989893213647523713846163 32984839820471285570769245)
        ·
          refine ⟨12369314932676732089038467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32984839820471285570769245 12369314932676732089038467)
          ·
            refine ⟨18553972399015098133557701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12369314932676732089038467 18553972399015098133557701)
            ·
              refine ⟨3478869824815330900042069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18553972399015098133557701 3478869824815330900042069)
              ·
                refine ⟨10192001439888664746217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3478869824815330900042069 10192001439888664746217)
                ·
                  rfl

theorem cell23_535919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 10].length) (baseStart_535919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535919 prefixEnd_535919 := by exact prefixLift 535919
  have htrace : WordTrace (prefixWord ++ tailWord_535919) baseStart_535919 baseEnd_535919 := by
    simpa [prefixWord, tailWord_535919, baseEnd_535919] using wordTrace_append hprefix tailTrace_535919
  have hstable : (prefixWord ++ tailWord_535919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535919).length < 2 ^ (prefixWord ++ tailWord_535919).sum := by decide
  have hdescent : baseEnd_535919 < baseStart_535919 := by decide
  rcases family_descends (prefixWord ++ tailWord_535919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535950 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_535950 : Nat := 118140960795 + 535950 * 2 ^ 59
def prefixEnd_535950 : Nat := 4983230072969 + 3 ^ 40 * 535950 * 2
def baseEnd_535950 : Nat := 275199956777283326860217

theorem tailTrace_535950 : CollatzResearch.WordTrace tailWord_535950 prefixEnd_535950 275199956777283326860217 := by
  unfold tailWord_535950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2443462801044019727224663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13031801605568105211864869 2443462801044019727224663)
  ·
    refine ⟨3665194201566029590836995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2443462801044019727224663 3665194201566029590836995)
    ·
      refine ⟨5497791302349044386255493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3665194201566029590836995 5497791302349044386255493)
      ·
        refine ⟨1030835869190445822422905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5497791302349044386255493 1030835869190445822422905)
        ·
          refine ⟨773126901892834366817179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030835869190445822422905 773126901892834366817179)
          ·
            refine ⟨1159690352839251550225769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773126901892834366817179 1159690352839251550225769)
            ·
              refine ⟨869767764629438662669327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159690352839251550225769 869767764629438662669327)
              ·
                refine ⟨1304651646944157994003991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869767764629438662669327 1304651646944157994003991)
                ·
                  refine ⟨1956977470416236991005987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304651646944157994003991 1956977470416236991005987)
                  ·
                    refine ⟨2935466205624355486508981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1956977470416236991005987 2935466205624355486508981)
                    ·
                      refine ⟨275199956777283326860217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2935466205624355486508981 275199956777283326860217)
                      ·
                        rfl

theorem cell23_535950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_535950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535950 prefixEnd_535950 := by exact prefixLift 535950
  have htrace : WordTrace (prefixWord ++ tailWord_535950) baseStart_535950 baseEnd_535950 := by
    simpa [prefixWord, tailWord_535950, baseEnd_535950] using wordTrace_append hprefix tailTrace_535950
  have hstable : (prefixWord ++ tailWord_535950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535950).length < 2 ^ (prefixWord ++ tailWord_535950).sum := by decide
  have hdescent : baseEnd_535950 < baseStart_535950 := by decide
  rcases family_descends (prefixWord ++ tailWord_535950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535986 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_535986 : Nat := 118140960795 + 535986 * 2 ^ 59
def prefixEnd_535986 : Nat := 4983230072969 + 3 ^ 40 * 535986 * 2
def baseEnd_535986 : Nat := 275218442080845186010051

theorem tailTrace_535986 : CollatzResearch.WordTrace tailWord_535986 prefixEnd_535986 275218442080845186010051 := by
  unfold tailWord_535986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4887253859055433991526953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13032676957481157310738541 4887253859055433991526953)
  ·
    refine ⟨3665440394291575493645215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4887253859055433991526953 3665440394291575493645215)
    ·
      refine ⟨5498160591437363240467823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3665440394291575493645215 5498160591437363240467823)
      ·
        refine ⟨8247240887156044860701735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5498160591437363240467823 8247240887156044860701735)
        ·
          refine ⟨12370861330734067291052603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8247240887156044860701735 12370861330734067291052603)
          ·
            refine ⟨18556291996101100936578905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12370861330734067291052603 18556291996101100936578905)
            ·
              refine ⟨13917218997075825702434179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18556291996101100936578905 13917218997075825702434179)
              ·
                refine ⟨20875828495613738553651269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13917218997075825702434179 20875828495613738553651269)
                ·
                  refine ⟨3914217842927575978809613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20875828495613738553651269 3914217842927575978809613)
                  ·
                    refine ⟨1467831691097840992053605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3914217842927575978809613 1467831691097840992053605)
                    ·
                      refine ⟨275218442080845186010051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1467831691097840992053605 275218442080845186010051)
                      ·
                        rfl

theorem cell23_535986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_535986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_535986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_535986 prefixEnd_535986 := by exact prefixLift 535986
  have htrace : WordTrace (prefixWord ++ tailWord_535986) baseStart_535986 baseEnd_535986 := by
    simpa [prefixWord, tailWord_535986, baseEnd_535986] using wordTrace_append hprefix tailTrace_535986
  have hstable : (prefixWord ++ tailWord_535986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535986).length < 2 ^ (prefixWord ++ tailWord_535986).sum := by decide
  have hdescent : baseEnd_535986 < baseStart_535986 := by decide
  rcases family_descends (prefixWord ++ tailWord_535986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536003 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 3, 4, 2]
def baseStart_536003 : Nat := 118140960795 + 536003 * 2 ^ 59
def prefixEnd_536003 : Nat := 4983230072969 + 3 ^ 40 * 536003 * 2
def baseEnd_536003 : Nat := 275227171251971619497473

theorem tailTrace_536003 : CollatzResearch.WordTrace tailWord_536003 prefixEnd_536003 275227171251971619497473 := by
  unfold tailWord_536003
  simp only [CollatzResearch.WordTrace]
  refine ⟨19549635477160147869476663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13033090318106765246317775 19549635477160147869476663)
  ·
    refine ⟨29324453215740221804214995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19549635477160147869476663 29324453215740221804214995)
    ·
      refine ⟨43986679823610332706322493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29324453215740221804214995 43986679823610332706322493)
      ·
        refine ⟨16495004933853874764870935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43986679823610332706322493 16495004933853874764870935)
        ·
          refine ⟨24742507400780812147306403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16495004933853874764870935 24742507400780812147306403)
          ·
            refine ⟨37113761101171218220959605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24742507400780812147306403 37113761101171218220959605)
            ·
              refine ⟨3479415103234801708214963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37113761101171218220959605 3479415103234801708214963)
              ·
                refine ⟨5219122654852202562322445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479415103234801708214963 5219122654852202562322445)
                ·
                  refine ⟨1957170995569575960870917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5219122654852202562322445 1957170995569575960870917)
                  ·
                    refine ⟨366969561669295492663297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1957170995569575960870917 366969561669295492663297)
                    ·
                      refine ⟨275227171251971619497473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366969561669295492663297 275227171251971619497473)
                      ·
                        rfl

theorem cell23_536003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_536003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536003 prefixEnd_536003 := by exact prefixLift 536003
  have htrace : WordTrace (prefixWord ++ tailWord_536003) baseStart_536003 baseEnd_536003 := by
    simpa [prefixWord, tailWord_536003, baseEnd_536003] using wordTrace_append hprefix tailTrace_536003
  have hstable : (prefixWord ++ tailWord_536003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536003).length < 2 ^ (prefixWord ++ tailWord_536003).sum := by decide
  have hdescent : baseEnd_536003 < baseStart_536003 := by decide
  rcases family_descends (prefixWord ++ tailWord_536003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536007 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 1, 3, 2]
def baseStart_536007 : Nat := 118140960795 + 536007 * 2 ^ 59
def prefixEnd_536007 : Nat := 4983230072969 + 3 ^ 40 * 536007 * 2
def baseEnd_536007 : Nat := 275229225174589603847455

theorem tailTrace_536007 : CollatzResearch.WordTrace tailWord_536007 prefixEnd_536007 275229225174589603847455 := by
  unfold tailWord_536007
  simp only [CollatzResearch.WordTrace]
  refine ⟨19549781369145656552622275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13033187579430437701748183 19549781369145656552622275)
  ·
    refine ⟨29324672053718484828933413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19549781369145656552622275 29324672053718484828933413)
    ·
      refine ⟨5498376010072215905425015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29324672053718484828933413 5498376010072215905425015)
      ·
        refine ⟨8247564015108323858137523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5498376010072215905425015 8247564015108323858137523)
        ·
          refine ⟨12371346022662485787206285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8247564015108323858137523 12371346022662485787206285)
          ·
            refine ⟨4639254758498432170202357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12371346022662485787206285 4639254758498432170202357)
            ·
              refine ⟨434930133609228015956471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4639254758498432170202357 434930133609228015956471)
              ·
                refine ⟨652395200413842023934707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434930133609228015956471 652395200413842023934707)
                ·
                  refine ⟨978592800620763035902061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652395200413842023934707 978592800620763035902061)
                  ·
                    refine ⟨366972300232786138463273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978592800620763035902061 366972300232786138463273)
                    ·
                      refine ⟨275229225174589603847455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366972300232786138463273 275229225174589603847455)
                      ·
                        rfl

theorem cell23_536007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_536007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536007 prefixEnd_536007 := by exact prefixLift 536007
  have htrace : WordTrace (prefixWord ++ tailWord_536007) baseStart_536007 baseEnd_536007 := by
    simpa [prefixWord, tailWord_536007, baseEnd_536007] using wordTrace_append hprefix tailTrace_536007
  have hstable : (prefixWord ++ tailWord_536007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536007).length < 2 ^ (prefixWord ++ tailWord_536007).sum := by decide
  have hdescent : baseEnd_536007 < baseStart_536007 := by decide
  rcases family_descends (prefixWord ++ tailWord_536007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536016 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_536016 : Nat := 118140960795 + 536016 * 2 ^ 59
def prefixEnd_536016 : Nat := 4983230072969 + 3 ^ 40 * 536016 * 2
def baseEnd_536016 : Nat := 275233846500480068634913

theorem tailTrace_536016 : CollatzResearch.WordTrace tailWord_536016 prefixEnd_536016 275233846500480068634913 := by
  unfold tailWord_536016
  simp only [CollatzResearch.WordTrace]
  refine ⟨9775054813056525544849951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13033406417408700726466601 9775054813056525544849951)
  ·
    refine ⟨14662582219584788317274927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9775054813056525544849951 14662582219584788317274927)
    ·
      refine ⟨21993873329377182475912391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14662582219584788317274927 21993873329377182475912391)
      ·
        refine ⟨32990809994065773713868587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21993873329377182475912391 32990809994065773713868587)
        ·
          refine ⟨49486214991098660570802881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32990809994065773713868587 49486214991098660570802881)
          ·
            refine ⟨37114661243323995428102161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49486214991098660570802881 37114661243323995428102161)
            ·
              refine ⟨27835995932492996571076621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37114661243323995428102161 27835995932492996571076621)
              ·
                refine ⟨10438498474684873714153733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27835995932492996571076621 10438498474684873714153733)
                ·
                  refine ⟨1957218464003413821403825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10438498474684873714153733 1957218464003413821403825)
                  ·
                    refine ⟨1467913848002560366052869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1957218464003413821403825 1467913848002560366052869)
                    ·
                      refine ⟨275233846500480068634913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1467913848002560366052869 275233846500480068634913)
                      ·
                        rfl

theorem cell23_536016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_536016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536016 prefixEnd_536016 := by exact prefixLift 536016
  have htrace : WordTrace (prefixWord ++ tailWord_536016) baseStart_536016 baseEnd_536016 := by
    simpa [prefixWord, tailWord_536016, baseEnd_536016] using wordTrace_append hprefix tailTrace_536016
  have hstable : (prefixWord ++ tailWord_536016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536016).length < 2 ^ (prefixWord ++ tailWord_536016).sum := by decide
  have hdescent : baseEnd_536016 < baseStart_536016 := by decide
  rcases family_descends (prefixWord ++ tailWord_536016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536033 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_536033 : Nat := 118140960795 + 536033 * 2 ^ 59
def prefixEnd_536033 : Nat := 4983230072969 + 3 ^ 40 * 536033 * 2
def baseEnd_536033 : Nat := 275242575671606502122335

theorem tailTrace_536033 : CollatzResearch.WordTrace tailWord_536033 prefixEnd_536033 275242575671606502122335 := by
  unfold tailWord_536033
  simp only [CollatzResearch.WordTrace]
  refine ⟨19550729667051462993068753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13033819778034308662045835 19550729667051462993068753)
  ·
    refine ⟨14663047250288597244801565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19550729667051462993068753 14663047250288597244801565)
    ·
      refine ⟨5498642718858223966800587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14663047250288597244801565 5498642718858223966800587)
      ·
        refine ⟨8247964078287335950200881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5498642718858223966800587 8247964078287335950200881)
        ·
          refine ⟨6185973058715501962650661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8247964078287335950200881 6185973058715501962650661)
          ·
            refine ⟨1159869948509156617996999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6185973058715501962650661 1159869948509156617996999)
            ·
              refine ⟨1739804922763734926995499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159869948509156617996999 1739804922763734926995499)
              ·
                refine ⟨2609707384145602390493249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739804922763734926995499 2609707384145602390493249)
                ·
                  refine ⟨1957280538109201792869937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2609707384145602390493249 1957280538109201792869937)
                  ·
                    refine ⟨1467960403581901344652453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1957280538109201792869937 1467960403581901344652453)
                    ·
                      refine ⟨275242575671606502122335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1467960403581901344652453 275242575671606502122335)
                      ·
                        rfl

theorem cell23_536033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_536033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536033 prefixEnd_536033 := by exact prefixLift 536033
  have htrace : WordTrace (prefixWord ++ tailWord_536033) baseStart_536033 baseEnd_536033 := by
    simpa [prefixWord, tailWord_536033, baseEnd_536033] using wordTrace_append hprefix tailTrace_536033
  have hstable : (prefixWord ++ tailWord_536033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536033).length < 2 ^ (prefixWord ++ tailWord_536033).sum := by decide
  have hdescent : baseEnd_536033 < baseStart_536033 := by decide
  rcases family_descends (prefixWord ++ tailWord_536033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536037 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 1, 4, 2]
def baseStart_536037 : Nat := 118140960795 + 536037 * 2 ^ 59
def prefixEnd_536037 : Nat := 4983230072969 + 3 ^ 40 * 536037 * 2
def baseEnd_536037 : Nat := 275244629594224486472317

theorem tailTrace_536037 : CollatzResearch.WordTrace tailWord_536037 prefixEnd_536037 275244629594224486472317 := by
  unfold tailWord_536037
  simp only [CollatzResearch.WordTrace]
  refine ⟨19550875559036971676214365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13033917039357981117476243 19550875559036971676214365)
  ·
    refine ⟨7331578334638864378580387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19550875559036971676214365 7331578334638864378580387)
    ·
      refine ⟨10997367501958296567870581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7331578334638864378580387 10997367501958296567870581)
      ·
        refine ⟨1031003203308590303237867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10997367501958296567870581 1031003203308590303237867)
        ·
          refine ⟨1546504804962885454856801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031003203308590303237867 1546504804962885454856801)
          ·
            refine ⟨1159878603722164091142601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1546504804962885454856801 1159878603722164091142601)
            ·
              refine ⟨869908952791623068356951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159878603722164091142601 869908952791623068356951)
              ·
                refine ⟨1304863429187434602535427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869908952791623068356951 1304863429187434602535427)
                ·
                  refine ⟨1957295143781151903803141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304863429187434602535427 1957295143781151903803141)
                  ·
                    refine ⟨366992839458965981963089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1957295143781151903803141 366992839458965981963089)
                    ·
                      refine ⟨275244629594224486472317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 366992839458965981963089 275244629594224486472317)
                      ·
                        rfl

theorem cell23_536037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_536037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536037 prefixEnd_536037 := by exact prefixLift 536037
  have htrace : WordTrace (prefixWord ++ tailWord_536037) baseStart_536037 baseEnd_536037 := by
    simpa [prefixWord, tailWord_536037, baseEnd_536037] using wordTrace_append hprefix tailTrace_536037
  have hstable : (prefixWord ++ tailWord_536037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536037).length < 2 ^ (prefixWord ++ tailWord_536037).sum := by decide
  have hdescent : baseEnd_536037 < baseStart_536037 := by decide
  rcases family_descends (prefixWord ++ tailWord_536037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536063 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 1, 7, 2]
def baseStart_536063 : Nat := 118140960795 + 536063 * 2 ^ 59
def prefixEnd_536063 : Nat := 4983230072969 + 3 ^ 40 * 536063 * 2
def baseEnd_536063 : Nat := 275257980091241384747197

theorem tailTrace_536063 : CollatzResearch.WordTrace tailWord_536063 prefixEnd_536063 275257980091241384747197 := by
  unfold tailWord_536063
  simp only [CollatzResearch.WordTrace]
  refine ⟨19551823856942778116660843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13034549237961852077773895 19551823856942778116660843)
  ·
    refine ⟨29327735785414167174991265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19551823856942778116660843 29327735785414167174991265)
    ·
      refine ⟨21995801839060625381243449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29327735785414167174991265 21995801839060625381243449)
      ·
        refine ⟨16496851379295469035932587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21995801839060625381243449 16496851379295469035932587)
        ·
          refine ⟨24745277068943203553898881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16496851379295469035932587 24745277068943203553898881)
          ·
            refine ⟨18558957801707402665424161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24745277068943203553898881 18558957801707402665424161)
            ·
              refine ⟨13919218351280551999068121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18558957801707402665424161 13919218351280551999068121)
              ·
                refine ⟨10439413763460413999301091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13919218351280551999068121 10439413763460413999301091)
                ·
                  refine ⟨15659120645190620998951637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10439413763460413999301091 15659120645190620998951637)
                  ·
                    refine ⟨367010640121655179662929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15659120645190620998951637 367010640121655179662929)
                    ·
                      refine ⟨275257980091241384747197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 367010640121655179662929 275257980091241384747197)
                      ·
                        rfl

theorem cell23_536063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_536063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536063 prefixEnd_536063 := by exact prefixLift 536063
  have htrace : WordTrace (prefixWord ++ tailWord_536063) baseStart_536063 baseEnd_536063 := by
    simpa [prefixWord, tailWord_536063, baseEnd_536063] using wordTrace_append hprefix tailTrace_536063
  have hstable : (prefixWord ++ tailWord_536063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536063).length < 2 ^ (prefixWord ++ tailWord_536063).sum := by decide
  have hdescent : baseEnd_536063 < baseStart_536063 := by decide
  rcases family_descends (prefixWord ++ tailWord_536063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536093 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_536093 : Nat := 118140960795 + 536093 * 2 ^ 59
def prefixEnd_536093 : Nat := 4983230072969 + 3 ^ 40 * 536093 * 2
def baseEnd_536093 : Nat := 275273384510876267372059

theorem tailTrace_536093 : CollatzResearch.WordTrace tailWord_536093 prefixEnd_536093 275273384510876267372059 := by
  unfold tailWord_536093
  simp only [CollatzResearch.WordTrace]
  refine ⟨19552918046834093240252933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13035278697889395493501955 19552918046834093240252933)
  ·
    refine ⟨3666172133781392482547425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19552918046834093240252933 3666172133781392482547425)
    ·
      refine ⟨2749629100336044361910569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3666172133781392482547425 2749629100336044361910569)
      ·
        refine ⟨2062221825252033271432927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2749629100336044361910569 2062221825252033271432927)
        ·
          refine ⟨3093332737878049907149391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062221825252033271432927 3093332737878049907149391)
          ·
            refine ⟨4639999106817074860724087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093332737878049907149391 4639999106817074860724087)
            ·
              refine ⟨6959998660225612291086131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4639999106817074860724087 6959998660225612291086131)
              ·
                refine ⟨10439997990338418436629197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6959998660225612291086131 10439997990338418436629197)
                ·
                  refine ⟨3914999246376906913735949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10439997990338418436629197 3914999246376906913735949)
                  ·
                    refine ⟨1468124717391340092650981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3914999246376906913735949 1468124717391340092650981)
                    ·
                      refine ⟨275273384510876267372059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1468124717391340092650981 275273384510876267372059)
                      ·
                        rfl

theorem cell23_536093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_536093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536093 prefixEnd_536093 := by exact prefixLift 536093
  have htrace : WordTrace (prefixWord ++ tailWord_536093) baseStart_536093 baseEnd_536093 := by
    simpa [prefixWord, tailWord_536093, baseEnd_536093] using wordTrace_append hprefix tailTrace_536093
  have hstable : (prefixWord ++ tailWord_536093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536093).length < 2 ^ (prefixWord ++ tailWord_536093).sum := by decide
  have hdescent : baseEnd_536093 < baseStart_536093 := by decide
  rcases family_descends (prefixWord ++ tailWord_536093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536110 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_536110 : Nat := 118140960795 + 536110 * 2 ^ 59
def prefixEnd_536110 : Nat := 4983230072969 + 3 ^ 40 * 536110 * 2
def baseEnd_536110 : Nat := 275282113682002700859481

theorem tailTrace_536110 : CollatzResearch.WordTrace tailWord_536110 prefixEnd_536110 275282113682002700859481 := by
  unfold tailWord_536110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2444192260971563142952723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13035692058515003429081189 2444192260971563142952723)
  ·
    refine ⟨3666288391457344714429085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2444192260971563142952723 3666288391457344714429085)
    ·
      refine ⟨1374858146796504267910907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3666288391457344714429085 1374858146796504267910907)
      ·
        refine ⟨2062287220194756401866361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1374858146796504267910907 2062287220194756401866361)
        ·
          refine ⟨1546715415146067301399771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2062287220194756401866361 1546715415146067301399771)
          ·
            refine ⟨2320073122719100952099657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546715415146067301399771 2320073122719100952099657)
            ·
              refine ⟨1740054842039325714074743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2320073122719100952099657 1740054842039325714074743)
              ·
                refine ⟨2610082263058988571112115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740054842039325714074743 2610082263058988571112115)
                ·
                  refine ⟨3915123394588482856668173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2610082263058988571112115 3915123394588482856668173)
                  ·
                    refine ⟨1468171272970681071250565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3915123394588482856668173 1468171272970681071250565)
                    ·
                      refine ⟨275282113682002700859481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1468171272970681071250565 275282113682002700859481)
                      ·
                        rfl

theorem cell23_536110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_536110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536110 prefixEnd_536110 := by exact prefixLift 536110
  have htrace : WordTrace (prefixWord ++ tailWord_536110) baseStart_536110 baseEnd_536110 := by
    simpa [prefixWord, tailWord_536110, baseEnd_536110] using wordTrace_append hprefix tailTrace_536110
  have hstable : (prefixWord ++ tailWord_536110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536110).length < 2 ^ (prefixWord ++ tailWord_536110).sum := by decide
  have hdescent : baseEnd_536110 < baseStart_536110 := by decide
  rcases family_descends (prefixWord ++ tailWord_536110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536133 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 6]
def baseStart_536133 : Nat := 118140960795 + 536133 * 2 ^ 59
def prefixEnd_536133 : Nat := 4983230072969 + 3 ^ 40 * 536133 * 2
def baseEnd_536133 : Nat := 30588213748561790096875

theorem tailTrace_536133 : CollatzResearch.WordTrace tailWord_536133 prefixEnd_536133 30588213748561790096875 := by
  unfold tailWord_536133
  simp only [CollatzResearch.WordTrace]
  refine ⟨19554376966689180071709053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13036251311126120047806035 19554376966689180071709053)
  ·
    refine ⟨7332891362508442526890895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19554376966689180071709053 7332891362508442526890895)
    ·
      refine ⟨10999337043762663790336343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7332891362508442526890895 10999337043762663790336343)
      ·
        refine ⟨16499005565643995685504515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10999337043762663790336343 16499005565643995685504515)
        ·
          refine ⟨24748508348465993528256773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16499005565643995685504515 24748508348465993528256773)
          ·
            refine ⟨4640345315337373786548145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24748508348465993528256773 4640345315337373786548145)
            ·
              refine ⟨3480258986503030339911109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4640345315337373786548145 3480258986503030339911109)
              ·
                refine ⟨652548559969318188733333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3480258986503030339911109 652548559969318188733333)
                ·
                  refine ⟨30588213748561790096875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 652548559969318188733333 30588213748561790096875)
                  ·
                    rfl

theorem cell23_536133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_536133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536133 prefixEnd_536133 := by exact prefixLift 536133
  have htrace : WordTrace (prefixWord ++ tailWord_536133) baseStart_536133 baseEnd_536133 := by
    simpa [prefixWord, tailWord_536133, baseEnd_536133] using wordTrace_append hprefix tailTrace_536133
  have hstable : (prefixWord ++ tailWord_536133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536133).length < 2 ^ (prefixWord ++ tailWord_536133).sum := by decide
  have hdescent : baseEnd_536133 < baseStart_536133 := by decide
  rcases family_descends (prefixWord ++ tailWord_536133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536160 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 5, 1, 3]
def baseStart_536160 : Nat := 118140960795 + 536160 * 2 ^ 59
def prefixEnd_536160 : Nat := 4983230072969 + 3 ^ 40 * 536160 * 2
def baseEnd_536160 : Nat := 275307787714727505234251

theorem tailTrace_536160 : CollatzResearch.WordTrace tailWord_536160 prefixEnd_536160 275307787714727505234251 := by
  unfold tailWord_536160
  simp only [CollatzResearch.WordTrace]
  refine ⟨9777680868795681841470967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13036907825060909121961289 9777680868795681841470967)
  ·
    refine ⟨14666521303193522762206451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9777680868795681841470967 14666521303193522762206451)
    ·
      refine ⟨21999781954790284143309677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14666521303193522762206451 21999781954790284143309677)
      ·
        refine ⟨8249918233046356553741129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21999781954790284143309677 8249918233046356553741129)
        ·
          refine ⟨6187438674784767415305847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8249918233046356553741129 6187438674784767415305847)
          ·
            refine ⟨9281158012177151122958771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6187438674784767415305847 9281158012177151122958771)
            ·
              refine ⟨13921737018265726684438157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9281158012177151122958771 13921737018265726684438157)
              ·
                refine ⟨5220651381849647506664309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13921737018265726684438157 5220651381849647506664309)
                ·
                  refine ⟨489436067048404453749779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5220651381849647506664309 489436067048404453749779)
                  ·
                    refine ⟨734154100572606680624669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 489436067048404453749779 734154100572606680624669)
                    ·
                      refine ⟨275307787714727505234251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 734154100572606680624669 275307787714727505234251)
                      ·
                        rfl

theorem cell23_536160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_536160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536160 prefixEnd_536160 := by exact prefixLift 536160
  have htrace : WordTrace (prefixWord ++ tailWord_536160) baseStart_536160 baseEnd_536160 := by
    simpa [prefixWord, tailWord_536160, baseEnd_536160] using wordTrace_append hprefix tailTrace_536160
  have hstable : (prefixWord ++ tailWord_536160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536160).length < 2 ^ (prefixWord ++ tailWord_536160).sum := by decide
  have hdescent : baseEnd_536160 < baseStart_536160 := by decide
  rcases family_descends (prefixWord ++ tailWord_536160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536203 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 5]
def baseStart_536203 : Nat := 118140960795 + 536203 * 2 ^ 59
def prefixEnd_536203 : Nat := 4983230072969 + 3 ^ 40 * 536203 * 2
def baseEnd_536203 : Nat := 275329867382870836996553

theorem tailTrace_536203 : CollatzResearch.WordTrace tailWord_536203 prefixEnd_536203 275329867382870836996553 := by
  unfold tailWord_536203
  simp only [CollatzResearch.WordTrace]
  refine ⟨19556930076435582026757263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13037953384290388017838175 19556930076435582026757263)
  ·
    refine ⟨29335395114653373040135895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19556930076435582026757263 29335395114653373040135895)
    ·
      refine ⟨44003092671980059560203843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29335395114653373040135895 44003092671980059560203843)
      ·
        refine ⟨66004639007970089340305765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44003092671980059560203843 66004639007970089340305765)
        ·
          refine ⟨12375869813994391751307331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66004639007970089340305765 12375869813994391751307331)
          ·
            refine ⟨18563804720991587626960997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12375869813994391751307331 18563804720991587626960997)
            ·
              refine ⟨3480713385185922680055187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18563804720991587626960997 3480713385185922680055187)
              ·
                refine ⟨5221070077778884020082781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3480713385185922680055187 5221070077778884020082781)
                ·
                  refine ⟨1957901279167081507531043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5221070077778884020082781 1957901279167081507531043)
                  ·
                    refine ⟨2936851918750622261296565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1957901279167081507531043 2936851918750622261296565)
                    ·
                      refine ⟨275329867382870836996553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2936851918750622261296565 275329867382870836996553)
                      ·
                        rfl

theorem cell23_536203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 5].length) (baseStart_536203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536203 prefixEnd_536203 := by exact prefixLift 536203
  have htrace : WordTrace (prefixWord ++ tailWord_536203) baseStart_536203 baseEnd_536203 := by
    simpa [prefixWord, tailWord_536203, baseEnd_536203] using wordTrace_append hprefix tailTrace_536203
  have hstable : (prefixWord ++ tailWord_536203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536203).length < 2 ^ (prefixWord ++ tailWord_536203).sum := by decide
  have hdescent : baseEnd_536203 < baseStart_536203 := by decide
  rcases family_descends (prefixWord ++ tailWord_536203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536213 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_536213 : Nat := 118140960795 + 536213 * 2 ^ 59
def prefixEnd_536213 : Nat := 4983230072969 + 3 ^ 40 * 536213 * 2
def baseEnd_536213 : Nat := 275335002189415797871507

theorem tailTrace_536213 : CollatzResearch.WordTrace tailWord_536213 prefixEnd_536213 275335002189415797871507 := by
  unfold tailWord_536213
  simp only [CollatzResearch.WordTrace]
  refine ⟨19557294806399353734621293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13038196537599569156414195 19557294806399353734621293)
  ·
    refine ⟨7333985552399757650482985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19557294806399353734621293 7333985552399757650482985)
    ·
      refine ⟨5500489164299818237862239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7333985552399757650482985 5500489164299818237862239)
      ·
        refine ⟨8250733746449727356793359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5500489164299818237862239 8250733746449727356793359)
        ·
          refine ⟨12376100619674591035190039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8250733746449727356793359 12376100619674591035190039)
          ·
            refine ⟨18564150929511886552785059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12376100619674591035190039 18564150929511886552785059)
            ·
              refine ⟨27846226394267829829177589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18564150929511886552785059 27846226394267829829177589)
              ·
                refine ⟨2610583724462609046485399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27846226394267829829177589 2610583724462609046485399)
                ·
                  refine ⟨3915875586693913569728099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2610583724462609046485399 3915875586693913569728099)
                  ·
                    refine ⟨5873813380040870354592149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3915875586693913569728099 5873813380040870354592149)
                    ·
                      refine ⟨275335002189415797871507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5873813380040870354592149 275335002189415797871507)
                      ·
                        rfl

theorem cell23_536213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_536213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536213 prefixEnd_536213 := by exact prefixLift 536213
  have htrace : WordTrace (prefixWord ++ tailWord_536213) baseStart_536213 baseEnd_536213 := by
    simpa [prefixWord, tailWord_536213, baseEnd_536213] using wordTrace_append hprefix tailTrace_536213
  have hstable : (prefixWord ++ tailWord_536213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536213).length < 2 ^ (prefixWord ++ tailWord_536213).sum := by decide
  have hdescent : baseEnd_536213 < baseStart_536213 := by decide
  rcases family_descends (prefixWord ++ tailWord_536213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536267 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 2, 1, 3]
def baseStart_536267 : Nat := 118140960795 + 536267 * 2 ^ 59
def prefixEnd_536267 : Nat := 4983230072969 + 3 ^ 40 * 536267 * 2
def baseEnd_536267 : Nat := 275362730144758586596259

theorem tailTrace_536267 : CollatzResearch.WordTrace tailWord_536267 prefixEnd_536267 275362730144758586596259 := by
  unfold tailWord_536267
  simp only [CollatzResearch.WordTrace]
  refine ⟨19559264348203720957087055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13039509565469147304724703 19559264348203720957087055)
  ·
    refine ⟨29338896522305581435630583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19559264348203720957087055 29338896522305581435630583)
    ·
      refine ⟨44008344783458372153445875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29338896522305581435630583 44008344783458372153445875)
      ·
        refine ⟨66012517175187558230168813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44008344783458372153445875 66012517175187558230168813)
        ·
          refine ⟨24754693940695334336313305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66012517175187558230168813 24754693940695334336313305)
          ·
            refine ⟨18566020455521500752234979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24754693940695334336313305 18566020455521500752234979)
            ·
              refine ⟨27849030683282251128352469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18566020455521500752234979 27849030683282251128352469)
              ·
                refine ⟨652711656639427760820761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27849030683282251128352469 652711656639427760820761)
                ·
                  refine ⟨489533742479570820615571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652711656639427760820761 489533742479570820615571)
                  ·
                    refine ⟨734300613719356230923357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 489533742479570820615571 734300613719356230923357)
                    ·
                      refine ⟨275362730144758586596259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 734300613719356230923357 275362730144758586596259)
                      ·
                        rfl

theorem cell23_536267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 1, 3].length) (baseStart_536267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536267 prefixEnd_536267 := by exact prefixLift 536267
  have htrace : WordTrace (prefixWord ++ tailWord_536267) baseStart_536267 baseEnd_536267 := by
    simpa [prefixWord, tailWord_536267, baseEnd_536267] using wordTrace_append hprefix tailTrace_536267
  have hstable : (prefixWord ++ tailWord_536267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536267).length < 2 ^ (prefixWord ++ tailWord_536267).sum := by decide
  have hdescent : baseEnd_536267 < baseStart_536267 := by decide
  rcases family_descends (prefixWord ++ tailWord_536267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536364 : List Nat := [2, 2, 1, 1, 1, 5, 4, 2, 5]
def baseStart_536364 : Nat := 118140960795 + 536364 * 2 ^ 59
def prefixEnd_536364 : Nat := 4983230072969 + 3 ^ 40 * 536364 * 2
def baseEnd_536364 : Nat := 30601393085360523009257

theorem tailTrace_536364 : CollatzResearch.WordTrace tailWord_536364 prefixEnd_536364 30601393085360523009257 := by
  unfold tailWord_536364
  simp only [CollatzResearch.WordTrace]
  refine ⟨9781401114426153261684073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13041868152568204348912097 9781401114426153261684073)
  ·
    refine ⟨7336050835819614946263055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9781401114426153261684073 7336050835819614946263055)
    ·
      refine ⟨11004076253729422419394583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7336050835819614946263055 11004076253729422419394583)
      ·
        refine ⟨16506114380594133629091875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11004076253729422419394583 16506114380594133629091875)
        ·
          refine ⟨24759171570891200443637813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16506114380594133629091875 24759171570891200443637813)
          ·
            refine ⟨2321172334771050041591045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24759171570891200443637813 2321172334771050041591045)
            ·
              refine ⟨435219812769571882798321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2321172334771050041591045 435219812769571882798321)
              ·
                refine ⟨326414859577178912098741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435219812769571882798321 326414859577178912098741)
                ·
                  refine ⟨30601393085360523009257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326414859577178912098741 30601393085360523009257)
                  ·
                    rfl

theorem cell23_536364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_536364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536364 prefixEnd_536364 := by exact prefixLift 536364
  have htrace : WordTrace (prefixWord ++ tailWord_536364) baseStart_536364 baseEnd_536364 := by
    simpa [prefixWord, tailWord_536364, baseEnd_536364] using wordTrace_append hprefix tailTrace_536364
  have hstable : (prefixWord ++ tailWord_536364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536364).length < 2 ^ (prefixWord ++ tailWord_536364).sum := by decide
  have hdescent : baseEnd_536364 < baseStart_536364 := by decide
  rcases family_descends (prefixWord ++ tailWord_536364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536374 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_536374 : Nat := 118140960795 + 536374 * 2 ^ 59
def prefixEnd_536374 : Nat := 4983230072969 + 3 ^ 40 * 536374 * 2
def baseEnd_536374 : Nat := 275417672574789667958267

theorem tailTrace_536374 : CollatzResearch.WordTrace tailWord_536374 prefixEnd_536374 275417672574789667958267 := by
  unfold tailWord_536374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222697934926004889452011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13042111305877385487488117 1222697934926004889452011)
  ·
    refine ⟨1834046902389007334178017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1222697934926004889452011 1834046902389007334178017)
    ·
      refine ⟨1375535176791755500633513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1834046902389007334178017 1375535176791755500633513)
      ·
        refine ⟨1031651382593816625475135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1375535176791755500633513 1031651382593816625475135)
        ·
          refine ⟨1547477073890724938212703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031651382593816625475135 1547477073890724938212703)
          ·
            refine ⟨2321215610836087407319055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547477073890724938212703 2321215610836087407319055)
            ·
              refine ⟨3481823416254131110978583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321215610836087407319055 3481823416254131110978583)
              ·
                refine ⟨5222735124381196666467875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481823416254131110978583 5222735124381196666467875)
                ·
                  refine ⟨7834102686571794999701813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5222735124381196666467875 7834102686571794999701813)
                  ·
                    refine ⟨734447126866105781222045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7834102686571794999701813 734447126866105781222045)
                    ·
                      refine ⟨275417672574789667958267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 734447126866105781222045 275417672574789667958267)
                      ·
                        rfl

theorem cell23_536374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_536374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536374 prefixEnd_536374 := by exact prefixLift 536374
  have htrace : WordTrace (prefixWord ++ tailWord_536374) baseStart_536374 baseEnd_536374 := by
    simpa [prefixWord, tailWord_536374, baseEnd_536374] using wordTrace_append hprefix tailTrace_536374
  have hstable : (prefixWord ++ tailWord_536374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536374).length < 2 ^ (prefixWord ++ tailWord_536374).sum := by decide
  have hdescent : baseEnd_536374 < baseStart_536374 := by decide
  rcases family_descends (prefixWord ++ tailWord_536374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536410 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_536410 : Nat := 118140960795 + 536410 * 2 ^ 59
def prefixEnd_536410 : Nat := 4983230072969 + 3 ^ 40 * 536410 * 2
def baseEnd_536410 : Nat := 275436157878351527108101

theorem tailTrace_536410 : CollatzResearch.WordTrace tailWord_536410 prefixEnd_536410 275436157878351527108101 := by
  unfold tailWord_536410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4891119996671414094885671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13042986657790437586361789 4891119996671414094885671)
  ·
    refine ⟨7336679995007121142328507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4891119996671414094885671 7336679995007121142328507)
    ·
      refine ⟨11005019992510681713492761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7336679995007121142328507 11005019992510681713492761)
      ·
        refine ⟨8253764994383011285119571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11005019992510681713492761 8253764994383011285119571)
        ·
          refine ⟨12380647491574516927679357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8253764994383011285119571 12380647491574516927679357)
          ·
            refine ⟨4642742809340443847879759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12380647491574516927679357 4642742809340443847879759)
            ·
              refine ⟨6964114214010665771819639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642742809340443847879759 6964114214010665771819639)
              ·
                refine ⟨10446171321015998657729459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6964114214010665771819639 10446171321015998657729459)
                ·
                  refine ⟨15669256981523997986594189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10446171321015998657729459 15669256981523997986594189)
                  ·
                    refine ⟨5875971368071499244972821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15669256981523997986594189 5875971368071499244972821)
                    ·
                      refine ⟨275436157878351527108101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5875971368071499244972821 275436157878351527108101)
                      ·
                        rfl

theorem cell23_536410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_536410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536410 prefixEnd_536410 := by exact prefixLift 536410
  have htrace : WordTrace (prefixWord ++ tailWord_536410) baseStart_536410 baseEnd_536410 := by
    simpa [prefixWord, tailWord_536410, baseEnd_536410] using wordTrace_append hprefix tailTrace_536410
  have hstable : (prefixWord ++ tailWord_536410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536410).length < 2 ^ (prefixWord ++ tailWord_536410).sum := by decide
  have hdescent : baseEnd_536410 < baseStart_536410 := by decide
  rcases family_descends (prefixWord ++ tailWord_536410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536417 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_536417 : Nat := 118140960795 + 536417 * 2 ^ 59
def prefixEnd_536417 : Nat := 4983230072969 + 3 ^ 40 * 536417 * 2
def baseEnd_536417 : Nat := 275439752242932999720569

theorem tailTrace_536417 : CollatzResearch.WordTrace tailWord_536417 prefixEnd_536417 275439752242932999720569 := by
  unfold tailWord_536417
  simp only [CollatzResearch.WordTrace]
  refine ⟨19564735297660296575047505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13043156865106864383365003 19564735297660296575047505)
  ·
    refine ⟨14673551473245222431285629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19564735297660296575047505 14673551473245222431285629)
    ·
      refine ⟨5502581802466958411732111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14673551473245222431285629 5502581802466958411732111)
      ·
        refine ⟨8253872703700437617598167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5502581802466958411732111 8253872703700437617598167)
        ·
          refine ⟨12380809055550656426397251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8253872703700437617598167 12380809055550656426397251)
          ·
            refine ⟨18571213583325984639595877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12380809055550656426397251 18571213583325984639595877)
            ·
              refine ⟨3482102546873622119924227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18571213583325984639595877 3482102546873622119924227)
              ·
                refine ⟨5223153820310433179886341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482102546873622119924227 5223153820310433179886341)
                ·
                  refine ⟨979341341308206221228689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5223153820310433179886341 979341341308206221228689)
                  ·
                    refine ⟨734506005981154665921517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 979341341308206221228689 734506005981154665921517)
                    ·
                      refine ⟨275439752242932999720569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 734506005981154665921517 275439752242932999720569)
                      ·
                        rfl

theorem cell23_536417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_536417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536417 prefixEnd_536417 := by exact prefixLift 536417
  have htrace : WordTrace (prefixWord ++ tailWord_536417) baseStart_536417 baseEnd_536417 := by
    simpa [prefixWord, tailWord_536417, baseEnd_536417] using wordTrace_append hprefix tailTrace_536417
  have hstable : (prefixWord ++ tailWord_536417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536417).length < 2 ^ (prefixWord ++ tailWord_536417).sum := by decide
  have hdescent : baseEnd_536417 < baseStart_536417 := by decide
  rcases family_descends (prefixWord ++ tailWord_536417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536424 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 3, 4]
def baseStart_536424 : Nat := 118140960795 + 536424 * 2 ^ 59
def prefixEnd_536424 : Nat := 4983230072969 + 3 ^ 40 * 536424 * 2
def baseEnd_536424 : Nat := 91814448869171490777679

theorem tailTrace_536424 : CollatzResearch.WordTrace tailWord_536424 prefixEnd_536424 91814448869171490777679 := by
  unfold tailWord_536424
  simp only [CollatzResearch.WordTrace]
  refine ⟨9782495304317468385276163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13043327072423291180368217 9782495304317468385276163)
  ·
    refine ⟨14673742956476202577914245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9782495304317468385276163 14673742956476202577914245)
    ·
      refine ⟨2751326804339287983358921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14673742956476202577914245 2751326804339287983358921)
      ·
        refine ⟨2063495103254465987519191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2751326804339287983358921 2063495103254465987519191)
        ·
          refine ⟨3095242654881698981278787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2063495103254465987519191 3095242654881698981278787)
          ·
            refine ⟨4642863982322548471918181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095242654881698981278787 4642863982322548471918181)
            ·
              refine ⟨870536996685477838484659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4642863982322548471918181 870536996685477838484659)
              ·
                refine ⟨1305805495028216757726989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870536996685477838484659 1305805495028216757726989)
                ·
                  refine ⟨489677060635581284147621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1305805495028216757726989 489677060635581284147621)
                  ·
                    refine ⟨91814448869171490777679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489677060635581284147621 91814448869171490777679)
                    ·
                      rfl

theorem cell23_536424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_536424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536424 prefixEnd_536424 := by exact prefixLift 536424
  have htrace : WordTrace (prefixWord ++ tailWord_536424) baseStart_536424 baseEnd_536424 := by
    simpa [prefixWord, tailWord_536424, baseEnd_536424] using wordTrace_append hprefix tailTrace_536424
  have hstable : (prefixWord ++ tailWord_536424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536424).length < 2 ^ (prefixWord ++ tailWord_536424).sum := by decide
  have hdescent : baseEnd_536424 < baseStart_536424 := by decide
  rcases family_descends (prefixWord ++ tailWord_536424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536501 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_536501 : Nat := 118140960795 + 536501 * 2 ^ 59
def prefixEnd_536501 : Nat := 4983230072969 + 3 ^ 40 * 536501 * 2
def baseEnd_536501 : Nat := 91827628205970223690061

theorem tailTrace_536501 : CollatzResearch.WordTrace tailWord_536501 prefixEnd_536501 91827628205970223690061 := by
  unfold tailWord_536501
  simp only [CollatzResearch.WordTrace]
  refine ⟨19567799029355978921105357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13045199352903985947403571 19567799029355978921105357)
  ·
    refine ⟨7337924636008492095414509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19567799029355978921105357 7337924636008492095414509)
    ·
      refine ⟨2751721738503184535780441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7337924636008492095414509 2751721738503184535780441)
      ·
        refine ⟨2063791303877388401835331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2751721738503184535780441 2063791303877388401835331)
        ·
          refine ⟨3095686955816082602752997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2063791303877388401835331 3095686955816082602752997)
          ·
            refine ⟨580441304215515488016187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3095686955816082602752997 580441304215515488016187)
            ·
              refine ⟨870661956323273232024281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580441304215515488016187 870661956323273232024281)
              ·
                refine ⟨652996467242454924018211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870661956323273232024281 652996467242454924018211)
                ·
                  refine ⟨979494700863682386027317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652996467242454924018211 979494700863682386027317)
                  ·
                    refine ⟨91827628205970223690061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 979494700863682386027317 91827628205970223690061)
                    ·
                      rfl

theorem cell23_536501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_536501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536501 prefixEnd_536501 := by exact prefixLift 536501
  have htrace : WordTrace (prefixWord ++ tailWord_536501) baseStart_536501 baseEnd_536501 := by
    simpa [prefixWord, tailWord_536501, baseEnd_536501] using wordTrace_append hprefix tailTrace_536501
  have hstable : (prefixWord ++ tailWord_536501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536501).length < 2 ^ (prefixWord ++ tailWord_536501).sum := by decide
  have hdescent : baseEnd_536501 < baseStart_536501 := by decide
  rcases family_descends (prefixWord ++ tailWord_536501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536524 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 1, 1, 5]
def baseStart_536524 : Nat := 118140960795 + 536524 * 2 ^ 59
def prefixEnd_536524 : Nat := 4983230072969 + 3 ^ 40 * 536524 * 2
def baseEnd_536524 : Nat := 275494694672964081082577

theorem tailTrace_536524 : CollatzResearch.WordTrace tailWord_536524 prefixEnd_536524 275494694672964081082577 := by
  unfold tailWord_536524
  simp only [CollatzResearch.WordTrace]
  refine ⟨9784318954136326924596313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13045758605515102566128417 9784318954136326924596313)
  ·
    refine ⟨7338239215602245193447235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9784318954136326924596313 7338239215602245193447235)
    ·
      refine ⟨11007358823403367790170853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7338239215602245193447235 11007358823403367790170853)
      ·
        refine ⟨2063879779388131460657035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11007358823403367790170853 2063879779388131460657035)
        ·
          refine ⟨3095819669082197190985553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2063879779388131460657035 3095819669082197190985553)
          ·
            refine ⟨2321864751811647893239165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3095819669082197190985553 2321864751811647893239165)
            ·
              refine ⟨870699281929367959964687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2321864751811647893239165 870699281929367959964687)
              ·
                refine ⟨1306048922894051939947031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870699281929367959964687 1306048922894051939947031)
                ·
                  refine ⟨1959073384341077909920547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306048922894051939947031 1959073384341077909920547)
                  ·
                    refine ⟨2938610076511616864880821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1959073384341077909920547 2938610076511616864880821)
                    ·
                      refine ⟨275494694672964081082577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2938610076511616864880821 275494694672964081082577)
                      ·
                        rfl

theorem cell23_536524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_536524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536524 prefixEnd_536524 := by exact prefixLift 536524
  have htrace : WordTrace (prefixWord ++ tailWord_536524) baseStart_536524 baseEnd_536524 := by
    simpa [prefixWord, tailWord_536524, baseEnd_536524] using wordTrace_append hprefix tailTrace_536524
  have hstable : (prefixWord ++ tailWord_536524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536524).length < 2 ^ (prefixWord ++ tailWord_536524).sum := by decide
  have hdescent : baseEnd_536524 < baseStart_536524 := by decide
  rcases family_descends (prefixWord ++ tailWord_536524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536551 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_536551 : Nat := 118140960795 + 536551 * 2 ^ 59
def prefixEnd_536551 : Nat := 4983230072969 + 3 ^ 40 * 536551 * 2
def baseEnd_536551 : Nat := 275508558650635475444953

theorem tailTrace_536551 : CollatzResearch.WordTrace tailWord_536551 prefixEnd_536551 275508558650635475444953 := by
  unfold tailWord_536551
  simp only [CollatzResearch.WordTrace]
  refine ⟨19569622679174837460425507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13046415119449891640283671 19569622679174837460425507)
  ·
    refine ⟨29354434018762256190638261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19569622679174837460425507 29354434018762256190638261)
    ·
      refine ⟨2751978189258961517872337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29354434018762256190638261 2751978189258961517872337)
      ·
        refine ⟨2063983641944221138404253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2751978189258961517872337 2063983641944221138404253)
        ·
          refine ⟨773993865729082926901595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2063983641944221138404253 773993865729082926901595)
          ·
            refine ⟨1160990798593624390352393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773993865729082926901595 1160990798593624390352393)
            ·
              refine ⟨870743098945218292764295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160990798593624390352393 870743098945218292764295)
              ·
                refine ⟨1306114648417827439146443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870743098945218292764295 1306114648417827439146443)
                ·
                  refine ⟨1959171972626741158719665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306114648417827439146443 1959171972626741158719665)
                  ·
                    refine ⟨1469378979470055869039749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1959171972626741158719665 1469378979470055869039749)
                    ·
                      refine ⟨275508558650635475444953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1469378979470055869039749 275508558650635475444953)
                      ·
                        rfl

theorem cell23_536551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_536551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536551 prefixEnd_536551 := by exact prefixLift 536551
  have htrace : WordTrace (prefixWord ++ tailWord_536551) baseStart_536551 baseEnd_536551 := by
    simpa [prefixWord, tailWord_536551, baseEnd_536551] using wordTrace_append hprefix tailTrace_536551
  have hstable : (prefixWord ++ tailWord_536551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536551).length < 2 ^ (prefixWord ++ tailWord_536551).sum := by decide
  have hdescent : baseEnd_536551 < baseStart_536551 := by decide
  rcases family_descends (prefixWord ++ tailWord_536551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536582 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_536582 : Nat := 118140960795 + 536582 * 2 ^ 59
def prefixEnd_536582 : Nat := 4983230072969 + 3 ^ 40 * 536582 * 2
def baseEnd_536582 : Nat := 91841492183641618052437

theorem tailTrace_536582 : CollatzResearch.WordTrace tailWord_536582 prefixEnd_536582 91841492183641618052437 := by
  unfold tailWord_536582
  simp only [CollatzResearch.WordTrace]
  refine ⟨611586041939454054837625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13047168894708353169869333 611586041939454054837625)
  ·
    refine ⟨458689531454590541128219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 611586041939454054837625 458689531454590541128219)
    ·
      refine ⟨688034297181885811692329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458689531454590541128219 688034297181885811692329)
      ·
        refine ⟨516025722886414358769247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 688034297181885811692329 516025722886414358769247)
        ·
          refine ⟨774038584329621538153871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516025722886414358769247 774038584329621538153871)
          ·
            refine ⟨1161057876494432307230807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774038584329621538153871 1161057876494432307230807)
            ·
              refine ⟨1741586814741648460846211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161057876494432307230807 1741586814741648460846211)
              ·
                refine ⟨2612380222112472691269317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741586814741648460846211 2612380222112472691269317)
                ·
                  refine ⟨489821291646088629612997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2612380222112472691269317 489821291646088629612997)
                  ·
                    refine ⟨91841492183641618052437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489821291646088629612997 91841492183641618052437)
                    ·
                      rfl

theorem cell23_536582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_536582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536582 prefixEnd_536582 := by exact prefixLift 536582
  have htrace : WordTrace (prefixWord ++ tailWord_536582) baseStart_536582 baseEnd_536582 := by
    simpa [prefixWord, tailWord_536582, baseEnd_536582] using wordTrace_append hprefix tailTrace_536582
  have hstable : (prefixWord ++ tailWord_536582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536582).length < 2 ^ (prefixWord ++ tailWord_536582).sum := by decide
  have hdescent : baseEnd_536582 < baseStart_536582 := by decide
  rcases family_descends (prefixWord ++ tailWord_536582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536587 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 4, 6]
def baseStart_536587 : Nat := 118140960795 + 536587 * 2 ^ 59
def prefixEnd_536587 : Nat := 4983230072969 + 3 ^ 40 * 536587 * 2
def baseEnd_536587 : Nat := 91842347984732444864929

theorem tailTrace_536587 : CollatzResearch.WordTrace tailWord_536587 prefixEnd_536587 91842347984732444864929 := by
  unfold tailWord_536587
  simp only [CollatzResearch.WordTrace]
  refine ⟨19570935707044415608736015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13047290471362943739157343 19570935707044415608736015)
  ·
    refine ⟨29356403560566623413104023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19570935707044415608736015 29356403560566623413104023)
    ·
      refine ⟨44034605340849935119656035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29356403560566623413104023 44034605340849935119656035)
      ·
        refine ⟨66051908011274902679484053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44034605340849935119656035 66051908011274902679484053)
        ·
          refine ⟨3096183188028511063100815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66051908011274902679484053 3096183188028511063100815)
          ·
            refine ⟨4644274782042766594651223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3096183188028511063100815 4644274782042766594651223)
            ·
              refine ⟨6966412173064149891976835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4644274782042766594651223 6966412173064149891976835)
              ·
                refine ⟨10449618259596224837965253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6966412173064149891976835 10449618259596224837965253)
                ·
                  refine ⟨1959303423674292157118485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10449618259596224837965253 1959303423674292157118485)
                  ·
                    refine ⟨91842347984732444864929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1959303423674292157118485 91842347984732444864929)
                    ·
                      rfl

theorem cell23_536587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 6].length) (baseStart_536587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536587 prefixEnd_536587 := by exact prefixLift 536587
  have htrace : WordTrace (prefixWord ++ tailWord_536587) baseStart_536587 baseEnd_536587 := by
    simpa [prefixWord, tailWord_536587, baseEnd_536587] using wordTrace_append hprefix tailTrace_536587
  have hstable : (prefixWord ++ tailWord_536587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536587).length < 2 ^ (prefixWord ++ tailWord_536587).sum := by decide
  have hdescent : baseEnd_536587 < baseStart_536587 := by decide
  rcases family_descends (prefixWord ++ tailWord_536587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536589 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_536589 : Nat := 118140960795 + 536589 * 2 ^ 59
def prefixEnd_536589 : Nat := 4983230072969 + 3 ^ 40 * 536589 * 2
def baseEnd_536589 : Nat := 275528070915506326769779

theorem tailTrace_536589 : CollatzResearch.WordTrace tailWord_536589 prefixEnd_536589 275528070915506326769779 := by
  unfold tailWord_536589
  simp only [CollatzResearch.WordTrace]
  refine ⟨19571008653037169950308821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13047339102024779966872547 19571008653037169950308821)
  ·
    refine ⟨458695515305558670710363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19571008653037169950308821 458695515305558670710363)
    ·
      refine ⟨688043272958338006065545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458695515305558670710363 688043272958338006065545)
      ·
        refine ⟨516032454718753504549159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 688043272958338006065545 516032454718753504549159)
        ·
          refine ⟨774048682078130256823739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516032454718753504549159 774048682078130256823739)
          ·
            refine ⟨1161073023117195385235609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774048682078130256823739 1161073023117195385235609)
            ·
              refine ⟨870804767337896538926707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161073023117195385235609 870804767337896538926707)
              ·
                refine ⟨1306207151006844808390061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870804767337896538926707 1306207151006844808390061)
                ·
                  refine ⟨489827681627566803146273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1306207151006844808390061 489827681627566803146273)
                  ·
                    refine ⟨367370761220675102359705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 489827681627566803146273 367370761220675102359705)
                    ·
                      refine ⟨275528070915506326769779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 367370761220675102359705 275528070915506326769779)
                      ·
                        rfl

theorem cell23_536589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_536589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536589 prefixEnd_536589 := by exact prefixLift 536589
  have htrace : WordTrace (prefixWord ++ tailWord_536589) baseStart_536589 baseEnd_536589 := by
    simpa [prefixWord, tailWord_536589, baseEnd_536589] using wordTrace_append hprefix tailTrace_536589
  have hstable : (prefixWord ++ tailWord_536589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536589).length < 2 ^ (prefixWord ++ tailWord_536589).sum := by decide
  have hdescent : baseEnd_536589 < baseStart_536589 := by decide
  rcases family_descends (prefixWord ++ tailWord_536589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536604 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_536604 : Nat := 118140960795 + 536604 * 2 ^ 59
def prefixEnd_536604 : Nat := 4983230072969 + 3 ^ 40 * 536604 * 2
def baseEnd_536604 : Nat := 91845257708441256027403

theorem tailTrace_536604 : CollatzResearch.WordTrace tailWord_536604 prefixEnd_536604 91845257708441256027403 := by
  unfold tailWord_536604
  simp only [CollatzResearch.WordTrace]
  refine ⟨9785777873991413756052433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13047703831988551674736577 9785777873991413756052433)
  ·
    refine ⟨7339333405493560317039325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9785777873991413756052433 7339333405493560317039325)
    ·
      refine ⟨2752250027060085118889747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7339333405493560317039325 2752250027060085118889747)
      ·
        refine ⟨4128375040590127678334621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2752250027060085118889747 4128375040590127678334621)
        ·
          refine ⟨1548140640221297879375483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4128375040590127678334621 1548140640221297879375483)
          ·
            refine ⟨2322210960331946819063225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548140640221297879375483 2322210960331946819063225)
            ·
              refine ⟨1741658220248960114297419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2322210960331946819063225 1741658220248960114297419)
              ·
                refine ⟨2612487330373440171446129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741658220248960114297419 2612487330373440171446129)
                ·
                  refine ⟨1959365497780080128584597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2612487330373440171446129 1959365497780080128584597)
                  ·
                    refine ⟨91845257708441256027403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1959365497780080128584597 91845257708441256027403)
                    ·
                      rfl

theorem cell23_536604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_536604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536604 prefixEnd_536604 := by exact prefixLift 536604
  have htrace : WordTrace (prefixWord ++ tailWord_536604) baseStart_536604 baseEnd_536604 := by
    simpa [prefixWord, tailWord_536604, baseEnd_536604] using wordTrace_append hprefix tailTrace_536604
  have hstable : (prefixWord ++ tailWord_536604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536604).length < 2 ^ (prefixWord ++ tailWord_536604).sum := by decide
  have hdescent : baseEnd_536604 < baseStart_536604 := by decide
  rcases family_descends (prefixWord ++ tailWord_536604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536605 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_536605 : Nat := 118140960795 + 536605 * 2 ^ 59
def prefixEnd_536605 : Nat := 4983230072969 + 3 ^ 40 * 536605 * 2
def baseEnd_536605 : Nat := 275536286605978264169705

theorem tailTrace_536605 : CollatzResearch.WordTrace tailWord_536605 prefixEnd_536605 275536286605978264169705 := by
  unfold tailWord_536605
  simp only [CollatzResearch.WordTrace]
  refine ⟨19571592220979204682891269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13047728147319469788594179 19571592220979204682891269)
  ·
    refine ⟨3669673541433600878042113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19571592220979204682891269 3669673541433600878042113)
    ·
      refine ⟨2752255156075200658531585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3669673541433600878042113 2752255156075200658531585)
      ·
        refine ⟨2064191367056400493898689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2752255156075200658531585 2064191367056400493898689)
        ·
          refine ⟨1548143525292300370424017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2064191367056400493898689 1548143525292300370424017)
          ·
            refine ⟨1161107643969225277818013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1548143525292300370424017 1161107643969225277818013)
            ·
              refine ⟨435415366488459479181755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1161107643969225277818013 435415366488459479181755)
              ·
                refine ⟨653123049732689218772633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435415366488459479181755 653123049732689218772633)
                ·
                  refine ⟨489842287299516914079475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 653123049732689218772633 489842287299516914079475)
                  ·
                    refine ⟨734763430949275371119213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 489842287299516914079475 734763430949275371119213)
                    ·
                      refine ⟨275536286605978264169705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 734763430949275371119213 275536286605978264169705)
                      ·
                        rfl

theorem cell23_536605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_536605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536605 prefixEnd_536605 := by exact prefixLift 536605
  have htrace : WordTrace (prefixWord ++ tailWord_536605) baseStart_536605 baseEnd_536605 := by
    simpa [prefixWord, tailWord_536605, baseEnd_536605] using wordTrace_append hprefix tailTrace_536605
  have hstable : (prefixWord ++ tailWord_536605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536605).length < 2 ^ (prefixWord ++ tailWord_536605).sum := by decide
  have hdescent : baseEnd_536605 < baseStart_536605 := by decide
  rcases family_descends (prefixWord ++ tailWord_536605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536701 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_536701 : Nat := 118140960795 + 536701 * 2 ^ 59
def prefixEnd_536701 : Nat := 4983230072969 + 3 ^ 40 * 536701 * 2
def baseEnd_536701 : Nat := 275585580748809888569263

theorem tailTrace_536701 : CollatzResearch.WordTrace tailWord_536701 prefixEnd_536701 275585580748809888569263 := by
  unfold tailWord_536701
  simp only [CollatzResearch.WordTrace]
  refine ⟨19575093628631413078385957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13050062419087608718923971 19575093628631413078385957)
  ·
    refine ⟨3670330055368389952197367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19575093628631413078385957 3670330055368389952197367)
    ·
      refine ⟨5505495083052584928296051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3670330055368389952197367 5505495083052584928296051)
      ·
        refine ⟨8258242624578877392444077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5505495083052584928296051 8258242624578877392444077)
        ·
          refine ⟨3096840984217079022166529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8258242624578877392444077 3096840984217079022166529)
          ·
            refine ⟨2322630738162809266624897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3096840984217079022166529 2322630738162809266624897)
            ·
              refine ⟨1741973053622106949968673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2322630738162809266624897 1741973053622106949968673)
              ·
                refine ⟨1306479790216580212476505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1741973053622106949968673 1306479790216580212476505)
                ·
                  refine ⟨979859842662435159357379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1306479790216580212476505 979859842662435159357379)
                  ·
                    refine ⟨1469789763993652739036069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 979859842662435159357379 1469789763993652739036069)
                    ·
                      refine ⟨275585580748809888569263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1469789763993652739036069 275585580748809888569263)
                      ·
                        rfl

theorem cell23_536701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_536701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536701 prefixEnd_536701 := by exact prefixLift 536701
  have htrace : WordTrace (prefixWord ++ tailWord_536701) baseStart_536701 baseEnd_536701 := by
    simpa [prefixWord, tailWord_536701, baseEnd_536701] using wordTrace_append hprefix tailTrace_536701
  have hstable : (prefixWord ++ tailWord_536701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536701).length < 2 ^ (prefixWord ++ tailWord_536701).sum := by decide
  have hdescent : baseEnd_536701 < baseStart_536701 := by decide
  rcases family_descends (prefixWord ++ tailWord_536701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536704 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 3]
def baseStart_536704 : Nat := 118140960795 + 536704 * 2 ^ 59
def prefixEnd_536704 : Nat := 4983230072969 + 3 ^ 40 * 536704 * 2
def baseEnd_536704 : Nat := 275587121190773376831749

theorem tailTrace_536704 : CollatzResearch.WordTrace tailWord_536704 prefixEnd_536704 275587121190773376831749 := by
  unfold tailWord_536704
  simp only [CollatzResearch.WordTrace]
  refine ⟨9787601523810272295372583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13050135365080363060496777 9787601523810272295372583)
  ·
    refine ⟨14681402285715408443058875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9787601523810272295372583 14681402285715408443058875)
    ·
      refine ⟨22022103428573112664588313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14681402285715408443058875 22022103428573112664588313)
      ·
        refine ⟨16516577571429834498441235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22022103428573112664588313 16516577571429834498441235)
        ·
          refine ⟨24774866357144751747661853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16516577571429834498441235 24774866357144751747661853)
          ·
            refine ⟨9290574883929281905373195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24774866357144751747661853 9290574883929281905373195)
            ·
              refine ⟨13935862325893922858059793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9290574883929281905373195 13935862325893922858059793)
              ·
                refine ⟨10451896744420442143544845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13935862325893922858059793 10451896744420442143544845)
                ·
                  refine ⟨3919461279157665803829317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10451896744420442143544845 3919461279157665803829317)
                  ·
                    refine ⟨734898989842062338217997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3919461279157665803829317 734898989842062338217997)
                    ·
                      refine ⟨275587121190773376831749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 734898989842062338217997 275587121190773376831749)
                      ·
                        rfl

theorem cell23_536704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_536704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536704 prefixEnd_536704 := by exact prefixLift 536704
  have htrace : WordTrace (prefixWord ++ tailWord_536704) baseStart_536704 baseEnd_536704 := by
    simpa [prefixWord, tailWord_536704, baseEnd_536704] using wordTrace_append hprefix tailTrace_536704
  have hstable : (prefixWord ++ tailWord_536704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536704).length < 2 ^ (prefixWord ++ tailWord_536704).sum := by decide
  have hdescent : baseEnd_536704 < baseStart_536704 := by decide
  rcases family_descends (prefixWord ++ tailWord_536704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536728 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 3, 4]
def baseStart_536728 : Nat := 118140960795 + 536728 * 2 ^ 59
def prefixEnd_536728 : Nat := 4983230072969 + 3 ^ 40 * 536728 * 2
def baseEnd_536728 : Nat := 91866481575493760977213

theorem tailTrace_536728 : CollatzResearch.WordTrace tailWord_536728 prefixEnd_536728 91866481575493760977213 := by
  unfold tailWord_536728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9788039199766798344809419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13050718933022397793079225 9788039199766798344809419)
  ·
    refine ⟨14682058799650197517214129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9788039199766798344809419 14682058799650197517214129)
    ·
      refine ⟨11011544099737648137910597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14682058799650197517214129 11011544099737648137910597)
      ·
        refine ⟨2064664518700809025858237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11011544099737648137910597 2064664518700809025858237)
        ·
          refine ⟨774249194512803384696839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2064664518700809025858237 774249194512803384696839)
          ·
            refine ⟨1161373791769205077045259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774249194512803384696839 1161373791769205077045259)
            ·
              refine ⟨1742060687653807615567889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161373791769205077045259 1742060687653807615567889)
              ·
                refine ⟨1306545515740355711675917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1742060687653807615567889 1306545515740355711675917)
                ·
                  refine ⟨489954568402633391878469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1306545515740355711675917 489954568402633391878469)
                  ·
                    refine ⟨91866481575493760977213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489954568402633391878469 91866481575493760977213)
                    ·
                      rfl

theorem cell23_536728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_536728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536728 prefixEnd_536728 := by exact prefixLift 536728
  have htrace : WordTrace (prefixWord ++ tailWord_536728) baseStart_536728 baseEnd_536728 := by
    simpa [prefixWord, tailWord_536728, baseEnd_536728] using wordTrace_append hprefix tailTrace_536728
  have hstable : (prefixWord ++ tailWord_536728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536728).length < 2 ^ (prefixWord ++ tailWord_536728).sum := by decide
  have hdescent : baseEnd_536728 < baseStart_536728 := by decide
  rcases family_descends (prefixWord ++ tailWord_536728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536738 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_536738 : Nat := 118140960795 + 536738 * 2 ^ 59
def prefixEnd_536738 : Nat := 4983230072969 + 3 ^ 40 * 536738 * 2
def baseEnd_536738 : Nat := 275604579533026243806593

theorem tailTrace_536738 : CollatzResearch.WordTrace tailWord_536738 prefixEnd_536738 275604579533026243806593 := by
  unfold tailWord_536738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894110782374342099370717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13050962086331578931655245 4894110782374342099370717)
  ·
    refine ⟨1835291543390378287264019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4894110782374342099370717 1835291543390378287264019)
    ·
      refine ⟨2752937315085567430896029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1835291543390378287264019 2752937315085567430896029)
      ·
        refine ⟨1032351493157087786586011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2752937315085567430896029 1032351493157087786586011)
        ·
          refine ⟨1548527239735631679879017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032351493157087786586011 1548527239735631679879017)
          ·
            refine ⟨1161395429801723759909263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1548527239735631679879017 1161395429801723759909263)
            ·
              refine ⟨1742093144702585639863895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161395429801723759909263 1742093144702585639863895)
              ·
                refine ⟨2613139717053878459795843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742093144702585639863895 2613139717053878459795843)
                ·
                  refine ⟨3919709575580817689693765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613139717053878459795843 3919709575580817689693765)
                  ·
                    refine ⟨734945545421403316817581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3919709575580817689693765 734945545421403316817581)
                    ·
                      refine ⟨275604579533026243806593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 734945545421403316817581 275604579533026243806593)
                      ·
                        rfl

theorem cell23_536738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_536738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536738 prefixEnd_536738 := by exact prefixLift 536738
  have htrace : WordTrace (prefixWord ++ tailWord_536738) baseStart_536738 baseEnd_536738 := by
    simpa [prefixWord, tailWord_536738, baseEnd_536738] using wordTrace_append hprefix tailTrace_536738
  have hstable : (prefixWord ++ tailWord_536738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536738).length < 2 ^ (prefixWord ++ tailWord_536738).sum := by decide
  have hdescent : baseEnd_536738 < baseStart_536738 := by decide
  rcases family_descends (prefixWord ++ tailWord_536738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536751 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 7, 1, 3]
def baseStart_536751 : Nat := 118140960795 + 536751 * 2 ^ 59
def prefixEnd_536751 : Nat := 4983230072969 + 3 ^ 40 * 536751 * 2
def baseEnd_536751 : Nat := 275611254781534692944033

theorem tailTrace_536751 : CollatzResearch.WordTrace tailWord_536751 prefixEnd_536751 275611254781534692944033 := by
  unfold tailWord_536751
  simp only [CollatzResearch.WordTrace]
  refine ⟨19576917278450271617706107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13051278185633514411804071 19576917278450271617706107)
  ·
    refine ⟨29365375917675407426559161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19576917278450271617706107 29365375917675407426559161)
    ·
      refine ⟨22024031938256555569919371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29365375917675407426559161 22024031938256555569919371)
      ·
        refine ⟨33036047907384833354879057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22024031938256555569919371 33036047907384833354879057)
        ·
          refine ⟨24777035930538625016159293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33036047907384833354879057 24777035930538625016159293)
          ·
            refine ⟨9291388473951984381059735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24777035930538625016159293 9291388473951984381059735)
            ·
              refine ⟨13937082710927976571589603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9291388473951984381059735 13937082710927976571589603)
              ·
                refine ⟨20905624066391964857384405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13937082710927976571589603 20905624066391964857384405)
                ·
                  refine ⟨489975564056061676344947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20905624066391964857384405 489975564056061676344947)
                  ·
                    refine ⟨734963346084092514517421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 489975564056061676344947 734963346084092514517421)
                    ·
                      refine ⟨275611254781534692944033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 734963346084092514517421 275611254781534692944033)
                      ·
                        rfl

theorem cell23_536751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 1, 3].length) (baseStart_536751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536751 prefixEnd_536751 := by exact prefixLift 536751
  have htrace : WordTrace (prefixWord ++ tailWord_536751) baseStart_536751 baseEnd_536751 := by
    simpa [prefixWord, tailWord_536751, baseEnd_536751] using wordTrace_append hprefix tailTrace_536751
  have hstable : (prefixWord ++ tailWord_536751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536751).length < 2 ^ (prefixWord ++ tailWord_536751).sum := by decide
  have hdescent : baseEnd_536751 < baseStart_536751 := by decide
  rcases family_descends (prefixWord ++ tailWord_536751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536768 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 3, 1, 3]
def baseStart_536768 : Nat := 118140960795 + 536768 * 2 ^ 59
def prefixEnd_536768 : Nat := 4983230072969 + 3 ^ 40 * 536768 * 2
def baseEnd_536768 : Nat := 275619983952661126431455

theorem tailTrace_536768 : CollatzResearch.WordTrace tailWord_536768 prefixEnd_536768 275619983952661126431455 := by
  unfold tailWord_536768
  simp only [CollatzResearch.WordTrace]
  refine ⟨9788768659694341760537479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13051691546259122347383305 9788768659694341760537479)
  ·
    refine ⟨14683152989541512640806219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9788768659694341760537479 14683152989541512640806219)
    ·
      refine ⟨22024729484312268961209329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14683152989541512640806219 22024729484312268961209329)
      ·
        refine ⟨16518547113234201720906997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22024729484312268961209329 16518547113234201720906997)
        ·
          refine ⟨1548613791865706411335031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16518547113234201720906997 1548613791865706411335031)
          ·
            refine ⟨2322920687798559617002547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548613791865706411335031 2322920687798559617002547)
            ·
              refine ⟨3484381031697839425503821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2322920687798559617002547 3484381031697839425503821)
              ·
                refine ⟨1306642886886689784563933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3484381031697839425503821 1306642886886689784563933)
                ·
                  refine ⟨489991082582508669211475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1306642886886689784563933 489991082582508669211475)
                  ·
                    refine ⟨734986623873763003817213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 489991082582508669211475 734986623873763003817213)
                    ·
                      refine ⟨275619983952661126431455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 734986623873763003817213 275619983952661126431455)
                      ·
                        rfl

theorem cell23_536768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_536768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536768 prefixEnd_536768 := by exact prefixLift 536768
  have htrace : WordTrace (prefixWord ++ tailWord_536768) baseStart_536768 baseEnd_536768 := by
    simpa [prefixWord, tailWord_536768, baseEnd_536768] using wordTrace_append hprefix tailTrace_536768
  have hstable : (prefixWord ++ tailWord_536768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536768).length < 2 ^ (prefixWord ++ tailWord_536768).sum := by decide
  have hdescent : baseEnd_536768 < baseStart_536768 := by decide
  rcases family_descends (prefixWord ++ tailWord_536768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536791 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 1, 8, 2]
def baseStart_536791 : Nat := 118140960795 + 536791 * 2 ^ 59
def prefixEnd_536791 : Nat := 4983230072969 + 3 ^ 40 * 536791 * 2
def baseEnd_536791 : Nat := 275631794007714536443849

theorem tailTrace_536791 : CollatzResearch.WordTrace tailWord_536791 prefixEnd_536791 275631794007714536443849 := by
  unfold tailWord_536791
  simp only [CollatzResearch.WordTrace]
  refine ⟨19578376198305358449162227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13052250798870238966108151 19578376198305358449162227)
  ·
    refine ⟨29367564297458037673743341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19578376198305358449162227 29367564297458037673743341)
    ·
      refine ⟨11012836611546764127653753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29367564297458037673743341 11012836611546764127653753)
      ·
        refine ⟨8259627458660073095740315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11012836611546764127653753 8259627458660073095740315)
        ·
          refine ⟨12389441187990109643610473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8259627458660073095740315 12389441187990109643610473)
          ·
            refine ⟨9292080890992582232707855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12389441187990109643610473 9292080890992582232707855)
            ·
              refine ⟨13938121336488873349061783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9292080890992582232707855 13938121336488873349061783)
              ·
                refine ⟨20907182004733310023592675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13938121336488873349061783 20907182004733310023592675)
                ·
                  refine ⟨31360773007099965035389013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20907182004733310023592675 31360773007099965035389013)
                  ·
                    refine ⟨367509058676952715258465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31360773007099965035389013 367509058676952715258465)
                    ·
                      refine ⟨275631794007714536443849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 367509058676952715258465 275631794007714536443849)
                      ·
                        rfl

theorem cell23_536791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_536791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536791 prefixEnd_536791 := by exact prefixLift 536791
  have htrace : WordTrace (prefixWord ++ tailWord_536791) baseStart_536791 baseEnd_536791 := by
    simpa [prefixWord, tailWord_536791, baseEnd_536791] using wordTrace_append hprefix tailTrace_536791
  have hstable : (prefixWord ++ tailWord_536791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536791).length < 2 ^ (prefixWord ++ tailWord_536791).sum := by decide
  have hdescent : baseEnd_536791 < baseStart_536791 := by decide
  rcases family_descends (prefixWord ++ tailWord_536791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536796 : List Nat := [2, 2, 5, 2, 2, 1, 1, 3, 1, 4]
def baseStart_536796 : Nat := 118140960795 + 536796 * 2 ^ 59
def prefixEnd_536796 : Nat := 4983230072969 + 3 ^ 40 * 536796 * 2
def baseEnd_536796 : Nat := 91878120470329005627109

theorem tailTrace_536796 : CollatzResearch.WordTrace tailWord_536796 prefixEnd_536796 91878120470329005627109 := by
  unfold tailWord_536796
  simp only [CollatzResearch.WordTrace]
  refine ⟨9789279281643622151547121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13052372375524829535396161 9789279281643622151547121)
  ·
    refine ⟨7341959461232716613660341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9789279281643622151547121 7341959461232716613660341)
    ·
      refine ⟨688308699490567182530657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7341959461232716613660341 688308699490567182530657)
      ·
        refine ⟨516231524617925386897993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 688308699490567182530657 516231524617925386897993)
        ·
          refine ⟨387173643463444040173495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516231524617925386897993 387173643463444040173495)
          ·
            refine ⟨580760465195166060260243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387173643463444040173495 580760465195166060260243)
            ·
              refine ⟨871140697792749090390365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580760465195166060260243 871140697792749090390365)
              ·
                refine ⟨326677761672280908896387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 871140697792749090390365 326677761672280908896387)
                ·
                  refine ⟨490016642508421363344581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326677761672280908896387 490016642508421363344581)
                  ·
                    refine ⟨91878120470329005627109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 490016642508421363344581 91878120470329005627109)
                    ·
                      rfl

theorem cell23_536796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_536796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536796 prefixEnd_536796 := by exact prefixLift 536796
  have htrace : WordTrace (prefixWord ++ tailWord_536796) baseStart_536796 baseEnd_536796 := by
    simpa [prefixWord, tailWord_536796, baseEnd_536796] using wordTrace_append hprefix tailTrace_536796
  have hstable : (prefixWord ++ tailWord_536796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536796).length < 2 ^ (prefixWord ++ tailWord_536796).sum := by decide
  have hdescent : baseEnd_536796 < baseStart_536796 := by decide
  rcases family_descends (prefixWord ++ tailWord_536796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536801 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 6, 4]
def baseStart_536801 : Nat := 118140960795 + 536801 * 2 ^ 59
def prefixEnd_536801 : Nat := 4983230072969 + 3 ^ 40 * 536801 * 2
def baseEnd_536801 : Nat := 91878976271419832439601

theorem tailTrace_536801 : CollatzResearch.WordTrace tailWord_536801 prefixEnd_536801 91878976271419832439601 := by
  unfold tailWord_536801
  simp only [CollatzResearch.WordTrace]
  refine ⟨19578740928269130157026257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13052493952179420104684171 19578740928269130157026257)
  ·
    refine ⟨14684055696201847617769693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19578740928269130157026257 14684055696201847617769693)
    ·
      refine ⟨5506520886075692856663635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14684055696201847617769693 5506520886075692856663635)
      ·
        refine ⟨8259781329113539284995453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5506520886075692856663635 8259781329113539284995453)
        ·
          refine ⟨3097417998417577231873295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8259781329113539284995453 3097417998417577231873295)
          ·
            refine ⟨4646126997626365847809943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097417998417577231873295 4646126997626365847809943)
            ·
              refine ⟨6969190496439548771714915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4646126997626365847809943 6969190496439548771714915)
              ·
                refine ⟨10453785744659323157572373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6969190496439548771714915 10453785744659323157572373)
                ·
                  refine ⟨490021206780905773011205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10453785744659323157572373 490021206780905773011205)
                  ·
                    refine ⟨91878976271419832439601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 490021206780905773011205 91878976271419832439601)
                    ·
                      rfl

theorem cell23_536801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_536801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536801 prefixEnd_536801 := by exact prefixLift 536801
  have htrace : WordTrace (prefixWord ++ tailWord_536801) baseStart_536801 baseEnd_536801 := by
    simpa [prefixWord, tailWord_536801, baseEnd_536801] using wordTrace_append hprefix tailTrace_536801
  have hstable : (prefixWord ++ tailWord_536801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536801).length < 2 ^ (prefixWord ++ tailWord_536801).sum := by decide
  have hdescent : baseEnd_536801 < baseStart_536801 := by decide
  rcases family_descends (prefixWord ++ tailWord_536801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536808 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_536808 : Nat := 118140960795 + 536808 * 2 ^ 59
def prefixEnd_536808 : Nat := 4983230072969 + 3 ^ 40 * 536808 * 2
def baseEnd_536808 : Nat := 275640523178840969931271

theorem tailTrace_536808 : CollatzResearch.WordTrace tailWord_536808 prefixEnd_536808 275640523178840969931271 := by
  unfold tailWord_536808
  simp only [CollatzResearch.WordTrace]
  refine ⟨9789498119621885176265539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13052664159495846901687385 9789498119621885176265539)
  ·
    refine ⟨14684247179432827764398309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9789498119621885176265539 14684247179432827764398309)
    ·
      refine ⟨2753296346143655205824683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14684247179432827764398309 2753296346143655205824683)
      ·
        refine ⟨4129944519215482808737025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753296346143655205824683 4129944519215482808737025)
        ·
          refine ⟨3097458389411612106552769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4129944519215482808737025 3097458389411612106552769)
          ·
            refine ⟨2323093792058709079914577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3097458389411612106552769 2323093792058709079914577)
            ·
              refine ⟨1742320344044031809935933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323093792058709079914577 1742320344044031809935933)
              ·
                refine ⟨653370129016511928725975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1742320344044031809935933 653370129016511928725975)
                ·
                  refine ⟨980055193524767893088963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653370129016511928725975 980055193524767893088963)
                  ·
                    refine ⟨1470082790287151839633445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 980055193524767893088963 1470082790287151839633445)
                    ·
                      refine ⟨275640523178840969931271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1470082790287151839633445 275640523178840969931271)
                      ·
                        rfl

theorem cell23_536808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_536808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536808 prefixEnd_536808 := by exact prefixLift 536808
  have htrace : WordTrace (prefixWord ++ tailWord_536808) baseStart_536808 baseEnd_536808 := by
    simpa [prefixWord, tailWord_536808, baseEnd_536808] using wordTrace_append hprefix tailTrace_536808
  have hstable : (prefixWord ++ tailWord_536808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536808).length < 2 ^ (prefixWord ++ tailWord_536808).sum := by decide
  have hdescent : baseEnd_536808 < baseStart_536808 := by decide
  rcases family_descends (prefixWord ++ tailWord_536808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536811 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 5]
def baseStart_536811 : Nat := 118140960795 + 536811 * 2 ^ 59
def prefixEnd_536811 : Nat := 4983230072969 + 3 ^ 40 * 536811 * 2
def baseEnd_536811 : Nat := 275642063620804458193757

theorem tailTrace_536811 : CollatzResearch.WordTrace tailWord_536811 prefixEnd_536811 275642063620804458193757 := by
  unfold tailWord_536811
  simp only [CollatzResearch.WordTrace]
  refine ⟨19579105658232901864890287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13052737105488601243260191 19579105658232901864890287)
  ·
    refine ⟨29368658487349352797335431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19579105658232901864890287 29368658487349352797335431)
    ·
      refine ⟨44052987731024029196003147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29368658487349352797335431 44052987731024029196003147)
      ·
        refine ⟨66079481596536043794004721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44052987731024029196003147 66079481596536043794004721)
        ·
          refine ⟨49559611197402032845503541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66079481596536043794004721 49559611197402032845503541)
          ·
            refine ⟨4646213549756440579265957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49559611197402032845503541 4646213549756440579265957)
            ·
              refine ⟨871165040579332608612367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4646213549756440579265957 871165040579332608612367)
              ·
                refine ⟨1306747560868998912918551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871165040579332608612367 1306747560868998912918551)
                ·
                  refine ⟨1960121341303498369377827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306747560868998912918551 1960121341303498369377827)
                  ·
                    refine ⟨2940182011955247554066741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1960121341303498369377827 2940182011955247554066741)
                    ·
                      refine ⟨275642063620804458193757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2940182011955247554066741 275642063620804458193757)
                      ·
                        rfl

theorem cell23_536811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 5].length) (baseStart_536811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536811 prefixEnd_536811 := by exact prefixLift 536811
  have htrace : WordTrace (prefixWord ++ tailWord_536811) baseStart_536811 baseEnd_536811 := by
    simpa [prefixWord, tailWord_536811, baseEnd_536811] using wordTrace_append hprefix tailTrace_536811
  have hstable : (prefixWord ++ tailWord_536811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536811).length < 2 ^ (prefixWord ++ tailWord_536811).sum := by decide
  have hdescent : baseEnd_536811 < baseStart_536811 := by decide
  rcases family_descends (prefixWord ++ tailWord_536811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536818 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_536818 : Nat := 118140960795 + 536818 * 2 ^ 59
def prefixEnd_536818 : Nat := 4983230072969 + 3 ^ 40 * 536818 * 2
def baseEnd_536818 : Nat := 91881885995128643602075

theorem tailTrace_536818 : CollatzResearch.WordTrace tailWord_536818 prefixEnd_536818 91881885995128643602075 := by
  unfold tailWord_536818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894840242301885515098777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13052907312805028040263405 4894840242301885515098777)
  ·
    refine ⟨3671130181726414136324083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4894840242301885515098777 3671130181726414136324083)
    ·
      refine ⟨5506695272589621204486125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3671130181726414136324083 5506695272589621204486125)
      ·
        refine ⟨2065010727221107951682297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5506695272589621204486125 2065010727221107951682297)
        ·
          refine ⟨1548758045415830963761723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2065010727221107951682297 1548758045415830963761723)
          ·
            refine ⟨2323137068123746445642585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548758045415830963761723 2323137068123746445642585)
            ·
              refine ⟨1742352801092809834231939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323137068123746445642585 1742352801092809834231939)
              ·
                refine ⟨2613529201639214751347909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742352801092809834231939 2613529201639214751347909)
                ·
                  refine ⟨490036725307352765877733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2613529201639214751347909 490036725307352765877733)
                  ·
                    refine ⟨91881885995128643602075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 490036725307352765877733 91881885995128643602075)
                    ·
                      rfl

theorem cell23_536818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_536818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536818 prefixEnd_536818 := by exact prefixLift 536818
  have htrace : WordTrace (prefixWord ++ tailWord_536818) baseStart_536818 baseEnd_536818 := by
    simpa [prefixWord, tailWord_536818, baseEnd_536818] using wordTrace_append hprefix tailTrace_536818
  have hstable : (prefixWord ++ tailWord_536818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536818).length < 2 ^ (prefixWord ++ tailWord_536818).sum := by decide
  have hdescent : baseEnd_536818 < baseStart_536818 := by decide
  rcases family_descends (prefixWord ++ tailWord_536818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536862 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_536862 : Nat := 118140960795 + 536862 * 2 ^ 59
def prefixEnd_536862 : Nat := 4983230072969 + 3 ^ 40 * 536862 * 2
def baseEnd_536862 : Nat := 275668251134183758656023

theorem tailTrace_536862 : CollatzResearch.WordTrace tailWord_536862 prefixEnd_536862 275668251134183758656023 := by
  unfold tailWord_536862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447620722631017196874605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13053977187365425049997893 2447620722631017196874605)
  ·
    refine ⟨917857770986631448827977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2447620722631017196874605 917857770986631448827977)
    ·
      refine ⟨688393328239973586620983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 917857770986631448827977 688393328239973586620983)
      ·
        refine ⟨1032589992359960379931475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688393328239973586620983 1032589992359960379931475)
        ·
          refine ⟨1548884988539940569897213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032589992359960379931475 1548884988539940569897213)
          ·
            refine ⟨580831870702477713711455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1548884988539940569897213 580831870702477713711455)
            ·
              refine ⟨871247806053716570567183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580831870702477713711455 871247806053716570567183)
              ·
                refine ⟨1306871709080574855850775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871247806053716570567183 1306871709080574855850775)
                ·
                  refine ⟨1960307563620862283776163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306871709080574855850775 1960307563620862283776163)
                  ·
                    refine ⟨2940461345431293425664245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1960307563620862283776163 2940461345431293425664245)
                    ·
                      refine ⟨275668251134183758656023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2940461345431293425664245 275668251134183758656023)
                      ·
                        rfl

theorem cell23_536862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_536862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536862 prefixEnd_536862 := by exact prefixLift 536862
  have htrace : WordTrace (prefixWord ++ tailWord_536862) baseStart_536862 baseEnd_536862 := by
    simpa [prefixWord, tailWord_536862, baseEnd_536862] using wordTrace_append hprefix tailTrace_536862
  have hstable : (prefixWord ++ tailWord_536862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536862).length < 2 ^ (prefixWord ++ tailWord_536862).sum := by decide
  have hdescent : baseEnd_536862 < baseStart_536862 := by decide
  rcases family_descends (prefixWord ++ tailWord_536862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536938 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 7]
def baseStart_536938 : Nat := 118140960795 + 536938 * 2 ^ 59
def prefixEnd_536938 : Nat := 4983230072969 + 3 ^ 40 * 536938 * 2
def baseEnd_536938 : Nat := 30634141740436162367297

theorem tailTrace_536938 : CollatzResearch.WordTrace tailWord_536938 prefixEnd_536938 30634141740436162367297 := by
  unfold tailWord_536938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4895934432193200638690867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13055825152515201703175645 4895934432193200638690867)
  ·
    refine ⟨7343901648289800958036301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4895934432193200638690867 7343901648289800958036301)
    ·
      refine ⟨2753963118108675359263613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7343901648289800958036301 2753963118108675359263613)
      ·
        refine ⟨1032736169290753259723855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2753963118108675359263613 1032736169290753259723855)
        ·
          refine ⟨1549104253936129889585783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032736169290753259723855 1549104253936129889585783)
          ·
            refine ⟨2323656380904194834378675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549104253936129889585783 2323656380904194834378675)
            ·
              refine ⟨3485484571356292251568013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323656380904194834378675 3485484571356292251568013)
              ·
                refine ⟨1307056714258609594338005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3485484571356292251568013 1307056714258609594338005)
                ·
                  refine ⟨30634141740436162367297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1307056714258609594338005 30634141740436162367297)
                  ·
                    rfl

theorem cell23_536938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_536938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536938 prefixEnd_536938 := by exact prefixLift 536938
  have htrace : WordTrace (prefixWord ++ tailWord_536938) baseStart_536938 baseEnd_536938 := by
    simpa [prefixWord, tailWord_536938, baseEnd_536938] using wordTrace_append hprefix tailTrace_536938
  have hstable : (prefixWord ++ tailWord_536938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536938).length < 2 ^ (prefixWord ++ tailWord_536938).sum := by decide
  have hdescent : baseEnd_536938 < baseStart_536938 := by decide
  rcases family_descends (prefixWord ++ tailWord_536938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536951 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 6, 5]
def baseStart_536951 : Nat := 118140960795 + 536951 * 2 ^ 59
def prefixEnd_536951 : Nat := 4983230072969 + 3 ^ 40 * 536951 * 2
def baseEnd_536951 : Nat := 91904650304144636814371

theorem tailTrace_536951 : CollatzResearch.WordTrace tailWord_536951 prefixEnd_536951 91904650304144636814371 := by
  unfold tailWord_536951
  simp only [CollatzResearch.WordTrace]
  refine ⟨19584211877725705774986707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13056141251817137183324471 19584211877725705774986707)
  ·
    refine ⟨29376317816588558662480061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19584211877725705774986707 29376317816588558662480061)
    ·
      refine ⟨11016119181220709498430023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29376317816588558662480061 11016119181220709498430023)
      ·
        refine ⟨16524178771831064247645035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11016119181220709498430023 16524178771831064247645035)
        ·
          refine ⟨24786268157746596371467553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16524178771831064247645035 24786268157746596371467553)
          ·
            refine ⟨18589701118309947278600665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24786268157746596371467553 18589701118309947278600665)
            ·
              refine ⟨13942275838732460458950499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18589701118309947278600665 13942275838732460458950499)
              ·
                refine ⟨20913413758098690688425749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13942275838732460458950499 20913413758098690688425749)
                ·
                  refine ⟨980316269910876126019957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20913413758098690688425749 980316269910876126019957)
                  ·
                    refine ⟨91904650304144636814371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 980316269910876126019957 91904650304144636814371)
                    ·
                      rfl

theorem cell23_536951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_536951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536951 prefixEnd_536951 := by exact prefixLift 536951
  have htrace : WordTrace (prefixWord ++ tailWord_536951) baseStart_536951 baseEnd_536951 := by
    simpa [prefixWord, tailWord_536951, baseEnd_536951] using wordTrace_append hprefix tailTrace_536951
  have hstable : (prefixWord ++ tailWord_536951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536951).length < 2 ^ (prefixWord ++ tailWord_536951).sum := by decide
  have hdescent : baseEnd_536951 < baseStart_536951 := by decide
  rcases family_descends (prefixWord ++ tailWord_536951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536968 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 2, 5]
def baseStart_536968 : Nat := 118140960795 + 536968 * 2 ^ 59
def prefixEnd_536968 : Nat := 4983230072969 + 3 ^ 40 * 536968 * 2
def baseEnd_536968 : Nat := 91907560027853447976845

theorem tailTrace_536968 : CollatzResearch.WordTrace tailWord_536968 prefixEnd_536968 91907560027853447976845 := by
  unfold tailWord_536968
  simp only [CollatzResearch.WordTrace]
  refine ⟨9792415959332058839177779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13056554612442745118903705 9792415959332058839177779)
  ·
    refine ⟨14688623938998088258766669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9792415959332058839177779 14688623938998088258766669)
    ·
      refine ⟨5508233977124283097037501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14688623938998088258766669 5508233977124283097037501)
      ·
        refine ⟨2065587741421606161389063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5508233977124283097037501 2065587741421606161389063)
        ·
          refine ⟨3098381612132409242083595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065587741421606161389063 3098381612132409242083595)
          ·
            refine ⟨4647572418198613863125393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3098381612132409242083595 4647572418198613863125393)
            ·
              refine ⟨3485679313648960397344045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4647572418198613863125393 3485679313648960397344045)
              ·
                refine ⟨1307129742618360149004017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3485679313648960397344045 1307129742618360149004017)
                ·
                  refine ⟨980347306963770111753013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1307129742618360149004017 980347306963770111753013)
                  ·
                    refine ⟨91907560027853447976845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 980347306963770111753013 91907560027853447976845)
                    ·
                      rfl

theorem cell23_536968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_536968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_536968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_536968 prefixEnd_536968 := by exact prefixLift 536968
  have htrace : WordTrace (prefixWord ++ tailWord_536968) baseStart_536968 baseEnd_536968 := by
    simpa [prefixWord, tailWord_536968, baseEnd_536968] using wordTrace_append hprefix tailTrace_536968
  have hstable : (prefixWord ++ tailWord_536968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536968).length < 2 ^ (prefixWord ++ tailWord_536968).sum := by decide
  have hdescent : baseEnd_536968 < baseStart_536968 := by decide
  rcases family_descends (prefixWord ++ tailWord_536968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537001 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_537001 : Nat := 118140960795 + 537001 * 2 ^ 59
def prefixEnd_537001 : Nat := 4983230072969 + 3 ^ 40 * 537001 * 2
def baseEnd_537001 : Nat := 275739624945158714817883

theorem tailTrace_537001 : CollatzResearch.WordTrace tailWord_537001 prefixEnd_537001 275739624945158714817883 := by
  unfold tailWord_537001
  simp only [CollatzResearch.WordTrace]
  refine ⟨19586035527544564314306857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13057357018363042876204571 19586035527544564314306857)
  ·
    refine ⟨14689526645658423235730143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19586035527544564314306857 14689526645658423235730143)
    ·
      refine ⟨22034289968487634853595215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14689526645658423235730143 22034289968487634853595215)
      ·
        refine ⟨33051434952731452280392823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22034289968487634853595215 33051434952731452280392823)
        ·
          refine ⟨49577152429097178420589235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33051434952731452280392823 49577152429097178420589235)
          ·
            refine ⟨74365728643645767630883853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49577152429097178420589235 74365728643645767630883853)
            ·
              refine ⟨27887148241367162861581445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74365728643645767630883853 27887148241367162861581445)
              ·
                refine ⟨5228840295256343036546521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27887148241367162861581445 5228840295256343036546521)
                ·
                  refine ⟨3921630221442257277409891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5228840295256343036546521 3921630221442257277409891)
                  ·
                    refine ⟨5882445332163385916114837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3921630221442257277409891 5882445332163385916114837)
                    ·
                      refine ⟨275739624945158714817883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5882445332163385916114837 275739624945158714817883)
                      ·
                        rfl

theorem cell23_537001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_537001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537001 prefixEnd_537001 := by exact prefixLift 537001
  have htrace : WordTrace (prefixWord ++ tailWord_537001) baseStart_537001 baseEnd_537001 := by
    simpa [prefixWord, tailWord_537001, baseEnd_537001] using wordTrace_append hprefix tailTrace_537001
  have hstable : (prefixWord ++ tailWord_537001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537001).length < 2 ^ (prefixWord ++ tailWord_537001).sum := by decide
  have hdescent : baseEnd_537001 < baseStart_537001 := by decide
  rcases family_descends (prefixWord ++ tailWord_537001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537045 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 6]
def baseStart_537045 : Nat := 118140960795 + 537045 * 2 ^ 59
def prefixEnd_537045 : Nat := 4983230072969 + 3 ^ 40 * 537045 * 2
def baseEnd_537045 : Nat := 30640246454884060296409

theorem tailTrace_537045 : CollatzResearch.WordTrace tailWord_537045 prefixEnd_537045 30640246454884060296409 := by
  unfold tailWord_537045
  simp only [CollatzResearch.WordTrace]
  refine ⟨19587640339385159828908589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13058426892923439885939059 19587640339385159828908589)
  ·
    refine ⟨7345365127269434935840721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19587640339385159828908589 7345365127269434935840721)
    ·
      refine ⟨5509023845452076201880541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7345365127269434935840721 5509023845452076201880541)
      ·
        refine ⟨2065883942044528575705203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5509023845452076201880541 2065883942044528575705203)
        ·
          refine ⟨3098825913066792863557805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065883942044528575705203 3098825913066792863557805)
          ·
            refine ⟨1162059717400047323834177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3098825913066792863557805 1162059717400047323834177)
            ·
              refine ⟨871544788050035492875633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1162059717400047323834177 871544788050035492875633)
              ·
                refine ⟨653658591037526619656725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871544788050035492875633 653658591037526619656725)
                ·
                  refine ⟨30640246454884060296409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 653658591037526619656725 30640246454884060296409)
                  ·
                    rfl

theorem cell23_537045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_537045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537045 prefixEnd_537045 := by exact prefixLift 537045
  have htrace : WordTrace (prefixWord ++ tailWord_537045) baseStart_537045 baseEnd_537045 := by
    simpa [prefixWord, tailWord_537045, baseEnd_537045] using wordTrace_append hprefix tailTrace_537045
  have hstable : (prefixWord ++ tailWord_537045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537045).length < 2 ^ (prefixWord ++ tailWord_537045).sum := by decide
  have hdescent : baseEnd_537045 < baseStart_537045 := by decide
  rcases family_descends (prefixWord ++ tailWord_537045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537089 : List Nat := [1, 2, 4, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_537089 : Nat := 118140960795 + 537089 * 2 ^ 59
def prefixEnd_537089 : Nat := 4983230072969 + 3 ^ 40 * 537089 * 2
def baseEnd_537089 : Nat := 275784811242754370517479

theorem tailTrace_537089 : CollatzResearch.WordTrace tailWord_537089 prefixEnd_537089 275784811242754370517479 := by
  unfold tailWord_537089
  simp only [CollatzResearch.WordTrace]
  refine ⟨19589245151225755343510321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13059496767483836895673547 19589245151225755343510321)
  ·
    refine ⟨14691933863419316507632741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19589245151225755343510321 14691933863419316507632741)
    ·
      refine ⟨2754737599391121845181139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14691933863419316507632741 2754737599391121845181139)
      ·
        refine ⟨4132106399086682767771709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2754737599391121845181139 4132106399086682767771709)
        ·
          refine ⟨1549539899657506037914391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4132106399086682767771709 1549539899657506037914391)
          ·
            refine ⟨2324309849486259056871587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549539899657506037914391 2324309849486259056871587)
            ·
              refine ⟨3486464774229388585307381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2324309849486259056871587 3486464774229388585307381)
              ·
                refine ⟨326856072584005179872567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3486464774229388585307381 326856072584005179872567)
                ·
                  refine ⟨490284108876007769808851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326856072584005179872567 490284108876007769808851)
                  ·
                    refine ⟨735426163314011654713277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 490284108876007769808851 735426163314011654713277)
                    ·
                      refine ⟨275784811242754370517479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 735426163314011654713277 275784811242754370517479)
                      ·
                        rfl

theorem cell23_537089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_537089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537089 prefixEnd_537089 := by exact prefixLift 537089
  have htrace : WordTrace (prefixWord ++ tailWord_537089) baseStart_537089 baseEnd_537089 := by
    simpa [prefixWord, tailWord_537089, baseEnd_537089] using wordTrace_append hprefix tailTrace_537089
  have hstable : (prefixWord ++ tailWord_537089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537089).length < 2 ^ (prefixWord ++ tailWord_537089).sum := by decide
  have hdescent : baseEnd_537089 < baseStart_537089 := by decide
  rcases family_descends (prefixWord ++ tailWord_537089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537092 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_537092 : Nat := 118140960795 + 537092 * 2 ^ 59
def prefixEnd_537092 : Nat := 4983230072969 + 3 ^ 40 * 537092 * 2
def baseEnd_537092 : Nat := 91928783894905952926655

theorem tailTrace_537092 : CollatzResearch.WordTrace tailWord_537092 prefixEnd_537092 91928783894905952926655 := by
  unfold tailWord_537092
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794677285107443427934765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13059569713476591237246353 9794677285107443427934765)
  ·
    refine ⟨3673003981915291285475537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9794677285107443427934765 3673003981915291285475537)
    ·
      refine ⟨2754752986436468464106653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3673003981915291285475537 2754752986436468464106653)
      ·
        refine ⟨1033032369913675674039995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2754752986436468464106653 1033032369913675674039995)
        ·
          refine ⟨1549548554870513511059993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033032369913675674039995 1549548554870513511059993)
          ·
            refine ⟨1162161416152885133294995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1549548554870513511059993 1162161416152885133294995)
            ·
              refine ⟨1743242124229327699942493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162161416152885133294995 1743242124229327699942493)
              ·
                refine ⟨653715796585997887478435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1743242124229327699942493 653715796585997887478435)
                ·
                  refine ⟨980573694878996831217653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653715796585997887478435 980573694878996831217653)
                  ·
                    refine ⟨91928783894905952926655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 980573694878996831217653 91928783894905952926655)
                    ·
                      rfl

theorem cell23_537092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_537092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537092 prefixEnd_537092 := by exact prefixLift 537092
  have htrace : WordTrace (prefixWord ++ tailWord_537092) baseStart_537092 baseEnd_537092 := by
    simpa [prefixWord, tailWord_537092, baseEnd_537092] using wordTrace_append hprefix tailTrace_537092
  have hstable : (prefixWord ++ tailWord_537092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537092).length < 2 ^ (prefixWord ++ tailWord_537092).sum := by decide
  have hdescent : baseEnd_537092 < baseStart_537092 := by decide
  rcases family_descends (prefixWord ++ tailWord_537092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537105 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 2, 4]
def baseStart_537105 : Nat := 118140960795 + 537105 * 2 ^ 59
def prefixEnd_537105 : Nat := 4983230072969 + 3 ^ 40 * 537105 * 2
def baseEnd_537105 : Nat := 91931008977742102639135

theorem tailTrace_537105 : CollatzResearch.WordTrace tailWord_537105 prefixEnd_537105 91931008977742102639135 := by
  unfold tailWord_537105
  simp only [CollatzResearch.WordTrace]
  refine ⟨19589828719167790076092769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13059885812778526717395179 19589828719167790076092769)
  ·
    refine ⟨14692371539375842557069577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19589828719167790076092769 14692371539375842557069577)
    ·
      refine ⟨11019278654531881917802183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14692371539375842557069577 11019278654531881917802183)
      ·
        refine ⟨16528917981797822876703275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11019278654531881917802183 16528917981797822876703275)
        ·
          refine ⟨24793376972696734315054913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16528917981797822876703275 24793376972696734315054913)
          ·
            refine ⟨18595032729522550736291185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24793376972696734315054913 18595032729522550736291185)
            ·
              refine ⟨13946274547141913052218389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18595032729522550736291185 13946274547141913052218389)
              ·
                refine ⟨653731619397277174322737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13946274547141913052218389 653731619397277174322737)
                ·
                  refine ⟨490298714547957880742053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 653731619397277174322737 490298714547957880742053)
                  ·
                    refine ⟨91931008977742102639135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 490298714547957880742053 91931008977742102639135)
                    ·
                      rfl

theorem cell23_537105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_537105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537105 prefixEnd_537105 := by exact prefixLift 537105
  have htrace : WordTrace (prefixWord ++ tailWord_537105) baseStart_537105 baseEnd_537105 := by
    simpa [prefixWord, tailWord_537105, baseEnd_537105] using wordTrace_append hprefix tailTrace_537105
  have hstable : (prefixWord ++ tailWord_537105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537105).length < 2 ^ (prefixWord ++ tailWord_537105).sum := by decide
  have hdescent : baseEnd_537105 < baseStart_537105 := by decide
  rcases family_descends (prefixWord ++ tailWord_537105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537125 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 4]
def baseStart_537125 : Nat := 118140960795 + 537125 * 2 ^ 59
def prefixEnd_537125 : Nat := 4983230072969 + 3 ^ 40 * 537125 * 2
def baseEnd_537125 : Nat := 275803296546316229667313

theorem tailTrace_537125 : CollatzResearch.WordTrace tailWord_537125 prefixEnd_537125 275803296546316229667313 := by
  unfold tailWord_537125
  simp only [CollatzResearch.WordTrace]
  refine ⟨19590558179095333491820829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13060372119396888994547219 19590558179095333491820829)
  ·
    refine ⟨7346459317160750059432811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19590558179095333491820829 7346459317160750059432811)
    ·
      refine ⟨11019688975741125089149217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7346459317160750059432811 11019688975741125089149217)
      ·
        refine ⟨8264766731805843816861913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11019688975741125089149217 8264766731805843816861913)
        ·
          refine ⟨6198575048854382862646435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8264766731805843816861913 6198575048854382862646435)
          ·
            refine ⟨9297862573281574293969653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6198575048854382862646435 9297862573281574293969653)
            ·
              refine ⟨871674616245147590059655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9297862573281574293969653 871674616245147590059655)
              ·
                refine ⟨1307511924367721385089483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871674616245147590059655 1307511924367721385089483)
                ·
                  refine ⟨1961267886551582077634225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307511924367721385089483 1961267886551582077634225)
                  ·
                    refine ⟨1470950914913686558225669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1961267886551582077634225 1470950914913686558225669)
                    ·
                      refine ⟨275803296546316229667313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1470950914913686558225669 275803296546316229667313)
                      ·
                        rfl

theorem cell23_537125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_537125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537125 prefixEnd_537125 := by exact prefixLift 537125
  have htrace : WordTrace (prefixWord ++ tailWord_537125) baseStart_537125 baseEnd_537125 := by
    simpa [prefixWord, tailWord_537125, baseEnd_537125] using wordTrace_append hprefix tailTrace_537125
  have hstable : (prefixWord ++ tailWord_537125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537125).length < 2 ^ (prefixWord ++ tailWord_537125).sum := by decide
  have hdescent : baseEnd_537125 < baseStart_537125 := by decide
  rcases family_descends (prefixWord ++ tailWord_537125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537140 : List Nat := [2, 5, 1, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_537140 : Nat := 118140960795 + 537140 * 2 ^ 59
def prefixEnd_537140 : Nat := 4983230072969 + 3 ^ 40 * 537140 * 2
def baseEnd_537140 : Nat := 275810998756133670979745

theorem tailTrace_537140 : CollatzResearch.WordTrace tailWord_537140 prefixEnd_537140 275810998756133670979745 := by
  unfold tailWord_537140
  simp only [CollatzResearch.WordTrace]
  refine ⟨9795552637020495526808437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13060736849360660702411249 9795552637020495526808437)
  ·
    refine ⟨918333059720671455638291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9795552637020495526808437 918333059720671455638291)
    ·
      refine ⟨1377499589581007183457437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 918333059720671455638291 1377499589581007183457437)
      ·
        refine ⟨516562346092877693796539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1377499589581007183457437 516562346092877693796539)
        ·
          refine ⟨774843519139316540694809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516562346092877693796539 774843519139316540694809)
          ·
            refine ⟨581132639354487405521107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774843519139316540694809 581132639354487405521107)
            ·
              refine ⟨871698959031731108281661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581132639354487405521107 871698959031731108281661)
              ·
                refine ⟨326887109636899165605623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 871698959031731108281661 326887109636899165605623)
                ·
                  refine ⟨490330664455348748408435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326887109636899165605623 490330664455348748408435)
                  ·
                    refine ⟨735495996683023122612653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 490330664455348748408435 735495996683023122612653)
                    ·
                      refine ⟨275810998756133670979745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 735495996683023122612653 275810998756133670979745)
                      ·
                        rfl

theorem cell23_537140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_537140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537140 prefixEnd_537140 := by exact prefixLift 537140
  have htrace : WordTrace (prefixWord ++ tailWord_537140) baseStart_537140 baseEnd_537140 := by
    simpa [prefixWord, tailWord_537140, baseEnd_537140] using wordTrace_append hprefix tailTrace_537140
  have hstable : (prefixWord ++ tailWord_537140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537140).length < 2 ^ (prefixWord ++ tailWord_537140).sum := by decide
  have hdescent : baseEnd_537140 < baseStart_537140 := by decide
  rcases family_descends (prefixWord ++ tailWord_537140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537145 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 3, 3, 3]
def baseStart_537145 : Nat := 118140960795 + 537145 * 2 ^ 59
def prefixEnd_537145 : Nat := 4983230072969 + 3 ^ 40 * 537145 * 2
def baseEnd_537145 : Nat := 275813566159406151417221

theorem tailTrace_537145 : CollatzResearch.WordTrace tailWord_537145 prefixEnd_537145 275813566159406151417221 := by
  unfold tailWord_537145
  simp only [CollatzResearch.WordTrace]
  refine ⟨19591287639022876907548889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13060858426015251271699259 19591287639022876907548889)
  ·
    refine ⟨14693465729267157680661667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19591287639022876907548889 14693465729267157680661667)
    ·
      refine ⟨22040198593900736520992501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14693465729267157680661667 22040198593900736520992501)
      ·
        refine ⟨2066268618178194048843047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22040198593900736520992501 2066268618178194048843047)
        ·
          refine ⟨3099402927267291073264571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2066268618178194048843047 3099402927267291073264571)
          ·
            refine ⟨4649104390900936609896857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099402927267291073264571 4649104390900936609896857)
            ·
              refine ⟨3486828293175702457422643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4649104390900936609896857 3486828293175702457422643)
              ·
                refine ⟨5230242439763553686133965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3486828293175702457422643 5230242439763553686133965)
                ·
                  refine ⟨1961340914911332632300237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5230242439763553686133965 1961340914911332632300237)
                  ·
                    refine ⟨735502843091749737112589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961340914911332632300237 735502843091749737112589)
                    ·
                      refine ⟨275813566159406151417221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 735502843091749737112589 275813566159406151417221)
                      ·
                        rfl

theorem cell23_537145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_537145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537145 prefixEnd_537145 := by exact prefixLift 537145
  have htrace : WordTrace (prefixWord ++ tailWord_537145) baseStart_537145 baseEnd_537145 := by
    simpa [prefixWord, tailWord_537145, baseEnd_537145] using wordTrace_append hprefix tailTrace_537145
  have hstable : (prefixWord ++ tailWord_537145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537145).length < 2 ^ (prefixWord ++ tailWord_537145).sum := by decide
  have hdescent : baseEnd_537145 < baseStart_537145 := by decide
  rcases family_descends (prefixWord ++ tailWord_537145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537146 : List Nat := [3, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2]
def baseStart_537146 : Nat := 118140960795 + 537146 * 2 ^ 59
def prefixEnd_537146 : Nat := 4983230072969 + 3 ^ 40 * 537146 * 2
def baseEnd_537146 : Nat := 275814079640060647504717

theorem tailTrace_537146 : CollatzResearch.WordTrace tailWord_537146 prefixEnd_537146 275814079640060647504717 := by
  unfold tailWord_537146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4897831028004813519583823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13060882741346169385556861 4897831028004813519583823)
  ·
    refine ⟨7346746542007220279375735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4897831028004813519583823 7346746542007220279375735)
    ·
      refine ⟨11020119813010830419063603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7346746542007220279375735 11020119813010830419063603)
      ·
        refine ⟨16530179719516245628595405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11020119813010830419063603 16530179719516245628595405)
        ·
          refine ⟨6198817394818592110723277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16530179719516245628595405 6198817394818592110723277)
          ·
            refine ⟨2324556523056972041521229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6198817394818592110723277 2324556523056972041521229)
            ·
              refine ⟨871708696146364515570461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2324556523056972041521229 871708696146364515570461)
              ·
                refine ⟨326890761054886693338923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 871708696146364515570461 326890761054886693338923)
                ·
                  refine ⟨490336141582330040008385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326890761054886693338923 490336141582330040008385)
                  ·
                    refine ⟨367752106186747530006289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 490336141582330040008385 367752106186747530006289)
                    ·
                      refine ⟨275814079640060647504717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 367752106186747530006289 275814079640060647504717)
                      ·
                        rfl

theorem cell23_537146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2].length) (baseStart_537146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537146 prefixEnd_537146 := by exact prefixLift 537146
  have htrace : WordTrace (prefixWord ++ tailWord_537146) baseStart_537146 baseEnd_537146 := by
    simpa [prefixWord, tailWord_537146, baseEnd_537146] using wordTrace_append hprefix tailTrace_537146
  have hstable : (prefixWord ++ tailWord_537146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537146).length < 2 ^ (prefixWord ++ tailWord_537146).sum := by decide
  have hdescent : baseEnd_537146 < baseStart_537146 := by decide
  rcases family_descends (prefixWord ++ tailWord_537146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537162 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_537162 : Nat := 118140960795 + 537162 * 2 ^ 59
def prefixEnd_537162 : Nat := 4983230072969 + 3 ^ 40 * 537162 * 2
def baseEnd_537162 : Nat := 275822295330532584904643

theorem tailTrace_537162 : CollatzResearch.WordTrace tailWord_537162 prefixEnd_537162 275822295330532584904643 := by
  unfold tailWord_537162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4897976919990322202729435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13061271786640859207278493 4897976919990322202729435)
  ·
    refine ⟨7346965379985483304094153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4897976919990322202729435 7346965379985483304094153)
    ·
      refine ⟨5510224034989112478070615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7346965379985483304094153 5510224034989112478070615)
      ·
        refine ⟨8265336052483668717105923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5510224034989112478070615 8265336052483668717105923)
        ·
          refine ⟨12398004078725503075658885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8265336052483668717105923 12398004078725503075658885)
          ·
            refine ⟨2324625764761031826686041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12398004078725503075658885 2324625764761031826686041)
            ·
              refine ⟨1743469323570773870014531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2324625764761031826686041 1743469323570773870014531)
              ·
                refine ⟨2615203985356160805021797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1743469323570773870014531 2615203985356160805021797)
                ·
                  refine ⟨490350747254280150941587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2615203985356160805021797 490350747254280150941587)
                  ·
                    refine ⟨735526120881420226412381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 490350747254280150941587 735526120881420226412381)
                    ·
                      refine ⟨275822295330532584904643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 735526120881420226412381 275822295330532584904643)
                      ·
                        rfl

theorem cell23_537162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_537162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537162 prefixEnd_537162 := by exact prefixLift 537162
  have htrace : WordTrace (prefixWord ++ tailWord_537162) baseStart_537162 baseEnd_537162 := by
    simpa [prefixWord, tailWord_537162, baseEnd_537162] using wordTrace_append hprefix tailTrace_537162
  have hstable : (prefixWord ++ tailWord_537162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537162).length < 2 ^ (prefixWord ++ tailWord_537162).sum := by decide
  have hdescent : baseEnd_537162 < baseStart_537162 := by decide
  rcases family_descends (prefixWord ++ tailWord_537162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537189 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 3, 3, 2]
def baseStart_537189 : Nat := 118140960795 + 537189 * 2 ^ 59
def prefixEnd_537189 : Nat := 4983230072969 + 3 ^ 40 * 537189 * 2
def baseEnd_537189 : Nat := 275836159308203979267019

theorem tailTrace_537189 : CollatzResearch.WordTrace tailWord_537189 prefixEnd_537189 275836159308203979267019 := by
  unfold tailWord_537189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19592892450863472422150621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13061928300575648281433747 19592892450863472422150621)
  ·
    refine ⟨7347334669073802158306483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19592892450863472422150621 7347334669073802158306483)
    ·
      refine ⟨11021002003610703237459725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7347334669073802158306483 11021002003610703237459725)
      ·
        refine ⟨4132875751354013714047397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11021002003610703237459725 4132875751354013714047397)
        ·
          refine ⟨774914203378877571383887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4132875751354013714047397 774914203378877571383887)
          ·
            refine ⟨1162371305068316357075831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774914203378877571383887 1162371305068316357075831)
            ·
              refine ⟨1743556957602474535613747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162371305068316357075831 1743556957602474535613747)
              ·
                refine ⟨2615335436403711803420621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1743556957602474535613747 2615335436403711803420621)
                ·
                  refine ⟨980750788651391926282733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2615335436403711803420621 980750788651391926282733)
                  ·
                    refine ⟨367781545744271972356025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 980750788651391926282733 367781545744271972356025)
                    ·
                      refine ⟨275836159308203979267019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 367781545744271972356025 275836159308203979267019)
                      ·
                        rfl

theorem cell23_537189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_537189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537189 prefixEnd_537189 := by exact prefixLift 537189
  have htrace : WordTrace (prefixWord ++ tailWord_537189) baseStart_537189 baseEnd_537189 := by
    simpa [prefixWord, tailWord_537189, baseEnd_537189] using wordTrace_append hprefix tailTrace_537189
  have hstable : (prefixWord ++ tailWord_537189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537189).length < 2 ^ (prefixWord ++ tailWord_537189).sum := by decide
  have hdescent : baseEnd_537189 < baseStart_537189 := by decide
  rcases family_descends (prefixWord ++ tailWord_537189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537208 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 9]
def baseStart_537208 : Nat := 118140960795 + 537208 * 2 ^ 59
def prefixEnd_537208 : Nat := 4983230072969 + 3 ^ 40 * 537208 * 2
def baseEnd_537208 : Nat := 30649546160071044992159

theorem tailTrace_537208 : CollatzResearch.WordTrace tailWord_537208 prefixEnd_537208 30649546160071044992159 := by
  unfold tailWord_537208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9796792718897319333546139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13062390291863092444728185 9796792718897319333546139)
  ·
    refine ⟨14695189078345979000319209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9796792718897319333546139 14695189078345979000319209)
    ·
      refine ⟨11021391808759484250239407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14695189078345979000319209 11021391808759484250239407)
      ·
        refine ⟨16532087713139226375359111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11021391808759484250239407 16532087713139226375359111)
        ·
          refine ⟨24798131569708839563038667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16532087713139226375359111 24798131569708839563038667)
          ·
            refine ⟨37197197354563259344558001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24798131569708839563038667 37197197354563259344558001)
            ·
              refine ⟨27897898015922444508418501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37197197354563259344558001 27897898015922444508418501)
              ·
                refine ⟨5230855877985458345328469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27897898015922444508418501 5230855877985458345328469)
                ·
                  refine ⟨30649546160071044992159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5230855877985458345328469 30649546160071044992159)
                  ·
                    rfl

theorem cell23_537208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 9].length) (baseStart_537208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537208 prefixEnd_537208 := by exact prefixLift 537208
  have htrace : WordTrace (prefixWord ++ tailWord_537208) baseStart_537208 baseEnd_537208 := by
    simpa [prefixWord, tailWord_537208, baseEnd_537208] using wordTrace_append hprefix tailTrace_537208
  have hstable : (prefixWord ++ tailWord_537208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537208).length < 2 ^ (prefixWord ++ tailWord_537208).sum := by decide
  have hdescent : baseEnd_537208 < baseStart_537208 := by decide
  rcases family_descends (prefixWord ++ tailWord_537208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537219 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 2, 2, 2]
def baseStart_537219 : Nat := 118140960795 + 537219 * 2 ^ 59
def prefixEnd_537219 : Nat := 4983230072969 + 3 ^ 40 * 537219 * 2
def baseEnd_537219 : Nat := 275851563727838861891881

theorem tailTrace_537219 : CollatzResearch.WordTrace tailWord_537219 prefixEnd_537219 275851563727838861891881 := by
  unfold tailWord_537219
  simp only [CollatzResearch.WordTrace]
  refine ⟨19593986640754787545742711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13062657760503191697161807 19593986640754787545742711)
  ·
    refine ⟨29390979961132181318614067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19593986640754787545742711 29390979961132181318614067)
    ·
      refine ⟨44086469941698271977921101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29390979961132181318614067 44086469941698271977921101)
      ·
        refine ⟨16532426228136851991720413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44086469941698271977921101 16532426228136851991720413)
        ·
          refine ⟨6199659835551319496895155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16532426228136851991720413 6199659835551319496895155)
          ·
            refine ⟨9299489753326979245342733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6199659835551319496895155 9299489753326979245342733)
            ·
              refine ⟨3487308657497617217003525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9299489753326979245342733 3487308657497617217003525)
              ·
                refine ⟨653870373280803228188161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3487308657497617217003525 653870373280803228188161)
                ·
                  refine ⟨490402779960602421141121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 653870373280803228188161 490402779960602421141121)
                  ·
                    refine ⟨367802084970451815855841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 490402779960602421141121 367802084970451815855841)
                    ·
                      refine ⟨275851563727838861891881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 367802084970451815855841 275851563727838861891881)
                      ·
                        rfl

theorem cell23_537219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_537219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537219 prefixEnd_537219 := by exact prefixLift 537219
  have htrace : WordTrace (prefixWord ++ tailWord_537219) baseStart_537219 baseEnd_537219 := by
    simpa [prefixWord, tailWord_537219, baseEnd_537219] using wordTrace_append hprefix tailTrace_537219
  have hstable : (prefixWord ++ tailWord_537219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537219).length < 2 ^ (prefixWord ++ tailWord_537219).sum := by decide
  have hdescent : baseEnd_537219 < baseStart_537219 := by decide
  rcases family_descends (prefixWord ++ tailWord_537219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537235 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 3]
def baseStart_537235 : Nat := 118140960795 + 537235 * 2 ^ 59
def prefixEnd_537235 : Nat := 4983230072969 + 3 ^ 40 * 537235 * 2
def baseEnd_537235 : Nat := 275859779418310799291807

theorem tailTrace_537235 : CollatzResearch.WordTrace tailWord_537235 prefixEnd_537235 275859779418310799291807 := by
  unfold tailWord_537235
  simp only [CollatzResearch.WordTrace]
  refine ⟨19594570208696822278325159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13063046805797881518883439 19594570208696822278325159)
  ·
    refine ⟨29391855313045233417487739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19594570208696822278325159 29391855313045233417487739)
    ·
      refine ⟨44087782969567850126231609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29391855313045233417487739 44087782969567850126231609)
      ·
        refine ⟨33065837227175887594673707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44087782969567850126231609 33065837227175887594673707)
        ·
          refine ⟨49598755840763831392010561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33065837227175887594673707 49598755840763831392010561)
          ·
            refine ⟨37199066880572873544007921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49598755840763831392010561 37199066880572873544007921)
            ·
              refine ⟨27899300160429655158005941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37199066880572873544007921 27899300160429655158005941)
              ·
                refine ⟨2615559390040280171063057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27899300160429655158005941 2615559390040280171063057)
                ·
                  refine ⟨1961669542530210128297293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2615559390040280171063057 1961669542530210128297293)
                  ·
                    refine ⟨735626078448828798111485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961669542530210128297293 735626078448828798111485)
                    ·
                      refine ⟨275859779418310799291807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 735626078448828798111485 275859779418310799291807)
                      ·
                        rfl

theorem cell23_537235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 3].length) (baseStart_537235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537235 prefixEnd_537235 := by exact prefixLift 537235
  have htrace : WordTrace (prefixWord ++ tailWord_537235) baseStart_537235 baseEnd_537235 := by
    simpa [prefixWord, tailWord_537235, baseEnd_537235] using wordTrace_append hprefix tailTrace_537235
  have hstable : (prefixWord ++ tailWord_537235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537235).length < 2 ^ (prefixWord ++ tailWord_537235).sum := by decide
  have hdescent : baseEnd_537235 < baseStart_537235 := by decide
  rcases family_descends (prefixWord ++ tailWord_537235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537236 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_537236 : Nat := 118140960795 + 537236 * 2 ^ 59
def prefixEnd_537236 : Nat := 4983230072969 + 3 ^ 40 * 537236 * 2
def baseEnd_537236 : Nat := 275860292898965295379303

theorem tailTrace_537236 : CollatzResearch.WordTrace tailWord_537236 prefixEnd_537236 275860292898965295379303 := by
  unfold tailWord_537236
  simp only [CollatzResearch.WordTrace]
  refine ⟨9797303340846599724555781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13063071121128799632741041 9797303340846599724555781)
  ·
    refine ⟨1836994376408737448354209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9797303340846599724555781 1836994376408737448354209)
    ·
      refine ⟨1377745782306553086265657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1836994376408737448354209 1377745782306553086265657)
      ·
        refine ⟨1033309336729914814699243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1377745782306553086265657 1033309336729914814699243)
        ·
          refine ⟨1549964005094872222048865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033309336729914814699243 1549964005094872222048865)
          ·
            refine ⟨1162473003821154166536649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1549964005094872222048865 1162473003821154166536649)
            ·
              refine ⟨871854752865865624902487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1162473003821154166536649 871854752865865624902487)
              ·
                refine ⟨1307782129298798437353731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871854752865865624902487 1307782129298798437353731)
                ·
                  refine ⟨1961673193948197656030597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307782129298798437353731 1961673193948197656030597)
                  ·
                    refine ⟨367813723865287060505737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1961673193948197656030597 367813723865287060505737)
                    ·
                      refine ⟨275860292898965295379303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 367813723865287060505737 275860292898965295379303)
                      ·
                        rfl

theorem cell23_537236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_537236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537236 prefixEnd_537236 := by exact prefixLift 537236
  have htrace : WordTrace (prefixWord ++ tailWord_537236) baseStart_537236 baseEnd_537236 := by
    simpa [prefixWord, tailWord_537236, baseEnd_537236] using wordTrace_append hprefix tailTrace_537236
  have hstable : (prefixWord ++ tailWord_537236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537236).length < 2 ^ (prefixWord ++ tailWord_537236).sum := by decide
  have hdescent : baseEnd_537236 < baseStart_537236 := by decide
  rcases family_descends (prefixWord ++ tailWord_537236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537292 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_537292 : Nat := 118140960795 + 537292 * 2 ^ 59
def prefixEnd_537292 : Nat := 4983230072969 + 3 ^ 40 * 537292 * 2
def baseEnd_537292 : Nat := 275889047815617076279045

theorem tailTrace_537292 : CollatzResearch.WordTrace tailWord_537292 prefixEnd_537292 275889047815617076279045 := by
  unfold tailWord_537292
  simp only [CollatzResearch.WordTrace]
  refine ⟨9798324584745160506575065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13064432779660214008766753 9798324584745160506575065)
  ·
    refine ⟨7348743438558870379931299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9798324584745160506575065 7348743438558870379931299)
    ·
      refine ⟨11023115157838305569896949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7348743438558870379931299 11023115157838305569896949)
      ·
        refine ⟨1033417046047341147177839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11023115157838305569896949 1033417046047341147177839)
        ·
          refine ⟨1550125569071011720766759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033417046047341147177839 1550125569071011720766759)
          ·
            refine ⟨2325188353606517581150139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550125569071011720766759 2325188353606517581150139)
            ·
              refine ⟨3487782530409776371725209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325188353606517581150139 3487782530409776371725209)
              ·
                refine ⟨2615836897807332278793907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3487782530409776371725209 2615836897807332278793907)
                ·
                  refine ⟨3923755346710998418190861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615836897807332278793907 3923755346710998418190861)
                  ·
                    refine ⟨1471408255016624406821573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3923755346710998418190861 1471408255016624406821573)
                    ·
                      refine ⟨275889047815617076279045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1471408255016624406821573 275889047815617076279045)
                      ·
                        rfl

theorem cell23_537292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_537292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537292 prefixEnd_537292 := by exact prefixLift 537292
  have htrace : WordTrace (prefixWord ++ tailWord_537292) baseStart_537292 baseEnd_537292 := by
    simpa [prefixWord, tailWord_537292, baseEnd_537292] using wordTrace_append hprefix tailTrace_537292
  have hstable : (prefixWord ++ tailWord_537292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537292).length < 2 ^ (prefixWord ++ tailWord_537292).sum := by decide
  have hdescent : baseEnd_537292 < baseStart_537292 := by decide
  rcases family_descends (prefixWord ++ tailWord_537292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537305 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_537305 : Nat := 118140960795 + 537305 * 2 ^ 59
def prefixEnd_537305 : Nat := 4983230072969 + 3 ^ 40 * 537305 * 2
def baseEnd_537305 : Nat := 275895723064125525416485

theorem tailTrace_537305 : CollatzResearch.WordTrace tailWord_537305 prefixEnd_537305 275895723064125525416485 := by
  unfold tailWord_537305
  simp only [CollatzResearch.WordTrace]
  refine ⟨19597123318443224233373369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13064748878962149488915579 19597123318443224233373369)
  ·
    refine ⟨14697842488832418175030027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19597123318443224233373369 14697842488832418175030027)
    ·
      refine ⟨22046763733248627262545041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14697842488832418175030027 22046763733248627262545041)
      ·
        refine ⟨16535072799936470446908781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22046763733248627262545041 16535072799936470446908781)
        ·
          refine ⟨6200652299976176417590793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16535072799936470446908781 6200652299976176417590793)
          ·
            refine ⟨4650489224982132313193095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6200652299976176417590793 4650489224982132313193095)
            ·
              refine ⟨6975733837473198469789643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650489224982132313193095 6975733837473198469789643)
              ·
                refine ⟨10463600756209797704684465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6975733837473198469789643 10463600756209797704684465)
                ·
                  refine ⟨7847700567157348278513349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10463600756209797704684465 7847700567157348278513349)
                  ·
                    refine ⟨1471443856342002802221253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7847700567157348278513349 1471443856342002802221253)
                    ·
                      refine ⟨275895723064125525416485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1471443856342002802221253 275895723064125525416485)
                      ·
                        rfl

theorem cell23_537305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_537305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537305 prefixEnd_537305 := by exact prefixLift 537305
  have htrace : WordTrace (prefixWord ++ tailWord_537305) baseStart_537305 baseEnd_537305 := by
    simpa [prefixWord, tailWord_537305, baseEnd_537305] using wordTrace_append hprefix tailTrace_537305
  have hstable : (prefixWord ++ tailWord_537305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537305).length < 2 ^ (prefixWord ++ tailWord_537305).sum := by decide
  have hdescent : baseEnd_537305 < baseStart_537305 := by decide
  rcases family_descends (prefixWord ++ tailWord_537305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537312 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 3]
def baseStart_537312 : Nat := 118140960795 + 537312 * 2 ^ 59
def prefixEnd_537312 : Nat := 4983230072969 + 3 ^ 40 * 537312 * 2
def baseEnd_537312 : Nat := 275899317428706998028953

theorem tailTrace_537312 : CollatzResearch.WordTrace tailWord_537312 prefixEnd_537312 275899317428706998028953 := by
  unfold tailWord_537312
  simp only [CollatzResearch.WordTrace]
  refine ⟨9798689314708932214439095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13064919086278576285918793 9798689314708932214439095)
  ·
    refine ⟨14698033972063398321658643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9798689314708932214439095 14698033972063398321658643)
    ·
      refine ⟨22047050958095097482487965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14698033972063398321658643 22047050958095097482487965)
      ·
        refine ⟨8267644109285661555932987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22047050958095097482487965 8267644109285661555932987)
        ·
          refine ⟨12401466163928492333899481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8267644109285661555932987 12401466163928492333899481)
          ·
            refine ⟨9301099622946369250424611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12401466163928492333899481 9301099622946369250424611)
            ·
              refine ⟨13951649434419553875636917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9301099622946369250424611 13951649434419553875636917)
              ·
                refine ⟨1307967134476833175840961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13951649434419553875636917 1307967134476833175840961)
                ·
                  refine ⟨980975350857624881880721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1307967134476833175840961 980975350857624881880721)
                  ·
                    refine ⟨735731513143218661410541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 980975350857624881880721 735731513143218661410541)
                    ·
                      refine ⟨275899317428706998028953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 735731513143218661410541 275899317428706998028953)
                      ·
                        rfl

theorem cell23_537312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_537312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537312 prefixEnd_537312 := by exact prefixLift 537312
  have htrace : WordTrace (prefixWord ++ tailWord_537312) baseStart_537312 baseEnd_537312 := by
    simpa [prefixWord, tailWord_537312, baseEnd_537312] using wordTrace_append hprefix tailTrace_537312
  have hstable : (prefixWord ++ tailWord_537312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537312).length < 2 ^ (prefixWord ++ tailWord_537312).sum := by decide
  have hdescent : baseEnd_537312 < baseStart_537312 := by decide
  rcases family_descends (prefixWord ++ tailWord_537312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537336 : List Nat := [2, 1, 2, 1, 1, 2, 7, 2, 1, 4]
def baseStart_537336 : Nat := 118140960795 + 537336 * 2 ^ 59
def prefixEnd_537336 : Nat := 4983230072969 + 3 ^ 40 * 537336 * 2
def baseEnd_537336 : Nat := 91970546988138301376281

theorem tailTrace_537336 : CollatzResearch.WordTrace tailWord_537336 prefixEnd_537336 91970546988138301376281 := by
  unfold tailWord_537336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9799126990665458263875931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13065502654220611018501241 9799126990665458263875931)
  ·
    refine ⟨14698690485998187395813897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9799126990665458263875931 14698690485998187395813897)
    ·
      refine ⟨11024017864498640546860423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14698690485998187395813897 11024017864498640546860423)
      ·
        refine ⟨16536026796747960820290635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11024017864498640546860423 16536026796747960820290635)
        ·
          refine ⟨24804040195121941230435953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16536026796747960820290635 24804040195121941230435953)
          ·
            refine ⟨18603030146341455922826965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24804040195121941230435953 18603030146341455922826965)
            ·
              refine ⟨436008519054877873191257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18603030146341455922826965 436008519054877873191257)
              ·
                refine ⟨327006389291158404893443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436008519054877873191257 327006389291158404893443)
                ·
                  refine ⟨490509583936737607340165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327006389291158404893443 490509583936737607340165)
                  ·
                    refine ⟨91970546988138301376281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 490509583936737607340165 91970546988138301376281)
                    ·
                      rfl

theorem cell23_537336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_537336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537336 prefixEnd_537336 := by exact prefixLift 537336
  have htrace : WordTrace (prefixWord ++ tailWord_537336) baseStart_537336 baseEnd_537336 := by
    simpa [prefixWord, tailWord_537336, baseEnd_537336] using wordTrace_append hprefix tailTrace_537336
  have hstable : (prefixWord ++ tailWord_537336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537336).length < 2 ^ (prefixWord ++ tailWord_537336).sum := by decide
  have hdescent : baseEnd_537336 < baseStart_537336 := by decide
  rcases family_descends (prefixWord ++ tailWord_537336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537345 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 2, 9]
def baseStart_537345 : Nat := 118140960795 + 537345 * 2 ^ 59
def prefixEnd_537345 : Nat := 4983230072969 + 3 ^ 40 * 537345 * 2
def baseEnd_537345 : Nat := 91972087430101789638767

theorem tailTrace_537345 : CollatzResearch.WordTrace tailWord_537345 prefixEnd_537345 91972087430101789638767 := by
  unfold tailWord_537345
  simp only [CollatzResearch.WordTrace]
  refine ⟨19598582238298311064829489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13065721492198874043219659 19598582238298311064829489)
  ·
    refine ⟨14698936678723733298622117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19598582238298311064829489 14698936678723733298622117)
    ·
      refine ⟨2756050627260699993491647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14698936678723733298622117 2756050627260699993491647)
      ·
        refine ⟨4134075940891049990237471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2756050627260699993491647 4134075940891049990237471)
        ·
          refine ⟨6201113911336574985356207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4134075940891049990237471 6201113911336574985356207)
          ·
            refine ⟨9301670867004862478034311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6201113911336574985356207 9301670867004862478034311)
            ·
              refine ⟨13952506300507293717051467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9301670867004862478034311 13952506300507293717051467)
              ·
                refine ⟨20928759450760940575577201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13952506300507293717051467 20928759450760940575577201)
                ·
                  refine ⟨15696569588070705431682901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20928759450760940575577201 15696569588070705431682901)
                  ·
                    refine ⟨91972087430101789638767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15696569588070705431682901 91972087430101789638767)
                    ·
                      rfl

theorem cell23_537345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_537345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537345 prefixEnd_537345 := by exact prefixLift 537345
  have htrace : WordTrace (prefixWord ++ tailWord_537345) baseStart_537345 baseEnd_537345 := by
    simpa [prefixWord, tailWord_537345, baseEnd_537345] using wordTrace_append hprefix tailTrace_537345
  have hstable : (prefixWord ++ tailWord_537345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537345).length < 2 ^ (prefixWord ++ tailWord_537345).sum := by decide
  have hdescent : baseEnd_537345 < baseStart_537345 := by decide
  rcases family_descends (prefixWord ++ tailWord_537345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537392 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 4, 4]
def baseStart_537392 : Nat := 118140960795 + 537392 * 2 ^ 59
def prefixEnd_537392 : Nat := 4983230072969 + 3 ^ 40 * 537392 * 2
def baseEnd_537392 : Nat := 91980131960355561676195

theorem tailTrace_537392 : CollatzResearch.WordTrace tailWord_537392 prefixEnd_537392 91980131960355561676195 := by
  unfold tailWord_537392
  simp only [CollatzResearch.WordTrace]
  refine ⟨9800148234564019045895215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13066864312752025394526953 9800148234564019045895215)
  ·
    refine ⟨14700222351846028568842823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9800148234564019045895215 14700222351846028568842823)
    ·
      refine ⟨22050333527769042853264235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14700222351846028568842823 22050333527769042853264235)
      ·
        refine ⟨33075500291653564279896353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22050333527769042853264235 33075500291653564279896353)
        ·
          refine ⟨24806625218740173209922265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33075500291653564279896353 24806625218740173209922265)
          ·
            refine ⟨18604968914055129907441699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24806625218740173209922265 18604968914055129907441699)
            ·
              refine ⟨27907453371082694861162549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18604968914055129907441699 27907453371082694861162549)
              ·
                refine ⟨2616323753539002643233989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27907453371082694861162549 2616323753539002643233989)
                ·
                  refine ⟨490560703788562995606373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2616323753539002643233989 490560703788562995606373)
                  ·
                    refine ⟨91980131960355561676195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 490560703788562995606373 91980131960355561676195)
                    ·
                      rfl

theorem cell23_537392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4, 4].length) (baseStart_537392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537392 prefixEnd_537392 := by exact prefixLift 537392
  have htrace : WordTrace (prefixWord ++ tailWord_537392) baseStart_537392 baseEnd_537392 := by
    simpa [prefixWord, tailWord_537392, baseEnd_537392] using wordTrace_append hprefix tailTrace_537392
  have hstable : (prefixWord ++ tailWord_537392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537392).length < 2 ^ (prefixWord ++ tailWord_537392).sum := by decide
  have hdescent : baseEnd_537392 < baseStart_537392 := by decide
  rcases family_descends (prefixWord ++ tailWord_537392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537416 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 3, 2, 2]
def baseStart_537416 : Nat := 118140960795 + 537416 * 2 ^ 59
def prefixEnd_537416 : Nat := 4983230072969 + 3 ^ 40 * 537416 * 2
def baseEnd_537416 : Nat := 275952719416774591128475

theorem tailTrace_537416 : CollatzResearch.WordTrace tailWord_537416 prefixEnd_537416 275952719416774591128475 := by
  unfold tailWord_537416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9800585910520545095332051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13067447880694060127109401 9800585910520545095332051)
  ·
    refine ⟨14700878865780817642998077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9800585910520545095332051 14700878865780817642998077)
    ·
      refine ⟨5512829574667806616124279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14700878865780817642998077 5512829574667806616124279)
      ·
        refine ⟨8269244362001709924186419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5512829574667806616124279 8269244362001709924186419)
        ·
          refine ⟨12403866543002564886279629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8269244362001709924186419 12403866543002564886279629)
          ·
            refine ⟨4651449953625961832354861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12403866543002564886279629 4651449953625961832354861)
            ·
              refine ⟨1744293732609735687133073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4651449953625961832354861 1744293732609735687133073)
              ·
                refine ⟨1308220299457301765349805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744293732609735687133073 1308220299457301765349805)
                ·
                  refine ⟨490582612296488162006177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1308220299457301765349805 490582612296488162006177)
                  ·
                    refine ⟨367936959222366121504633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 490582612296488162006177 367936959222366121504633)
                    ·
                      refine ⟨275952719416774591128475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 367936959222366121504633 275952719416774591128475)
                      ·
                        rfl

theorem cell23_537416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_537416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537416 prefixEnd_537416 := by exact prefixLift 537416
  have htrace : WordTrace (prefixWord ++ tailWord_537416) baseStart_537416 baseEnd_537416 := by
    simpa [prefixWord, tailWord_537416, baseEnd_537416] using wordTrace_append hprefix tailTrace_537416
  have hstable : (prefixWord ++ tailWord_537416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537416).length < 2 ^ (prefixWord ++ tailWord_537416).sum := by decide
  have hdescent : baseEnd_537416 < baseStart_537416 := by decide
  rcases family_descends (prefixWord ++ tailWord_537416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537433 : List Nat := [1, 2, 1, 2, 2, 4, 1, 5, 1, 2, 2]
def baseStart_537433 : Nat := 118140960795 + 537433 * 2 ^ 59
def prefixEnd_537433 : Nat := 4983230072969 + 3 ^ 40 * 537433 * 2
def baseEnd_537433 : Nat := 275961448587901024615897

theorem tailTrace_537433 : CollatzResearch.WordTrace tailWord_537433 prefixEnd_537433 275961448587901024615897 := by
  unfold tailWord_537433
  simp only [CollatzResearch.WordTrace]
  refine ⟨19601791861979502094032953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13067861241319668062688635 19601791861979502094032953)
  ·
    refine ⟨14701343896484626570524715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19601791861979502094032953 14701343896484626570524715)
    ·
      refine ⟨22052015844726939855787073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14701343896484626570524715 22052015844726939855787073)
      ·
        refine ⟨16539011883545204891840305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22052015844726939855787073 16539011883545204891840305)
        ·
          refine ⟨12404258912658903668880229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16539011883545204891840305 12404258912658903668880229)
          ·
            refine ⟨2325798546123544437915043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12404258912658903668880229 2325798546123544437915043)
            ·
              refine ⟨3488697819185316656872565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325798546123544437915043 3488697819185316656872565)
              ·
                refine ⟨327065420548623436581803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3488697819185316656872565 327065420548623436581803)
                ·
                  refine ⟨490598130822935154872705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327065420548623436581803 490598130822935154872705)
                  ·
                    refine ⟨367948598117201366154529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 490598130822935154872705 367948598117201366154529)
                    ·
                      refine ⟨275961448587901024615897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 367948598117201366154529 275961448587901024615897)
                      ·
                        rfl

theorem cell23_537433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 1, 2, 2].length) (baseStart_537433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537433 prefixEnd_537433 := by exact prefixLift 537433
  have htrace : WordTrace (prefixWord ++ tailWord_537433) baseStart_537433 baseEnd_537433 := by
    simpa [prefixWord, tailWord_537433, baseEnd_537433] using wordTrace_append hprefix tailTrace_537433
  have hstable : (prefixWord ++ tailWord_537433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537433).length < 2 ^ (prefixWord ++ tailWord_537433).sum := by decide
  have hdescent : baseEnd_537433 < baseStart_537433 := by decide
  rcases family_descends (prefixWord ++ tailWord_537433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537459 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 5, 3, 2]
def baseStart_537459 : Nat := 118140960795 + 537459 * 2 ^ 59
def prefixEnd_537459 : Nat := 4983230072969 + 3 ^ 40 * 537459 * 2
def baseEnd_537459 : Nat := 275974799084917922890777

theorem tailTrace_537459 : CollatzResearch.WordTrace tailWord_537459 prefixEnd_537459 275974799084917922890777 := by
  unfold tailWord_537459
  simp only [CollatzResearch.WordTrace]
  refine ⟨19602740159885308534479431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13068493439923539022986287 19602740159885308534479431)
  ·
    refine ⟨29404110239827962801719147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19602740159885308534479431 29404110239827962801719147)
    ·
      refine ⟨44106165359741944202578721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29404110239827962801719147 44106165359741944202578721)
      ·
        refine ⟨33079624019806458151934041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44106165359741944202578721 33079624019806458151934041)
        ·
          refine ⟨24809718014854843613950531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33079624019806458151934041 24809718014854843613950531)
          ·
            refine ⟨37214577022282265420925797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24809718014854843613950531 37214577022282265420925797)
            ·
              refine ⟨6977733191677924766423587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37214577022282265420925797 6977733191677924766423587)
              ·
                refine ⟨10466599787516887149635381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6977733191677924766423587 10466599787516887149635381)
                ·
                  refine ⟨981243730079708170278317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10466599787516887149635381 981243730079708170278317)
                  ·
                    refine ⟨367966398779890563854369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 981243730079708170278317 367966398779890563854369)
                    ·
                      refine ⟨275974799084917922890777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 367966398779890563854369 275974799084917922890777)
                      ·
                        rfl

theorem cell23_537459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 3, 2].length) (baseStart_537459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537459 prefixEnd_537459 := by exact prefixLift 537459
  have htrace : WordTrace (prefixWord ++ tailWord_537459) baseStart_537459 baseEnd_537459 := by
    simpa [prefixWord, tailWord_537459, baseEnd_537459] using wordTrace_append hprefix tailTrace_537459
  have hstable : (prefixWord ++ tailWord_537459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537459).length < 2 ^ (prefixWord ++ tailWord_537459).sum := by decide
  have hdescent : baseEnd_537459 < baseStart_537459 := by decide
  rcases family_descends (prefixWord ++ tailWord_537459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537470 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_537470 : Nat := 118140960795 + 537470 * 2 ^ 59
def prefixEnd_537470 : Nat := 4983230072969 + 3 ^ 40 * 537470 * 2
def baseEnd_537470 : Nat := 275980447372117379853227

theorem tailTrace_537470 : CollatzResearch.WordTrace tailWord_537470 prefixEnd_537470 275980447372117379853227 := by
  unfold tailWord_537470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450392670355682176641233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13068760908563638275419909 2450392670355682176641233)
  ·
    refine ⟨1837794502766761632480925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2450392670355682176641233 1837794502766761632480925)
    ·
      refine ⟨689172938537535612180347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1837794502766761632480925 689172938537535612180347)
      ·
        refine ⟨1033759407806303418270521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689172938537535612180347 1033759407806303418270521)
        ·
          refine ⟨775319555854727563702891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1033759407806303418270521 775319555854727563702891)
          ·
            refine ⟨1162979333782091345554337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775319555854727563702891 1162979333782091345554337)
            ·
              refine ⟨872234500336568509165753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1162979333782091345554337 872234500336568509165753)
              ·
                refine ⟨654175875252426381874315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872234500336568509165753 654175875252426381874315)
                ·
                  refine ⟨981263812878639572811473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654175875252426381874315 981263812878639572811473)
                  ·
                    refine ⟨735947859658979679608605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 981263812878639572811473 735947859658979679608605)
                    ·
                      refine ⟨275980447372117379853227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 735947859658979679608605 275980447372117379853227)
                      ·
                        rfl

theorem cell23_537470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_537470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537470 prefixEnd_537470 := by exact prefixLift 537470
  have htrace : WordTrace (prefixWord ++ tailWord_537470) baseStart_537470 baseEnd_537470 := by
    simpa [prefixWord, tailWord_537470, baseEnd_537470] using wordTrace_append hprefix tailTrace_537470
  have hstable : (prefixWord ++ tailWord_537470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537470).length < 2 ^ (prefixWord ++ tailWord_537470).sum := by decide
  have hdescent : baseEnd_537470 < baseStart_537470 := by decide
  rcases family_descends (prefixWord ++ tailWord_537470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537489 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 3, 4, 2]
def baseStart_537489 : Nat := 118140960795 + 537489 * 2 ^ 59
def prefixEnd_537489 : Nat := 4983230072969 + 3 ^ 40 * 537489 * 2
def baseEnd_537489 : Nat := 275990203504552805515639

theorem tailTrace_537489 : CollatzResearch.WordTrace tailWord_537489 prefixEnd_537489 275990203504552805515639 := by
  unfold tailWord_537489
  simp only [CollatzResearch.WordTrace]
  refine ⟨19603834349776623658071521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13069222899851082438714347 19603834349776623658071521)
  ·
    refine ⟨14702875762332467743553641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19603834349776623658071521 14702875762332467743553641)
    ·
      refine ⟨11027156821749350807665231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14702875762332467743553641 11027156821749350807665231)
      ·
        refine ⟨16540735232624026211497847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11027156821749350807665231 16540735232624026211497847)
        ·
          refine ⟨24811102848936039317246771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16540735232624026211497847 24811102848936039317246771)
          ·
            refine ⟨37216654273404058975870157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24811102848936039317246771 37216654273404058975870157)
            ·
              refine ⟨13956245352526522115951309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37216654273404058975870157 13956245352526522115951309)
              ·
                refine ⟨5233592007197445793481741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13956245352526522115951309 5233592007197445793481741)
                ·
                  refine ⟨1962597002699042172555653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5233592007197445793481741 1962597002699042172555653)
                  ·
                    refine ⟨367986938006070407354185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962597002699042172555653 367986938006070407354185)
                    ·
                      refine ⟨275990203504552805515639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 367986938006070407354185 275990203504552805515639)
                      ·
                        rfl

theorem cell23_537489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_537489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537489 prefixEnd_537489 := by exact prefixLift 537489
  have htrace : WordTrace (prefixWord ++ tailWord_537489) baseStart_537489 baseEnd_537489 := by
    simpa [prefixWord, tailWord_537489, baseEnd_537489] using wordTrace_append hprefix tailTrace_537489
  have hstable : (prefixWord ++ tailWord_537489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537489).length < 2 ^ (prefixWord ++ tailWord_537489).sum := by decide
  have hdescent : baseEnd_537489 < baseStart_537489 := by decide
  rcases family_descends (prefixWord ++ tailWord_537489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537540 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_537540 : Nat := 118140960795 + 537540 * 2 ^ 59
def prefixEnd_537540 : Nat := 4983230072969 + 3 ^ 40 * 537540 * 2
def baseEnd_537540 : Nat := 276016391017932105977905

theorem tailTrace_537540 : CollatzResearch.WordTrace tailWord_537540 prefixEnd_537540 276016391017932105977905 := by
  unfold tailWord_537540
  simp only [CollatzResearch.WordTrace]
  refine ⟨9802847236295929684089037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13070462981727906245452049 9802847236295929684089037)
  ·
    refine ⟨3676067713610973631533389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9802847236295929684089037 3676067713610973631533389)
    ·
      refine ⟨1378525392604115111825021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3676067713610973631533389 1378525392604115111825021)
      ·
        refine ⟨516947022226543166934383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1378525392604115111825021 516947022226543166934383)
        ·
          refine ⟨775420533339814750401575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516947022226543166934383 775420533339814750401575)
          ·
            refine ⟨1163130800009722125602363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775420533339814750401575 1163130800009722125602363)
            ·
              refine ⟨1744696200014583188403545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163130800009722125602363 1744696200014583188403545)
              ·
                refine ⟨1308522150010937391302659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744696200014583188403545 1308522150010937391302659)
                ·
                  refine ⟨1962783225016406086953989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308522150010937391302659 1962783225016406086953989)
                  ·
                    refine ⟨368021854690576141303873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962783225016406086953989 368021854690576141303873)
                    ·
                      refine ⟨276016391017932105977905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368021854690576141303873 276016391017932105977905)
                      ·
                        rfl

theorem cell23_537540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_537540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537540 prefixEnd_537540 := by exact prefixLift 537540
  have htrace : WordTrace (prefixWord ++ tailWord_537540) baseStart_537540 baseEnd_537540 := by
    simpa [prefixWord, tailWord_537540, baseEnd_537540] using wordTrace_append hprefix tailTrace_537540
  have hstable : (prefixWord ++ tailWord_537540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537540).length < 2 ^ (prefixWord ++ tailWord_537540).sum := by decide
  have hdescent : baseEnd_537540 < baseStart_537540 := by decide
  rcases family_descends (prefixWord ++ tailWord_537540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537573 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 2, 3, 3]
def baseStart_537573 : Nat := 118140960795 + 537573 * 2 ^ 59
def prefixEnd_537573 : Nat := 4983230072969 + 3 ^ 40 * 537573 * 2
def baseEnd_537573 : Nat := 276033335879530476865253

theorem tailTrace_537573 : CollatzResearch.WordTrace tailWord_537573 prefixEnd_537573 276033335879530476865253 := by
  unfold tailWord_537573
  simp only [CollatzResearch.WordTrace]
  refine ⟨19606898081472306004129373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13071265387648204002752915 19606898081472306004129373)
  ·
    refine ⟨7352586780552114751548515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19606898081472306004129373 7352586780552114751548515)
    ·
      refine ⟨11028880170828172127322773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7352586780552114751548515 11028880170828172127322773)
      ·
        refine ⟨516978758007570568468255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11028880170828172127322773 516978758007570568468255)
        ·
          refine ⟨775468137011355852702383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516978758007570568468255 775468137011355852702383)
          ·
            refine ⟨1163202205517033779053575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775468137011355852702383 1163202205517033779053575)
            ·
              refine ⟨1744803308275550668580363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163202205517033779053575 1744803308275550668580363)
              ·
                refine ⟨2617204962413326002870545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744803308275550668580363 2617204962413326002870545)
                ·
                  refine ⟨1962903721809994502152909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2617204962413326002870545 1962903721809994502152909)
                  ·
                    refine ⟨736088895678747938307341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1962903721809994502152909 736088895678747938307341)
                    ·
                      refine ⟨276033335879530476865253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 736088895678747938307341 276033335879530476865253)
                      ·
                        rfl

theorem cell23_537573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_537573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537573 prefixEnd_537573 := by exact prefixLift 537573
  have htrace : WordTrace (prefixWord ++ tailWord_537573) baseStart_537573 baseEnd_537573 := by
    simpa [prefixWord, tailWord_537573, baseEnd_537573] using wordTrace_append hprefix tailTrace_537573
  have hstable : (prefixWord ++ tailWord_537573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537573).length < 2 ^ (prefixWord ++ tailWord_537573).sum := by decide
  have hdescent : baseEnd_537573 < baseStart_537573 := by decide
  rcases family_descends (prefixWord ++ tailWord_537573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537596 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_537596 : Nat := 118140960795 + 537596 * 2 ^ 59
def prefixEnd_537596 : Nat := 4983230072969 + 3 ^ 40 * 537596 * 2
def baseEnd_537596 : Nat := 276045145934583886877647

theorem tailTrace_537596 : CollatzResearch.WordTrace tailWord_537596 prefixEnd_537596 276045145934583886877647 := by
  unfold tailWord_537596
  simp only [CollatzResearch.WordTrace]
  refine ⟨9803868480194490466108321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13071824640259320621477761 9803868480194490466108321)
  ·
    refine ⟨7352901360145867849581241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9803868480194490466108321 7352901360145867849581241)
    ·
      refine ⟨5514676020109400887185931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7352901360145867849581241 5514676020109400887185931)
      ·
        refine ⟨8272014030164101330778897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5514676020109400887185931 8272014030164101330778897)
        ·
          refine ⟨6204010522623075998084173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8272014030164101330778897 6204010522623075998084173)
          ·
            refine ⟨2326503945983653499281565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6204010522623075998084173 2326503945983653499281565)
            ·
              refine ⟨872438979743870062230587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2326503945983653499281565 872438979743870062230587)
              ·
                refine ⟨1308658469615805093345881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872438979743870062230587 1308658469615805093345881)
                ·
                  refine ⟨981493852211853820009411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1308658469615805093345881 981493852211853820009411)
                  ·
                    refine ⟨1472240778317780730014117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 981493852211853820009411 1472240778317780730014117)
                    ·
                      refine ⟨276045145934583886877647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1472240778317780730014117 276045145934583886877647)
                      ·
                        rfl

theorem cell23_537596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_537596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537596 prefixEnd_537596 := by exact prefixLift 537596
  have htrace : WordTrace (prefixWord ++ tailWord_537596) baseStart_537596 baseEnd_537596 := by
    simpa [prefixWord, tailWord_537596, baseEnd_537596] using wordTrace_append hprefix tailTrace_537596
  have hstable : (prefixWord ++ tailWord_537596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537596).length < 2 ^ (prefixWord ++ tailWord_537596).sum := by decide
  have hdescent : baseEnd_537596 < baseStart_537596 := by decide
  rcases family_descends (prefixWord ++ tailWord_537596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537623 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 3, 4]
def baseStart_537623 : Nat := 118140960795 + 537623 * 2 ^ 59
def prefixEnd_537623 : Nat := 4983230072969 + 3 ^ 40 * 537623 * 2
def baseEnd_537623 : Nat := 92019669970751760413341

theorem tailTrace_537623 : CollatzResearch.WordTrace tailWord_537623 prefixEnd_537623 92019669970751760413341 := by
  unfold tailWord_537623
  simp only [CollatzResearch.WordTrace]
  refine ⟨19608721731291164543449523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13072481154194109695633015 19608721731291164543449523)
  ·
    refine ⟨29413082596936746815174285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19608721731291164543449523 29413082596936746815174285)
    ·
      refine ⟨11029905973851280055690357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29413082596936746815174285 11029905973851280055690357)
      ·
        refine ⟨1034053685048557505220971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11029905973851280055690357 1034053685048557505220971)
        ·
          refine ⟨1551080527572836257831457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034053685048557505220971 1551080527572836257831457)
          ·
            refine ⟨1163310395679627193373593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1551080527572836257831457 1163310395679627193373593)
            ·
              refine ⟨872482796759720395030195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163310395679627193373593 872482796759720395030195)
              ·
                refine ⟨1308724195139580592545293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872482796759720395030195 1308724195139580592545293)
                ·
                  refine ⟨490771573177342722204485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1308724195139580592545293 490771573177342722204485)
                  ·
                    refine ⟨92019669970751760413341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 490771573177342722204485 92019669970751760413341)
                    ·
                      rfl

theorem cell23_537623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_537623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537623 prefixEnd_537623 := by exact prefixLift 537623
  have htrace : WordTrace (prefixWord ++ tailWord_537623) baseStart_537623 baseEnd_537623 := by
    simpa [prefixWord, tailWord_537623, baseEnd_537623] using wordTrace_append hprefix tailTrace_537623
  have hstable : (prefixWord ++ tailWord_537623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537623).length < 2 ^ (prefixWord ++ tailWord_537623).sum := by decide
  have hdescent : baseEnd_537623 < baseStart_537623 := by decide
  rcases family_descends (prefixWord ++ tailWord_537623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537646 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_537646 : Nat := 118140960795 + 537646 * 2 ^ 59
def prefixEnd_537646 : Nat := 4983230072969 + 3 ^ 40 * 537646 * 2
def baseEnd_537646 : Nat := 276070819967308691252417

theorem tailTrace_537646 : CollatzResearch.WordTrace tailWord_537646 prefixEnd_537646 276070819967308691252417 := by
  unfold tailWord_537646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451195076275979933942099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13073040406805226314357861 2451195076275979933942099)
  ·
    refine ⟨3676792614413969900913149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2451195076275979933942099 3676792614413969900913149)
    ·
      refine ⟨1378797230405238712842431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3676792614413969900913149 1378797230405238712842431)
      ·
        refine ⟨2068195845607858069263647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378797230405238712842431 2068195845607858069263647)
        ·
          refine ⟨3102293768411787103895471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068195845607858069263647 3102293768411787103895471)
          ·
            refine ⟨4653440652617680655843207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102293768411787103895471 4653440652617680655843207)
            ·
              refine ⟨6980160978926520983764811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4653440652617680655843207 6980160978926520983764811)
              ·
                refine ⟨10470241468389781475647217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6980160978926520983764811 10470241468389781475647217)
                ·
                  refine ⟨7852681101292336106735413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10470241468389781475647217 7852681101292336106735413)
                  ·
                    refine ⟨736188853246156510006445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7852681101292336106735413 736188853246156510006445)
                    ·
                      refine ⟨276070819967308691252417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 736188853246156510006445 276070819967308691252417)
                      ·
                        rfl

theorem cell23_537646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_537646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537646 prefixEnd_537646 := by exact prefixLift 537646
  have htrace : WordTrace (prefixWord ++ tailWord_537646) baseStart_537646 baseEnd_537646 := by
    simpa [prefixWord, tailWord_537646, baseEnd_537646] using wordTrace_append hprefix tailTrace_537646
  have hstable : (prefixWord ++ tailWord_537646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537646).length < 2 ^ (prefixWord ++ tailWord_537646).sum := by decide
  have hdescent : baseEnd_537646 < baseStart_537646 := by decide
  rcases family_descends (prefixWord ++ tailWord_537646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537689 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_537689 : Nat := 118140960795 + 537689 * 2 ^ 59
def prefixEnd_537689 : Nat := 4983230072969 + 3 ^ 40 * 537689 * 2
def baseEnd_537689 : Nat := 276092899635452023014719

theorem tailTrace_537689 : CollatzResearch.WordTrace tailWord_537689 prefixEnd_537689 276092899635452023014719 := by
  unfold tailWord_537689
  simp only [CollatzResearch.WordTrace]
  refine ⟨19611128949052057815352121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13074085966034705210234747 19611128949052057815352121)
  ·
    refine ⟨14708346711789043361514091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19611128949052057815352121 14708346711789043361514091)
    ·
      refine ⟨22062520067683565042271137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14708346711789043361514091 22062520067683565042271137)
      ·
        refine ⟨16546890050762673781703353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22062520067683565042271137 16546890050762673781703353)
        ·
          refine ⟨12410167538072005336277515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16546890050762673781703353 12410167538072005336277515)
          ·
            refine ⟨18615251307108008004416273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12410167538072005336277515 18615251307108008004416273)
            ·
              refine ⟨13961438480331006003312205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18615251307108008004416273 13961438480331006003312205)
              ·
                refine ⟨5235539430124127251242077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13961438480331006003312205 5235539430124127251242077)
                ·
                  refine ⟨1963327286296547719215779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5235539430124127251242077 1963327286296547719215779)
                  ·
                    refine ⟨2944990929444821578823669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1963327286296547719215779 2944990929444821578823669)
                    ·
                      refine ⟨276092899635452023014719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2944990929444821578823669 276092899635452023014719)
                      ·
                        rfl

theorem cell23_537689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_537689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537689 prefixEnd_537689 := by exact prefixLift 537689
  have htrace : WordTrace (prefixWord ++ tailWord_537689) baseStart_537689 baseEnd_537689 := by
    simpa [prefixWord, tailWord_537689, baseEnd_537689] using wordTrace_append hprefix tailTrace_537689
  have hstable : (prefixWord ++ tailWord_537689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537689).length < 2 ^ (prefixWord ++ tailWord_537689).sum := by decide
  have hdescent : baseEnd_537689 < baseStart_537689 := by decide
  rcases family_descends (prefixWord ++ tailWord_537689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537703 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_537703 : Nat := 118140960795 + 537703 * 2 ^ 59
def prefixEnd_537703 : Nat := 4983230072969 + 3 ^ 40 * 537703 * 2
def baseEnd_537703 : Nat := 276100088364614968239655

theorem tailTrace_537703 : CollatzResearch.WordTrace tailWord_537703 prefixEnd_537703 276100088364614968239655 := by
  unfold tailWord_537703
  simp only [CollatzResearch.WordTrace]
  refine ⟨19611639571001338206361763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13074426380667558804241175 19611639571001338206361763)
  ·
    refine ⟨29417459356502007309542645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19611639571001338206361763 29417459356502007309542645)
    ·
      refine ⟨2757886814672063185269623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29417459356502007309542645 2757886814672063185269623)
      ·
        refine ⟨4136830222008094777904435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2757886814672063185269623 4136830222008094777904435)
        ·
          refine ⟨6205245333012142166856653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4136830222008094777904435 6205245333012142166856653)
          ·
            refine ⟨2326966999879553312571245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6205245333012142166856653 2326966999879553312571245)
            ·
              refine ⟨872612624954832492214217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2326966999879553312571245 872612624954832492214217)
              ·
                refine ⟨654459468716124369160663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872612624954832492214217 654459468716124369160663)
                ·
                  refine ⟨981689203074186553740995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654459468716124369160663 981689203074186553740995)
                  ·
                    refine ⟨1472533804611279830611493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 981689203074186553740995 1472533804611279830611493)
                    ·
                      refine ⟨276100088364614968239655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1472533804611279830611493 276100088364614968239655)
                      ·
                        rfl

theorem cell23_537703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_537703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537703 prefixEnd_537703 := by exact prefixLift 537703
  have htrace : WordTrace (prefixWord ++ tailWord_537703) baseStart_537703 baseEnd_537703 := by
    simpa [prefixWord, tailWord_537703, baseEnd_537703] using wordTrace_append hprefix tailTrace_537703
  have hstable : (prefixWord ++ tailWord_537703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537703).length < 2 ^ (prefixWord ++ tailWord_537703).sum := by decide
  have hdescent : baseEnd_537703 < baseStart_537703 := by decide
  rcases family_descends (prefixWord ++ tailWord_537703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537717 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_537717 : Nat := 118140960795 + 537717 * 2 ^ 59
def prefixEnd_537717 : Nat := 4983230072969 + 3 ^ 40 * 537717 * 2
def baseEnd_537717 : Nat := 92035759031259304488197

theorem tailTrace_537717 : CollatzResearch.WordTrace tailWord_537717 prefixEnd_537717 92035759031259304488197 := by
  unfold tailWord_537717
  simp only [CollatzResearch.WordTrace]
  refine ⟨19612150192950618597371405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13074766795300412398247603 19612150192950618597371405)
  ·
    refine ⟨7354556322356481974014277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19612150192950618597371405 7354556322356481974014277)
    ·
      refine ⟨1378979310441840370127677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7354556322356481974014277 1378979310441840370127677)
      ·
        refine ⟨517117241415690138797879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1378979310441840370127677 517117241415690138797879)
        ·
          refine ⟨775675862123535208196819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517117241415690138797879 775675862123535208196819)
          ·
            refine ⟨1163513793185302812295229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775675862123535208196819 1163513793185302812295229)
            ·
              refine ⟨436317672444488554610711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1163513793185302812295229 436317672444488554610711)
              ·
                refine ⟨654476508666732831916067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436317672444488554610711 654476508666732831916067)
                ·
                  refine ⟨981714763000099247874101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654476508666732831916067 981714763000099247874101)
                  ·
                    refine ⟨92035759031259304488197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 981714763000099247874101 92035759031259304488197)
                    ·
                      rfl

theorem cell23_537717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_537717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537717 prefixEnd_537717 := by exact prefixLift 537717
  have htrace : WordTrace (prefixWord ++ tailWord_537717) baseStart_537717 baseEnd_537717 := by
    simpa [prefixWord, tailWord_537717, baseEnd_537717] using wordTrace_append hprefix tailTrace_537717
  have hstable : (prefixWord ++ tailWord_537717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537717).length < 2 ^ (prefixWord ++ tailWord_537717).sum := by decide
  have hdescent : baseEnd_537717 < baseStart_537717 := by decide
  rcases family_descends (prefixWord ++ tailWord_537717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537737 : List Nat := [1, 2, 1, 1, 4, 4, 1, 4, 1, 2, 2]
def baseStart_537737 : Nat := 118140960795 + 537737 * 2 ^ 59
def prefixEnd_537737 : Nat := 4983230072969 + 3 ^ 40 * 537737 * 2
def baseEnd_537737 : Nat := 276117546706867835214499

theorem tailTrace_537737 : CollatzResearch.WordTrace tailWord_537737 prefixEnd_537737 276117546706867835214499 := by
  unfold tailWord_537737
  simp only [CollatzResearch.WordTrace]
  refine ⟨19612879652878162013099465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13075253101918774675399643 19612879652878162013099465)
  ·
    refine ⟨14709659739658621509824599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19612879652878162013099465 14709659739658621509824599)
    ·
      refine ⟨22064489609487932264736899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14709659739658621509824599 22064489609487932264736899)
      ·
        refine ⟨33096734414231898397105349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22064489609487932264736899 33096734414231898397105349)
        ·
          refine ⟨6205637702668480949457253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33096734414231898397105349 6205637702668480949457253)
          ·
            refine ⟨1163557069250340178023235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6205637702668480949457253 1163557069250340178023235)
            ·
              refine ⟨1745335603875510267034853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163557069250340178023235 1745335603875510267034853)
              ·
                refine ⟨327250425726658175069035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1745335603875510267034853 327250425726658175069035)
                ·
                  refine ⟨490875638589987262603553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327250425726658175069035 490875638589987262603553)
                  ·
                    refine ⟨368156728942490446952665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 490875638589987262603553 368156728942490446952665)
                    ·
                      refine ⟨276117546706867835214499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368156728942490446952665 276117546706867835214499)
                      ·
                        rfl

theorem cell23_537737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 1, 2, 2].length) (baseStart_537737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537737 prefixEnd_537737 := by exact prefixLift 537737
  have htrace : WordTrace (prefixWord ++ tailWord_537737) baseStart_537737 baseEnd_537737 := by
    simpa [prefixWord, tailWord_537737, baseEnd_537737] using wordTrace_append hprefix tailTrace_537737
  have hstable : (prefixWord ++ tailWord_537737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537737).length < 2 ^ (prefixWord ++ tailWord_537737).sum := by decide
  have hdescent : baseEnd_537737 < baseStart_537737 := by decide
  rcases family_descends (prefixWord ++ tailWord_537737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537770 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_537770 : Nat := 118140960795 + 537770 * 2 ^ 59
def prefixEnd_537770 : Nat := 4983230072969 + 3 ^ 40 * 537770 * 2
def baseEnd_537770 : Nat := 276134491568466206101847

theorem tailTrace_537770 : CollatzResearch.WordTrace tailWord_537770 prefixEnd_537770 276134491568466206101847 := by
  unfold tailWord_537770
  simp only [CollatzResearch.WordTrace]
  refine ⟨4903520815439652162262691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13076055507839072432700509 4903520815439652162262691)
  ·
    refine ⟨7355281223159478243394037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4903520815439652162262691 7355281223159478243394037)
    ·
      refine ⟨689557614671201085318191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7355281223159478243394037 689557614671201085318191)
      ·
        refine ⟨1034336422006801627977287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689557614671201085318191 1034336422006801627977287)
        ·
          refine ⟨1551504633010202441965931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034336422006801627977287 1551504633010202441965931)
          ·
            refine ⟨2327256949515303662948897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551504633010202441965931 2327256949515303662948897)
            ·
              refine ⟨1745442712136477747211673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2327256949515303662948897 1745442712136477747211673)
              ·
                refine ⟨1309082034102358310408755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1745442712136477747211673 1309082034102358310408755)
                ·
                  refine ⟨1963623051153537465613133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309082034102358310408755 1963623051153537465613133)
                  ·
                    refine ⟨736358644182576549604925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1963623051153537465613133 736358644182576549604925)
                    ·
                      refine ⟨276134491568466206101847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 736358644182576549604925 276134491568466206101847)
                      ·
                        rfl

theorem cell23_537770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_537770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537770 prefixEnd_537770 := by exact prefixLift 537770
  have htrace : WordTrace (prefixWord ++ tailWord_537770) baseStart_537770 baseEnd_537770 := by
    simpa [prefixWord, tailWord_537770, baseEnd_537770] using wordTrace_append hprefix tailTrace_537770
  have hstable : (prefixWord ++ tailWord_537770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537770).length < 2 ^ (prefixWord ++ tailWord_537770).sum := by decide
  have hdescent : baseEnd_537770 < baseStart_537770 := by decide
  rcases family_descends (prefixWord ++ tailWord_537770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537850 : List Nat := [3, 1, 1, 1, 1, 4, 5, 2, 5]
def baseStart_537850 : Nat := 118140960795 + 537850 * 2 ^ 59
def prefixEnd_537850 : Nat := 4983230072969 + 3 ^ 40 * 537850 * 2
def baseEnd_537850 : Nat := 30686174446758432566831

theorem tailTrace_537850 : CollatzResearch.WordTrace tailWord_537850 prefixEnd_537850 30686174446758432566831 := by
  unfold tailWord_537850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4904250275367195577990751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13078000734312521541308669 4904250275367195577990751)
  ·
    refine ⟨7356375413050793366986127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4904250275367195577990751 7356375413050793366986127)
    ·
      refine ⟨11034563119576190050479191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7356375413050793366986127 11034563119576190050479191)
      ·
        refine ⟨16551844679364285075718787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11034563119576190050479191 16551844679364285075718787)
        ·
          refine ⟨24827767019046427613578181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16551844679364285075718787 24827767019046427613578181)
          ·
            refine ⟨4655206316071205177545909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24827767019046427613578181 4655206316071205177545909)
            ·
              refine ⟨436425592131675485394929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4655206316071205177545909 436425592131675485394929)
              ·
                refine ⟨327319194098756614046197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436425592131675485394929 327319194098756614046197)
                ·
                  refine ⟨30686174446758432566831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 327319194098756614046197 30686174446758432566831)
                  ·
                    rfl

theorem cell23_537850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_537850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537850 prefixEnd_537850 := by exact prefixLift 537850
  have htrace : WordTrace (prefixWord ++ tailWord_537850) baseStart_537850 baseEnd_537850 := by
    simpa [prefixWord, tailWord_537850, baseEnd_537850] using wordTrace_append hprefix tailTrace_537850
  have hstable : (prefixWord ++ tailWord_537850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537850).length < 2 ^ (prefixWord ++ tailWord_537850).sum := by decide
  have hdescent : baseEnd_537850 < baseStart_537850 := by decide
  rcases family_descends (prefixWord ++ tailWord_537850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537883 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 4, 4, 2]
def baseStart_537883 : Nat := 118140960795 + 537883 * 2 ^ 59
def prefixEnd_537883 : Nat := 4983230072969 + 3 ^ 40 * 537883 * 2
def baseEnd_537883 : Nat := 276192514882424263988827

theorem tailTrace_537883 : CollatzResearch.WordTrace tailWord_537883 prefixEnd_537883 276192514882424263988827 := by
  unfold tailWord_537883
  simp only [CollatzResearch.WordTrace]
  refine ⟨19618204710349228947914303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13078803140232819298609535 19618204710349228947914303)
  ·
    refine ⟨29427307065523843421871455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19618204710349228947914303 29427307065523843421871455)
    ·
      refine ⟨44140960598285765132807183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29427307065523843421871455 44140960598285765132807183)
      ·
        refine ⟨66211440897428647699210775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44140960598285765132807183 66211440897428647699210775)
        ·
          refine ⟨99317161346142971548816163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66211440897428647699210775 99317161346142971548816163)
          ·
            refine ⟨148975742019214457323224245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99317161346142971548816163 148975742019214457323224245)
            ·
              refine ⟨13966475814301355374052273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148975742019214457323224245 13966475814301355374052273)
              ·
                refine ⟨10474856860726016530539205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13966475814301355374052273 10474856860726016530539205)
                ·
                  refine ⟨1964035661386128099476101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10474856860726016530539205 1964035661386128099476101)
                  ·
                    refine ⟨368256686509899018651769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964035661386128099476101 368256686509899018651769)
                    ·
                      refine ⟨276192514882424263988827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368256686509899018651769 276192514882424263988827)
                      ·
                        rfl

theorem cell23_537883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 4, 2].length) (baseStart_537883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537883 prefixEnd_537883 := by exact prefixLift 537883
  have htrace : WordTrace (prefixWord ++ tailWord_537883) baseStart_537883 baseEnd_537883 := by
    simpa [prefixWord, tailWord_537883, baseEnd_537883] using wordTrace_append hprefix tailTrace_537883
  have hstable : (prefixWord ++ tailWord_537883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537883).length < 2 ^ (prefixWord ++ tailWord_537883).sum := by decide
  have hdescent : baseEnd_537883 < baseStart_537883 := by decide
  rcases family_descends (prefixWord ++ tailWord_537883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537967 : List Nat := [1, 1, 2, 1, 3, 1, 3, 6, 1, 1, 3]
def baseStart_537967 : Nat := 118140960795 + 537967 * 2 ^ 59
def prefixEnd_537967 : Nat := 4983230072969 + 3 ^ 40 * 537967 * 2
def baseEnd_537967 : Nat := 276235647257401935338441

theorem tailTrace_537967 : CollatzResearch.WordTrace tailWord_537967 prefixEnd_537967 276235647257401935338441 := by
  unfold tailWord_537967
  simp only [CollatzResearch.WordTrace]
  refine ⟨19621268442044911293972155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13080845628029940862648103 19621268442044911293972155)
  ·
    refine ⟨29431902663067366940958233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19621268442044911293972155 29431902663067366940958233)
    ·
      refine ⟨22073926997300525205718675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29431902663067366940958233 22073926997300525205718675)
      ·
        refine ⟨33110890495950787808578013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22073926997300525205718675 33110890495950787808578013)
        ·
          refine ⟨12416583935981545428216755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33110890495950787808578013 12416583935981545428216755)
          ·
            refine ⟨18624875903972318142325133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12416583935981545428216755 18624875903972318142325133)
            ·
              refine ⟨6984328463989619303371925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18624875903972318142325133 6984328463989619303371925)
              ·
                refine ⟨327390396749513404845559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6984328463989619303371925 327390396749513404845559)
                ·
                  refine ⟨491085595124270107268339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327390396749513404845559 491085595124270107268339)
                  ·
                    refine ⟨736628392686405160902509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 491085595124270107268339 736628392686405160902509)
                    ·
                      refine ⟨276235647257401935338441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 736628392686405160902509 276235647257401935338441)
                      ·
                        rfl

theorem cell23_537967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 1, 1, 3].length) (baseStart_537967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537967 prefixEnd_537967 := by exact prefixLift 537967
  have htrace : WordTrace (prefixWord ++ tailWord_537967) baseStart_537967 baseEnd_537967 := by
    simpa [prefixWord, tailWord_537967, baseEnd_537967] using wordTrace_append hprefix tailTrace_537967
  have hstable : (prefixWord ++ tailWord_537967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537967).length < 2 ^ (prefixWord ++ tailWord_537967).sum := by decide
  have hdescent : baseEnd_537967 < baseStart_537967 := by decide
  rcases family_descends (prefixWord ++ tailWord_537967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537983 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 8, 4]
def baseStart_537983 : Nat := 118140960795 + 537983 * 2 ^ 59
def prefixEnd_537983 : Nat := 4983230072969 + 3 ^ 40 * 537983 * 2
def baseEnd_537983 : Nat := 92081287649291290912789

theorem tailTrace_537983 : CollatzResearch.WordTrace tailWord_537983 prefixEnd_537983 92081287649291290912789 := by
  unfold tailWord_537983
  simp only [CollatzResearch.WordTrace]
  refine ⟨19621852009986946026554603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13081234673324630684369735 19621852009986946026554603)
  ·
    refine ⟨29432778014980419039831905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19621852009986946026554603 29432778014980419039831905)
    ·
      refine ⟨22074583511235314279873929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29432778014980419039831905 22074583511235314279873929)
      ·
        refine ⟨16555937633426485709905447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22074583511235314279873929 16555937633426485709905447)
        ·
          refine ⟨24833906450139728564858171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16555937633426485709905447 24833906450139728564858171)
          ·
            refine ⟨37250859675209592847287257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24833906450139728564858171 37250859675209592847287257)
            ·
              refine ⟨27938144756407194635465443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37250859675209592847287257 27938144756407194635465443)
              ·
                refine ⟨41907217134610791953198165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27938144756407194635465443 41907217134610791953198165)
                ·
                  refine ⟨491100200796220218201541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 41907217134610791953198165 491100200796220218201541)
                  ·
                    refine ⟨92081287649291290912789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 491100200796220218201541 92081287649291290912789)
                    ·
                      rfl

theorem cell23_537983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 4].length) (baseStart_537983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_537983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_537983 prefixEnd_537983 := by exact prefixLift 537983
  have htrace : WordTrace (prefixWord ++ tailWord_537983) baseStart_537983 baseEnd_537983 := by
    simpa [prefixWord, tailWord_537983, baseEnd_537983] using wordTrace_append hprefix tailTrace_537983
  have hstable : (prefixWord ++ tailWord_537983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537983).length < 2 ^ (prefixWord ++ tailWord_537983).sum := by decide
  have hdescent : baseEnd_537983 < baseStart_537983 := by decide
  rcases family_descends (prefixWord ++ tailWord_537983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538010 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5]
def baseStart_538010 : Nat := 118140960795 + 538010 * 2 ^ 59
def prefixEnd_538010 : Nat := 4983230072969 + 3 ^ 40 * 538010 * 2
def baseEnd_538010 : Nat := 276257726925545267100743

theorem tailTrace_538010 : CollatzResearch.WordTrace tailWord_538010 prefixEnd_538010 276257726925545267100743 := by
  unfold tailWord_538010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4905709195222282409446871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13081891187259419758524989 4905709195222282409446871)
  ·
    refine ⟨7358563792833423614170307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4905709195222282409446871 7358563792833423614170307)
    ·
      refine ⟨11037845689250135421255461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7358563792833423614170307 11037845689250135421255461)
      ·
        refine ⟨2069596066734400391485399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11037845689250135421255461 2069596066734400391485399)
        ·
          refine ⟨3104394100101600587228099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069596066734400391485399 3104394100101600587228099)
          ·
            refine ⟨4656591150152400880842149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104394100101600587228099 4656591150152400880842149)
            ·
              refine ⟨873110840653575165157903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4656591150152400880842149 873110840653575165157903)
              ·
                refine ⟨1309666260980362747736855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873110840653575165157903 1309666260980362747736855)
                ·
                  refine ⟨1964499391470544121605283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309666260980362747736855 1964499391470544121605283)
                  ·
                    refine ⟨2946749087205816182407925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1964499391470544121605283 2946749087205816182407925)
                    ·
                      refine ⟨276257726925545267100743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2946749087205816182407925 276257726925545267100743)
                      ·
                        rfl

theorem cell23_538010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_538010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538010 prefixEnd_538010 := by exact prefixLift 538010
  have htrace : WordTrace (prefixWord ++ tailWord_538010) baseStart_538010 baseEnd_538010 := by
    simpa [prefixWord, tailWord_538010, baseEnd_538010] using wordTrace_append hprefix tailTrace_538010
  have hstable : (prefixWord ++ tailWord_538010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538010).length < 2 ^ (prefixWord ++ tailWord_538010).sum := by decide
  have hdescent : baseEnd_538010 < baseStart_538010 := by decide
  rcases family_descends (prefixWord ++ tailWord_538010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538013 : List Nat := [1, 4, 2, 1, 3, 1, 11]
def baseStart_538013 : Nat := 118140960795 + 538013 * 2 ^ 59
def prefixEnd_538013 : Nat := 4983230072969 + 3 ^ 40 * 538013 * 2
def baseEnd_538013 : Nat := 3410608239105046362509

theorem tailTrace_538013 : CollatzResearch.WordTrace tailWord_538013 prefixEnd_538013 3410608239105046362509 := by
  unfold tailWord_538013
  simp only [CollatzResearch.WordTrace]
  refine ⟨19622946199878261150146693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13081964133252174100097795 19622946199878261150146693)
  ·
    refine ⟨3679302412477173965652505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19622946199878261150146693 3679302412477173965652505)
    ·
      refine ⟨2759476809357880474239379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3679302412477173965652505 2759476809357880474239379)
      ·
        refine ⟨4139215214036820711359069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2759476809357880474239379 4139215214036820711359069)
        ·
          refine ⟨1552205705263807766759651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4139215214036820711359069 1552205705263807766759651)
          ·
            refine ⟨2328308557895711650139477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552205705263807766759651 2328308557895711650139477)
            ·
              refine ⟨3410608239105046362509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2328308557895711650139477 3410608239105046362509)
              ·
                rfl

theorem cell23_538013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 11].length) (baseStart_538013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538013 prefixEnd_538013 := by exact prefixLift 538013
  have htrace : WordTrace (prefixWord ++ tailWord_538013) baseStart_538013 baseEnd_538013 := by
    simpa [prefixWord, tailWord_538013, baseEnd_538013] using wordTrace_append hprefix tailTrace_538013
  have hstable : (prefixWord ++ tailWord_538013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538013).length < 2 ^ (prefixWord ++ tailWord_538013).sum := by decide
  have hdescent : baseEnd_538013 < baseStart_538013 := by decide
  rcases family_descends (prefixWord ++ tailWord_538013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538033 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_538033 : Nat := 118140960795 + 538033 * 2 ^ 59
def prefixEnd_538033 : Nat := 4983230072969 + 3 ^ 40 * 538033 * 2
def baseEnd_538033 : Nat := 276269536980598677113137

theorem tailTrace_538033 : CollatzResearch.WordTrace tailWord_538033 prefixEnd_538033 276269536980598677113137 := by
  unfold tailWord_538033
  simp only [CollatzResearch.WordTrace]
  refine ⟨19623675659805804565874753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13082450439870536377249835 19623675659805804565874753)
  ·
    refine ⟨14717756744854353424406065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19623675659805804565874753 14717756744854353424406065)
    ·
      refine ⟨11038317558640765068304549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14717756744854353424406065 11038317558640765068304549)
      ·
        refine ⟨2069684542245143450307103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11038317558640765068304549 2069684542245143450307103)
        ·
          refine ⟨3104526813367715175460655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069684542245143450307103 3104526813367715175460655)
          ·
            refine ⟨4656790220051572763190983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104526813367715175460655 4656790220051572763190983)
            ·
              refine ⟨6985185330077359144786475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4656790220051572763190983 6985185330077359144786475)
              ·
                refine ⟨10477777995116038717179713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6985185330077359144786475 10477777995116038717179713)
                ·
                  refine ⟨7858333496337029037884785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10477777995116038717179713 7858333496337029037884785)
                  ·
                    refine ⟨5893750122252771778413589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7858333496337029037884785 5893750122252771778413589)
                    ·
                      refine ⟨276269536980598677113137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5893750122252771778413589 276269536980598677113137)
                      ·
                        rfl

theorem cell23_538033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_538033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538033 prefixEnd_538033 := by exact prefixLift 538033
  have htrace : WordTrace (prefixWord ++ tailWord_538033) baseStart_538033 baseEnd_538033 := by
    simpa [prefixWord, tailWord_538033, baseEnd_538033] using wordTrace_append hprefix tailTrace_538033
  have hstable : (prefixWord ++ tailWord_538033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538033).length < 2 ^ (prefixWord ++ tailWord_538033).sum := by decide
  have hdescent : baseEnd_538033 < baseStart_538033 := by decide
  rcases family_descends (prefixWord ++ tailWord_538033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538074 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3]
def baseStart_538074 : Nat := 118140960795 + 538074 * 2 ^ 59
def prefixEnd_538074 : Nat := 4983230072969 + 3 ^ 40 * 538074 * 2
def baseEnd_538074 : Nat := 276290589687433016700449

theorem tailTrace_538074 : CollatzResearch.WordTrace tailWord_538074 prefixEnd_538074 276290589687433016700449 := by
  unfold tailWord_538074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4906292763164317142029319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13083447368438179045411517 4906292763164317142029319)
  ·
    refine ⟨7359439144746475713043979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4906292763164317142029319 7359439144746475713043979)
    ·
      refine ⟨11039158717119713569565969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7359439144746475713043979 11039158717119713569565969)
      ·
        refine ⟨8279369037839785177174477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11039158717119713569565969 8279369037839785177174477)
        ·
          refine ⟨3104763389189919441440429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8279369037839785177174477 3104763389189919441440429)
          ·
            refine ⟨1164286270946219790540161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3104763389189919441440429 1164286270946219790540161)
            ·
              refine ⟨873214703209664842905121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1164286270946219790540161 873214703209664842905121)
              ·
                refine ⟨654911027407248632178841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873214703209664842905121 654911027407248632178841)
                ·
                  refine ⟨491183270555436474134131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 654911027407248632178841 491183270555436474134131)
                  ·
                    refine ⟨736774905833154711201197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 491183270555436474134131 736774905833154711201197)
                    ·
                      refine ⟨276290589687433016700449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 736774905833154711201197 276290589687433016700449)
                      ·
                        rfl

theorem cell23_538074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_538074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538074 prefixEnd_538074 := by exact prefixLift 538074
  have htrace : WordTrace (prefixWord ++ tailWord_538074) baseStart_538074 baseEnd_538074 := by
    simpa [prefixWord, tailWord_538074, baseEnd_538074] using wordTrace_append hprefix tailTrace_538074
  have hstable : (prefixWord ++ tailWord_538074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538074).length < 2 ^ (prefixWord ++ tailWord_538074).sum := by decide
  have hdescent : baseEnd_538074 < baseStart_538074 := by decide
  rcases family_descends (prefixWord ++ tailWord_538074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538097 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 1, 4, 2]
def baseStart_538097 : Nat := 118140960795 + 538097 * 2 ^ 59
def prefixEnd_538097 : Nat := 4983230072969 + 3 ^ 40 * 538097 * 2
def baseEnd_538097 : Nat := 276302399742486426712843

theorem tailTrace_538097 : CollatzResearch.WordTrace tailWord_538097 prefixEnd_538097 276302399742486426712843 := by
  unfold tailWord_538097
  simp only [CollatzResearch.WordTrace]
  refine ⟨19626009931573943496204545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13084006621049295664136363 19626009931573943496204545)
  ·
    refine ⟨14719507448680457622153409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19626009931573943496204545 14719507448680457622153409)
    ·
      refine ⟨11039630586510343216615057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14719507448680457622153409 11039630586510343216615057)
      ·
        refine ⟨8279722939882757412461293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11039630586510343216615057 8279722939882757412461293)
        ·
          refine ⟨3104896102456034029672985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8279722939882757412461293 3104896102456034029672985)
          ·
            refine ⟨2328672076842025522254739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3104896102456034029672985 2328672076842025522254739)
            ·
              refine ⟨3493008115263038283382109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328672076842025522254739 3493008115263038283382109)
              ·
                refine ⟨1309878043223639356268291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3493008115263038283382109 1309878043223639356268291)
                ·
                  refine ⟨1964817064835459034402437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309878043223639356268291 1964817064835459034402437)
                  ·
                    refine ⟨368403199656648568950457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964817064835459034402437 368403199656648568950457)
                    ·
                      refine ⟨276302399742486426712843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368403199656648568950457 276302399742486426712843)
                      ·
                        rfl

theorem cell23_538097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_538097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538097 prefixEnd_538097 := by exact prefixLift 538097
  have htrace : WordTrace (prefixWord ++ tailWord_538097) baseStart_538097 baseEnd_538097 := by
    simpa [prefixWord, tailWord_538097, baseEnd_538097] using wordTrace_append hprefix tailTrace_538097
  have hstable : (prefixWord ++ tailWord_538097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538097).length < 2 ^ (prefixWord ++ tailWord_538097).sum := by decide
  have hdescent : baseEnd_538097 < baseStart_538097 := by decide
  rcases family_descends (prefixWord ++ tailWord_538097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538125 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_538125 : Nat := 118140960795 + 538125 * 2 ^ 59
def prefixEnd_538125 : Nat := 4983230072969 + 3 ^ 40 * 538125 * 2
def baseEnd_538125 : Nat := 276316777200812317162715

theorem tailTrace_538125 : CollatzResearch.WordTrace tailWord_538125 prefixEnd_538125 276316777200812317162715 := by
  unfold tailWord_538125
  simp only [CollatzResearch.WordTrace]
  refine ⟨19627031175472504278223829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13084687450315002852149219 19627031175472504278223829)
  ·
    refine ⟨460008543175136819020871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19627031175472504278223829 460008543175136819020871)
    ·
      refine ⟨690012814762705228531307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 460008543175136819020871 690012814762705228531307)
      ·
        refine ⟨1035019222144057842796961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 690012814762705228531307 1035019222144057842796961)
        ·
          refine ⟨776264416608043382097721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1035019222144057842796961 776264416608043382097721)
          ·
            refine ⟨582198312456032536573291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776264416608043382097721 582198312456032536573291)
            ·
              refine ⟨873297468684048804859937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582198312456032536573291 873297468684048804859937)
              ·
                refine ⟨654973101513036603644953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873297468684048804859937 654973101513036603644953)
                ·
                  refine ⟨491229826134777452733715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 654973101513036603644953 491229826134777452733715)
                  ·
                    refine ⟨736844739202166179100573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 491229826134777452733715 736844739202166179100573)
                    ·
                      refine ⟨276316777200812317162715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 736844739202166179100573 276316777200812317162715)
                      ·
                        rfl

theorem cell23_538125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_538125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538125 prefixEnd_538125 := by exact prefixLift 538125
  have htrace : WordTrace (prefixWord ++ tailWord_538125) baseStart_538125 baseEnd_538125 := by
    simpa [prefixWord, tailWord_538125, baseEnd_538125] using wordTrace_append hprefix tailTrace_538125
  have hstable : (prefixWord ++ tailWord_538125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538125).length < 2 ^ (prefixWord ++ tailWord_538125).sum := by decide
  have hdescent : baseEnd_538125 < baseStart_538125 := by decide
  rcases family_descends (prefixWord ++ tailWord_538125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538131 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 2, 2, 2]
def baseStart_538131 : Nat := 118140960795 + 538131 * 2 ^ 59
def prefixEnd_538131 : Nat := 4983230072969 + 3 ^ 40 * 538131 * 2
def baseEnd_538131 : Nat := 276319858084739293687687

theorem tailTrace_538131 : CollatzResearch.WordTrace tailWord_538131 prefixEnd_538131 276319858084739293687687 := by
  unfold tailWord_538131
  simp only [CollatzResearch.WordTrace]
  refine ⟨19627250013450767302942247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13084833342300511535294831 19627250013450767302942247)
  ·
    refine ⟨29440875020176150954413371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19627250013450767302942247 29440875020176150954413371)
    ·
      refine ⟨44161312530264226431620057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29440875020176150954413371 44161312530264226431620057)
      ·
        refine ⟨33120984397698169823715043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44161312530264226431620057 33120984397698169823715043)
        ·
          refine ⟨49681476596547254735572565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33120984397698169823715043 49681476596547254735572565)
          ·
            refine ⟨582204803865788141432491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 49681476596547254735572565 582204803865788141432491)
            ·
              refine ⟨873307205798682212148737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582204803865788141432491 873307205798682212148737)
              ·
                refine ⟨654980404349011659111553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873307205798682212148737 654980404349011659111553)
                ·
                  refine ⟨491235303261758744333665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 654980404349011659111553 491235303261758744333665)
                  ·
                    refine ⟨368426477446319058250249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 491235303261758744333665 368426477446319058250249)
                    ·
                      refine ⟨276319858084739293687687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368426477446319058250249 276319858084739293687687)
                      ·
                        rfl

theorem cell23_538131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 2, 2].length) (baseStart_538131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538131 prefixEnd_538131 := by exact prefixLift 538131
  have htrace : WordTrace (prefixWord ++ tailWord_538131) baseStart_538131 baseEnd_538131 := by
    simpa [prefixWord, tailWord_538131, baseEnd_538131] using wordTrace_append hprefix tailTrace_538131
  have hstable : (prefixWord ++ tailWord_538131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538131).length < 2 ^ (prefixWord ++ tailWord_538131).sum := by decide
  have hdescent : baseEnd_538131 < baseStart_538131 := by decide
  rcases family_descends (prefixWord ++ tailWord_538131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538142 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_538142 : Nat := 118140960795 + 538142 * 2 ^ 59
def prefixEnd_538142 : Nat := 4983230072969 + 3 ^ 40 * 538142 * 2
def baseEnd_538142 : Nat := 276325506371938750650137

theorem tailTrace_538142 : CollatzResearch.WordTrace tailWord_538142 prefixEnd_538142 276325506371938750650137 := by
  unfold tailWord_538142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2453456402051364522699085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13085100810940610787728453 2453456402051364522699085)
  ·
    refine ⟨920046150769261696012157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2453456402051364522699085 920046150769261696012157)
    ·
      refine ⟨345017306538473136004559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 920046150769261696012157 345017306538473136004559)
      ·
        refine ⟨517525959807709704006839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345017306538473136004559 517525959807709704006839)
        ·
          refine ⟨776288939711564556010259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517525959807709704006839 776288939711564556010259)
          ·
            refine ⟨1164433409567346834015389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776288939711564556010259 1164433409567346834015389)
            ·
              refine ⟨436662528587755062755771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1164433409567346834015389 436662528587755062755771)
              ·
                refine ⟨654993792881632594133657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436662528587755062755771 654993792881632594133657)
                ·
                  refine ⟨491245344661224445600243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 654993792881632594133657 491245344661224445600243)
                  ·
                    refine ⟨736868016991836668400365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 491245344661224445600243 736868016991836668400365)
                    ·
                      refine ⟨276325506371938750650137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 736868016991836668400365 276325506371938750650137)
                      ·
                        rfl

theorem cell23_538142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_538142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538142 prefixEnd_538142 := by exact prefixLift 538142
  have htrace : WordTrace (prefixWord ++ tailWord_538142) baseStart_538142 baseEnd_538142 := by
    simpa [prefixWord, tailWord_538142, baseEnd_538142] using wordTrace_append hprefix tailTrace_538142
  have hstable : (prefixWord ++ tailWord_538142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538142).length < 2 ^ (prefixWord ++ tailWord_538142).sum := by decide
  have hdescent : baseEnd_538142 < baseStart_538142 := by decide
  rcases family_descends (prefixWord ++ tailWord_538142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538170 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_538170 : Nat := 118140960795 + 538170 * 2 ^ 59
def prefixEnd_538170 : Nat := 4983230072969 + 3 ^ 40 * 538170 * 2
def baseEnd_538170 : Nat := 276339883830264641100007

theorem tailTrace_538170 : CollatzResearch.WordTrace tailWord_538170 prefixEnd_538170 276339883830264641100007 := by
  unfold tailWord_538170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4907168115077369240902991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13085781640206317975741309 4907168115077369240902991)
  ·
    refine ⟨7360752172616053861354487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4907168115077369240902991 7360752172616053861354487)
    ·
      refine ⟨11041128258924080792031731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7360752172616053861354487 11041128258924080792031731)
      ·
        refine ⟨16561692388386121188047597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11041128258924080792031731 16561692388386121188047597)
        ·
          refine ⟨6210634645644795445517849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16561692388386121188047597 6210634645644795445517849)
          ·
            refine ⟨4657975984233596584138387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6210634645644795445517849 4657975984233596584138387)
            ·
              refine ⟨6986963976350394876207581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4657975984233596584138387 6986963976350394876207581)
              ·
                refine ⟨2620111491131398078577843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6986963976350394876207581 2620111491131398078577843)
                ·
                  refine ⟨3930167236697097117866765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2620111491131398078577843 3930167236697097117866765)
                  ·
                    refine ⟨1473812713761411419200037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3930167236697097117866765 1473812713761411419200037)
                    ·
                      refine ⟨276339883830264641100007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1473812713761411419200037 276339883830264641100007)
                      ·
                        rfl

theorem cell23_538170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_538170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538170 prefixEnd_538170 := by exact prefixLift 538170
  have htrace : WordTrace (prefixWord ++ tailWord_538170) baseStart_538170 baseEnd_538170 := by
    simpa [prefixWord, tailWord_538170, baseEnd_538170] using wordTrace_append hprefix tailTrace_538170
  have hstable : (prefixWord ++ tailWord_538170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538170).length < 2 ^ (prefixWord ++ tailWord_538170).sum := by decide
  have hdescent : baseEnd_538170 < baseStart_538170 := by decide
  rcases family_descends (prefixWord ++ tailWord_538170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538224 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 3]
def baseStart_538224 : Nat := 118140960795 + 538224 * 2 ^ 59
def prefixEnd_538224 : Nat := 4983230072969 + 3 ^ 40 * 538224 * 2
def baseEnd_538224 : Nat := 276367611785607429824759

theorem tailTrace_538224 : CollatzResearch.WordTrace tailWord_538224 prefixEnd_538224 276367611785607429824759 := by
  unfold tailWord_538224
  simp only [CollatzResearch.WordTrace]
  refine ⟨9815321001056922093038863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13087094668075896124051817 9815321001056922093038863)
  ·
    refine ⟨14722981501585383139558295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9815321001056922093038863 14722981501585383139558295)
    ·
      refine ⟨22084472252378074709337443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14722981501585383139558295 22084472252378074709337443)
      ·
        refine ⟨33126708378567112064006165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22084472252378074709337443 33126708378567112064006165)
        ·
          refine ⟨1552814455245333378000289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33126708378567112064006165 1552814455245333378000289)
          ·
            refine ⟨1164610841434000033500217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1552814455245333378000289 1164610841434000033500217)
            ·
              refine ⟨873458131075500025125163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1164610841434000033500217 873458131075500025125163)
              ·
                refine ⟨1310187196613250037687745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873458131075500025125163 1310187196613250037687745)
                ·
                  refine ⟨982640397459937528265809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1310187196613250037687745 982640397459937528265809)
                  ·
                    refine ⟨736980298094953146199357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 982640397459937528265809 736980298094953146199357)
                    ·
                      refine ⟨276367611785607429824759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 736980298094953146199357 276367611785607429824759)
                      ·
                        rfl

theorem cell23_538224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 3].length) (baseStart_538224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538224 prefixEnd_538224 := by exact prefixLift 538224
  have htrace : WordTrace (prefixWord ++ tailWord_538224) baseStart_538224 baseEnd_538224 := by
    simpa [prefixWord, tailWord_538224, baseEnd_538224] using wordTrace_append hprefix tailTrace_538224
  have hstable : (prefixWord ++ tailWord_538224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538224).length < 2 ^ (prefixWord ++ tailWord_538224).sum := by decide
  have hdescent : baseEnd_538224 < baseStart_538224 := by decide
  rcases family_descends (prefixWord ++ tailWord_538224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538244 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 6]
def baseStart_538244 : Nat := 118140960795 + 538244 * 2 ^ 59
def prefixEnd_538244 : Nat := 4983230072969 + 3 ^ 40 * 538244 * 2
def baseEnd_538244 : Nat := 30708653488744150174963

theorem tailTrace_538244 : CollatzResearch.WordTrace tailWord_538244 prefixEnd_538244 30708653488744150174963 := by
  unfold tailWord_538244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9815685731020693800902893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13087580974694258401203857 9815685731020693800902893)
  ·
    refine ⟨3680882149132760175338585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9815685731020693800902893 3680882149132760175338585)
    ·
      refine ⟨2760661611849570131503939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3680882149132760175338585 2760661611849570131503939)
      ·
        refine ⟨4140992417774355197255909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2760661611849570131503939 4140992417774355197255909)
        ·
          refine ⟨776436078332691599485483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4140992417774355197255909 776436078332691599485483)
          ·
            refine ⟨1164654117499037399228225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776436078332691599485483 1164654117499037399228225)
            ·
              refine ⟨873490588124278049421169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1164654117499037399228225 873490588124278049421169)
              ·
                refine ⟨655117941093208537065877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873490588124278049421169 655117941093208537065877)
                ·
                  refine ⟨30708653488744150174963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 655117941093208537065877 30708653488744150174963)
                  ·
                    rfl

theorem cell23_538244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_538244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538244 prefixEnd_538244 := by exact prefixLift 538244
  have htrace : WordTrace (prefixWord ++ tailWord_538244) baseStart_538244 baseEnd_538244 := by
    simpa [prefixWord, tailWord_538244, baseEnd_538244] using wordTrace_append hprefix tailTrace_538244
  have hstable : (prefixWord ++ tailWord_538244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538244).length < 2 ^ (prefixWord ++ tailWord_538244).sum := by decide
  have hdescent : baseEnd_538244 < baseStart_538244 := by decide
  rcases family_descends (prefixWord ++ tailWord_538244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538248 : List Nat := [2, 1, 3, 5, 1, 1, 1, 4, 1, 4]
def baseStart_538248 : Nat := 118140960795 + 538248 * 2 ^ 59
def prefixEnd_538248 : Nat := 4983230072969 + 3 ^ 40 * 538248 * 2
def baseEnd_538248 : Nat := 92126645107105111974883

theorem tailTrace_538248 : CollatzResearch.WordTrace tailWord_538248 prefixEnd_538248 92126645107105111974883 := by
  unfold tailWord_538248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9815758677013448142475699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13087678236017930856634265 9815758677013448142475699)
  ·
    refine ⟨14723638015520172213713549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9815758677013448142475699 14723638015520172213713549)
    ·
      refine ⟨5521364255820064580142581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14723638015520172213713549 5521364255820064580142581)
      ·
        refine ⟨517627898983131054388367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5521364255820064580142581 517627898983131054388367)
        ·
          refine ⟨776441848474696581582551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517627898983131054388367 776441848474696581582551)
          ·
            refine ⟨1164662772712044872373827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776441848474696581582551 1164662772712044872373827)
            ·
              refine ⟨1746994159068067308560741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1164662772712044872373827 1746994159068067308560741)
              ·
                refine ⟨327561404825262620355139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1746994159068067308560741 327561404825262620355139)
                ·
                  refine ⟨491342107237893930532709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327561404825262620355139 491342107237893930532709)
                  ·
                    refine ⟨92126645107105111974883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 491342107237893930532709 92126645107105111974883)
                    ·
                      rfl

theorem cell23_538248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_538248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538248 prefixEnd_538248 := by exact prefixLift 538248
  have htrace : WordTrace (prefixWord ++ tailWord_538248) baseStart_538248 baseEnd_538248 := by
    simpa [prefixWord, tailWord_538248, baseEnd_538248] using wordTrace_append hprefix tailTrace_538248
  have hstable : (prefixWord ++ tailWord_538248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538248).length < 2 ^ (prefixWord ++ tailWord_538248).sum := by decide
  have hdescent : baseEnd_538248 < baseStart_538248 := by decide
  rcases family_descends (prefixWord ++ tailWord_538248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538277 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_538277 : Nat := 118140960795 + 538277 * 2 ^ 59
def prefixEnd_538277 : Nat := 4983230072969 + 3 ^ 40 * 538277 * 2
def baseEnd_538277 : Nat := 276394826260295722462015

theorem tailTrace_538277 : CollatzResearch.WordTrace tailWord_538277 prefixEnd_538277 276394826260295722462015 := by
  unfold tailWord_538277
  simp only [CollatzResearch.WordTrace]
  refine ⟨19632575070921834237757085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13088383380614556158504723 19632575070921834237757085)
  ·
    refine ⟨7362215651595687839158907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19632575070921834237757085 7362215651595687839158907)
    ·
      refine ⟨11043323477393531758738361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7362215651595687839158907 11043323477393531758738361)
      ·
        refine ⟨8282492608045148819053771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11043323477393531758738361 8282492608045148819053771)
        ·
          refine ⟨12423738912067723228580657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8282492608045148819053771 12423738912067723228580657)
          ·
            refine ⟨9317804184050792421435493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12423738912067723228580657 9317804184050792421435493)
            ·
              refine ⟨1747088284509523579019155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9317804184050792421435493 1747088284509523579019155)
              ·
                refine ⟨2620632426764285368528733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747088284509523579019155 2620632426764285368528733)
                ·
                  refine ⟨982737160036607013198275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2620632426764285368528733 982737160036607013198275)
                  ·
                    refine ⟨1474105740054910519797413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 982737160036607013198275 1474105740054910519797413)
                    ·
                      refine ⟨276394826260295722462015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1474105740054910519797413 276394826260295722462015)
                      ·
                        rfl

theorem cell23_538277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_538277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538277 prefixEnd_538277 := by exact prefixLift 538277
  have htrace : WordTrace (prefixWord ++ tailWord_538277) baseStart_538277 baseEnd_538277 := by
    simpa [prefixWord, tailWord_538277, baseEnd_538277] using wordTrace_append hprefix tailTrace_538277
  have hstable : (prefixWord ++ tailWord_538277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538277).length < 2 ^ (prefixWord ++ tailWord_538277).sum := by decide
  have hdescent : baseEnd_538277 < baseStart_538277 := by decide
  rcases family_descends (prefixWord ++ tailWord_538277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538287 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 4, 4]
def baseStart_538287 : Nat := 118140960795 + 538287 * 2 ^ 59
def prefixEnd_538287 : Nat := 4983230072969 + 3 ^ 40 * 538287 * 2
def baseEnd_538287 : Nat := 92133320355613561112323

theorem tailTrace_538287 : CollatzResearch.WordTrace tailWord_538287 prefixEnd_538287 92133320355613561112323 := by
  unfold tailWord_538287
  simp only [CollatzResearch.WordTrace]
  refine ⟨19632939800885605945621115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13088626533923737297080743 19632939800885605945621115)
  ·
    refine ⟨29449409701328408918431673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19632939800885605945621115 29449409701328408918431673)
    ·
      refine ⟨22087057275996306688823755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29449409701328408918431673 22087057275996306688823755)
      ·
        refine ⟨33130585913994460033235633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22087057275996306688823755 33130585913994460033235633)
        ·
          refine ⟨24847939435495845024926725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33130585913994460033235633 24847939435495845024926725)
          ·
            refine ⟨4658988644155470942173761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24847939435495845024926725 4658988644155470942173761)
            ·
              refine ⟨3494241483116603206630321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4658988644155470942173761 3494241483116603206630321)
              ·
                refine ⟨2620681112337452404972741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3494241483116603206630321 2620681112337452404972741)
                ·
                  refine ⟨491377708563272325932389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2620681112337452404972741 491377708563272325932389)
                  ·
                    refine ⟨92133320355613561112323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 491377708563272325932389 92133320355613561112323)
                    ·
                      rfl

theorem cell23_538287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 4].length) (baseStart_538287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538287 prefixEnd_538287 := by exact prefixLift 538287
  have htrace : WordTrace (prefixWord ++ tailWord_538287) baseStart_538287 baseEnd_538287 := by
    simpa [prefixWord, tailWord_538287, baseEnd_538287] using wordTrace_append hprefix tailTrace_538287
  have hstable : (prefixWord ++ tailWord_538287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538287).length < 2 ^ (prefixWord ++ tailWord_538287).sum := by decide
  have hdescent : baseEnd_538287 < baseStart_538287 := by decide
  rcases family_descends (prefixWord ++ tailWord_538287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538311 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 3, 2, 2]
def baseStart_538311 : Nat := 118140960795 + 538311 * 2 ^ 59
def prefixEnd_538311 : Nat := 4983230072969 + 3 ^ 40 * 538311 * 2
def baseEnd_538311 : Nat := 276412284602548589436859

theorem tailTrace_538311 : CollatzResearch.WordTrace tailWord_538311 prefixEnd_538311 276412284602548589436859 := by
  unfold tailWord_538311
  simp only [CollatzResearch.WordTrace]
  refine ⟨19633815152798658044494787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13089210101865772029663191 19633815152798658044494787)
  ·
    refine ⟨29450722729197987066742181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19633815152798658044494787 29450722729197987066742181)
    ·
      refine ⟨5522010511724622575014159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29450722729197987066742181 5522010511724622575014159)
      ·
        refine ⟨8283015767586933862521239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5522010511724622575014159 8283015767586933862521239)
        ·
          refine ⟨12424523651380400793781859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8283015767586933862521239 12424523651380400793781859)
          ·
            refine ⟨18636785477070601190672789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12424523651380400793781859 18636785477070601190672789)
            ·
              refine ⟨873599319237684430812787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18636785477070601190672789 873599319237684430812787)
              ·
                refine ⟨1310398978856526646219181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873599319237684430812787 1310398978856526646219181)
                ·
                  refine ⟨491399617071197492332193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1310398978856526646219181 491399617071197492332193)
                  ·
                    refine ⟨368549712803398119249145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 491399617071197492332193 368549712803398119249145)
                    ·
                      refine ⟨276412284602548589436859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368549712803398119249145 276412284602548589436859)
                      ·
                        rfl

theorem cell23_538311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_538311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538311 prefixEnd_538311 := by exact prefixLift 538311
  have htrace : WordTrace (prefixWord ++ tailWord_538311) baseStart_538311 baseEnd_538311 := by
    simpa [prefixWord, tailWord_538311, baseEnd_538311] using wordTrace_append hprefix tailTrace_538311
  have hstable : (prefixWord ++ tailWord_538311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538311).length < 2 ^ (prefixWord ++ tailWord_538311).sum := by decide
  have hdescent : baseEnd_538311 < baseStart_538311 := by decide
  rcases family_descends (prefixWord ++ tailWord_538311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538314 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_538314 : Nat := 118140960795 + 538314 * 2 ^ 59
def prefixEnd_538314 : Nat := 4983230072969 + 3 ^ 40 * 538314 * 2
def baseEnd_538314 : Nat := 276413825044512077699345

theorem tailTrace_538314 : CollatzResearch.WordTrace tailWord_538314 prefixEnd_538314 276413825044512077699345 := by
  unfold tailWord_538314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4908481142946947389213499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13089283047858526371235997 4908481142946947389213499)
  ·
    refine ⟨7362721714420421083820249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4908481142946947389213499 7362721714420421083820249)
    ·
      refine ⟨5522041285815315812865187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7362721714420421083820249 5522041285815315812865187)
      ·
        refine ⟨8283061928722973719297781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5522041285815315812865187 8283061928722973719297781)
        ·
          refine ⟨776537055817778786184167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8283061928722973719297781 776537055817778786184167)
          ·
            refine ⟨1164805583726668179276251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776537055817778786184167 1164805583726668179276251)
            ·
              refine ⟨1747208375590002268914377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1164805583726668179276251 1747208375590002268914377)
              ·
                refine ⟨1310406281692501701685783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1747208375590002268914377 1310406281692501701685783)
                ·
                  refine ⟨1965609422538752552528675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310406281692501701685783 1965609422538752552528675)
                  ·
                    refine ⟨2948414133808128828793013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1965609422538752552528675 2948414133808128828793013)
                    ·
                      refine ⟨276413825044512077699345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2948414133808128828793013 276413825044512077699345)
                      ·
                        rfl

theorem cell23_538314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_538314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538314 prefixEnd_538314 := by exact prefixLift 538314
  have htrace : WordTrace (prefixWord ++ tailWord_538314) baseStart_538314 baseEnd_538314 := by
    simpa [prefixWord, tailWord_538314, baseEnd_538314] using wordTrace_append hprefix tailTrace_538314
  have hstable : (prefixWord ++ tailWord_538314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538314).length < 2 ^ (prefixWord ++ tailWord_538314).sum := by decide
  have hdescent : baseEnd_538314 < baseStart_538314 := by decide
  rcases family_descends (prefixWord ++ tailWord_538314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538320 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_538320 : Nat := 118140960795 + 538320 * 2 ^ 59
def prefixEnd_538320 : Nat := 4983230072969 + 3 ^ 40 * 538320 * 2
def baseEnd_538320 : Nat := 276416905928439054224317

theorem tailTrace_538320 : CollatzResearch.WordTrace tailWord_538320 prefixEnd_538320 276416905928439054224317 := by
  unfold tailWord_538320
  simp only [CollatzResearch.WordTrace]
  refine ⟨9817071704883026290786207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13089428939844035054381609 9817071704883026290786207)
  ·
    refine ⟨14725607557324539436179311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9817071704883026290786207 14725607557324539436179311)
    ·
      refine ⟨22088411335986809154268967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14725607557324539436179311 22088411335986809154268967)
      ·
        refine ⟨33132617003980213731403451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22088411335986809154268967 33132617003980213731403451)
        ·
          refine ⟨49698925505970320597105177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33132617003980213731403451 49698925505970320597105177)
          ·
            refine ⟨37274194129477740447828883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49698925505970320597105177 37274194129477740447828883)
            ·
              refine ⟨55911291194216610671743325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37274194129477740447828883 55911291194216610671743325)
              ·
                refine ⟨20966734197831229001903747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55911291194216610671743325 20966734197831229001903747)
                ·
                  refine ⟨31450101296746843502855621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20966734197831229001903747 31450101296746843502855621)
                  ·
                    refine ⟨5896893993140033156785429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31450101296746843502855621 5896893993140033156785429)
                    ·
                      refine ⟨276416905928439054224317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5896893993140033156785429 276416905928439054224317)
                      ·
                        rfl

theorem cell23_538320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_538320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538320 prefixEnd_538320 := by exact prefixLift 538320
  have htrace : WordTrace (prefixWord ++ tailWord_538320) baseStart_538320 baseEnd_538320 := by
    simpa [prefixWord, tailWord_538320, baseEnd_538320] using wordTrace_append hprefix tailTrace_538320
  have hstable : (prefixWord ++ tailWord_538320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538320).length < 2 ^ (prefixWord ++ tailWord_538320).sum := by decide
  have hdescent : baseEnd_538320 < baseStart_538320 := by decide
  rcases family_descends (prefixWord ++ tailWord_538320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538321 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 2, 4]
def baseStart_538321 : Nat := 118140960795 + 538321 * 2 ^ 59
def prefixEnd_538321 : Nat := 4983230072969 + 3 ^ 40 * 538321 * 2
def baseEnd_538321 : Nat := 92139139803031183437271

theorem tailTrace_538321 : CollatzResearch.WordTrace tailWord_538321 prefixEnd_538321 92139139803031183437271 := by
  unfold tailWord_538321
  simp only [CollatzResearch.WordTrace]
  refine ⟨19634179882762429752358817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13089453255174953168239211 19634179882762429752358817)
  ·
    refine ⟨14725634912071822314269113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19634179882762429752358817 14725634912071822314269113)
    ·
      refine ⟨11044226184053866735701835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14725634912071822314269113 11044226184053866735701835)
      ·
        refine ⟨16566339276080800103552753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11044226184053866735701835 16566339276080800103552753)
        ·
          refine ⟨12424754457060600077664565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16566339276080800103552753 12424754457060600077664565)
          ·
            refine ⟨1164820730349431257281053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12424754457060600077664565 1164820730349431257281053)
            ·
              refine ⟨436807773881036721480395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1164820730349431257281053 436807773881036721480395)
              ·
                refine ⟨655211660821555082220593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436807773881036721480395 655211660821555082220593)
                ·
                  refine ⟨491408745616166311665445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655211660821555082220593 491408745616166311665445)
                  ·
                    refine ⟨92139139803031183437271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 491408745616166311665445 92139139803031183437271)
                    ·
                      rfl

theorem cell23_538321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_538321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538321 prefixEnd_538321 := by exact prefixLift 538321
  have htrace : WordTrace (prefixWord ++ tailWord_538321) baseStart_538321 baseEnd_538321 := by
    simpa [prefixWord, tailWord_538321, baseEnd_538321] using wordTrace_append hprefix tailTrace_538321
  have hstable : (prefixWord ++ tailWord_538321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538321).length < 2 ^ (prefixWord ++ tailWord_538321).sum := by decide
  have hdescent : baseEnd_538321 < baseStart_538321 := by decide
  rcases family_descends (prefixWord ++ tailWord_538321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538324 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_538324 : Nat := 118140960795 + 538324 * 2 ^ 59
def prefixEnd_538324 : Nat := 4983230072969 + 3 ^ 40 * 538324 * 2
def baseEnd_538324 : Nat := 276418959851057038574299

theorem tailTrace_538324 : CollatzResearch.WordTrace tailWord_538324 prefixEnd_538324 276418959851057038574299 := by
  unfold tailWord_538324
  simp only [CollatzResearch.WordTrace]
  refine ⟨9817144650875780632359013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13089526201167707509812017 9817144650875780632359013)
  ·
    refine ⟨1840714622039208868567315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9817144650875780632359013 1840714622039208868567315)
    ·
      refine ⟨2761071933058813302850973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1840714622039208868567315 2761071933058813302850973)
      ·
        refine ⟨1035401974897054988569115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2761071933058813302850973 1035401974897054988569115)
        ·
          refine ⟨1553102962345582482853673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1035401974897054988569115 1553102962345582482853673)
          ·
            refine ⟨1164827221759186862140255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1553102962345582482853673 1164827221759186862140255)
            ·
              refine ⟨1747240832638780293210383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1164827221759186862140255 1747240832638780293210383)
              ·
                refine ⟨2620861248958170439815575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747240832638780293210383 2620861248958170439815575)
                ·
                  refine ⟨3931291873437255659723363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2620861248958170439815575 3931291873437255659723363)
                  ·
                    refine ⟨5896937810155883489585045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3931291873437255659723363 5896937810155883489585045)
                    ·
                      refine ⟨276418959851057038574299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5896937810155883489585045 276418959851057038574299)
                      ·
                        rfl

theorem cell23_538324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_538324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538324 prefixEnd_538324 := by exact prefixLift 538324
  have htrace : WordTrace (prefixWord ++ tailWord_538324) baseStart_538324 baseEnd_538324 := by
    simpa [prefixWord, tailWord_538324, baseEnd_538324] using wordTrace_append hprefix tailTrace_538324
  have hstable : (prefixWord ++ tailWord_538324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538324).length < 2 ^ (prefixWord ++ tailWord_538324).sum := by decide
  have hdescent : baseEnd_538324 < baseStart_538324 := by decide
  rcases family_descends (prefixWord ++ tailWord_538324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538378 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3]
def baseStart_538378 : Nat := 118140960795 + 538378 * 2 ^ 59
def prefixEnd_538378 : Nat := 4983230072969 + 3 ^ 40 * 538378 * 2
def baseEnd_538378 : Nat := 276446687806399827299051

theorem tailTrace_538378 : CollatzResearch.WordTrace tailWord_538378 prefixEnd_538378 276446687806399827299051 := by
  unfold tailWord_538378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4909064710888982121795947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13090839229037285658122525 4909064710888982121795947)
  ·
    refine ⟨7363597066333473182693921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4909064710888982121795947 7363597066333473182693921)
    ·
      refine ⟨5522697799750104887020441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7363597066333473182693921 5522697799750104887020441)
      ·
        refine ⟨4142023349812578665265331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5522697799750104887020441 4142023349812578665265331)
        ·
          refine ⟨6213035024718867997897997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4142023349812578665265331 6213035024718867997897997)
          ·
            refine ⟨2329888134269575499211749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6213035024718867997897997 2329888134269575499211749)
            ·
              refine ⟨436854025175545406102203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2329888134269575499211749 436854025175545406102203)
              ·
                refine ⟨655281037763318109153305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436854025175545406102203 655281037763318109153305)
                ·
                  refine ⟨491460778322488581864979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655281037763318109153305 491460778322488581864979)
                  ·
                    refine ⟨737191167483732872797469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 491460778322488581864979 737191167483732872797469)
                    ·
                      refine ⟨276446687806399827299051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 737191167483732872797469 276446687806399827299051)
                      ·
                        rfl

theorem cell23_538378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_538378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538378 prefixEnd_538378 := by exact prefixLift 538378
  have htrace : WordTrace (prefixWord ++ tailWord_538378) baseStart_538378 baseEnd_538378 := by
    simpa [prefixWord, tailWord_538378, baseEnd_538378] using wordTrace_append hprefix tailTrace_538378
  have hstable : (prefixWord ++ tailWord_538378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538378).length < 2 ^ (prefixWord ++ tailWord_538378).sum := by decide
  have hdescent : baseEnd_538378 < baseStart_538378 := by decide
  rcases family_descends (prefixWord ++ tailWord_538378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538387 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 3]
def baseStart_538387 : Nat := 118140960795 + 538387 * 2 ^ 59
def prefixEnd_538387 : Nat := 4983230072969 + 3 ^ 40 * 538387 * 2
def baseEnd_538387 : Nat := 276451309132290292086509

theorem tailTrace_538387 : CollatzResearch.WordTrace tailWord_538387 prefixEnd_538387 276451309132290292086509 := by
  unfold tailWord_538387
  simp only [CollatzResearch.WordTrace]
  refine ⟨19636587100523323024261415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13091058067015548682840943 19636587100523323024261415)
  ·
    refine ⟨29454880650784984536392123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19636587100523323024261415 29454880650784984536392123)
    ·
      refine ⟨44182320976177476804588185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29454880650784984536392123 44182320976177476804588185)
      ·
        refine ⟨33136740732133107603441139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44182320976177476804588185 33136740732133107603441139)
        ·
          refine ⟨49705111098199661405161709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33136740732133107603441139 49705111098199661405161709)
          ·
            refine ⟨18639416661824873026935641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49705111098199661405161709 18639416661824873026935641)
            ·
              refine ⟨13979562496368654770201731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18639416661824873026935641 13979562496368654770201731)
              ·
                refine ⟨20969343744552982155302597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13979562496368654770201731 20969343744552982155302597)
                ·
                  refine ⟨3931751952103684154119237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20969343744552982155302597 3931751952103684154119237)
                  ·
                    refine ⟨737203491019440778897357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931751952103684154119237 737203491019440778897357)
                    ·
                      refine ⟨276451309132290292086509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 737203491019440778897357 276451309132290292086509)
                      ·
                        rfl

theorem cell23_538387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 3].length) (baseStart_538387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538387 prefixEnd_538387 := by exact prefixLift 538387
  have htrace : WordTrace (prefixWord ++ tailWord_538387) baseStart_538387 baseEnd_538387 := by
    simpa [prefixWord, tailWord_538387, baseEnd_538387] using wordTrace_append hprefix tailTrace_538387
  have hstable : (prefixWord ++ tailWord_538387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538387).length < 2 ^ (prefixWord ++ tailWord_538387).sum := by decide
  have hdescent : baseEnd_538387 < baseStart_538387 := by decide
  rcases family_descends (prefixWord ++ tailWord_538387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538401 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 1, 4, 2]
def baseStart_538401 : Nat := 118140960795 + 538401 * 2 ^ 59
def prefixEnd_538401 : Nat := 4983230072969 + 3 ^ 40 * 538401 * 2
def baseEnd_538401 : Nat := 276458497861453237311445

theorem tailTrace_538401 : CollatzResearch.WordTrace tailWord_538401 prefixEnd_538401 276458497861453237311445 := by
  unfold tailWord_538401
  simp only [CollatzResearch.WordTrace]
  refine ⟨19637097722472603415271057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13091398481648402276847371 19637097722472603415271057)
  ·
    refine ⟨14727823291854452561453293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19637097722472603415271057 14727823291854452561453293)
    ·
      refine ⟨5522933734445419710544985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14727823291854452561453293 5522933734445419710544985)
      ·
        refine ⟨4142200300834064782908739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5522933734445419710544985 4142200300834064782908739)
        ·
          refine ⟨6213300451251097174363109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4142200300834064782908739 6213300451251097174363109)
          ·
            refine ⟨1164993834609580720193083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6213300451251097174363109 1164993834609580720193083)
            ·
              refine ⟨1747490751914371080289625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1164993834609580720193083 1747490751914371080289625)
              ·
                refine ⟨1310618063935778310217219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1747490751914371080289625 1310618063935778310217219)
                ·
                  refine ⟨1965927095903667465325829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310618063935778310217219 1965927095903667465325829)
                  ·
                    refine ⟨368611330481937649748593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1965927095903667465325829 368611330481937649748593)
                    ·
                      refine ⟨276458497861453237311445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368611330481937649748593 276458497861453237311445)
                      ·
                        rfl

theorem cell23_538401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_538401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538401 prefixEnd_538401 := by exact prefixLift 538401
  have htrace : WordTrace (prefixWord ++ tailWord_538401) baseStart_538401 baseEnd_538401 := by
    simpa [prefixWord, tailWord_538401, baseEnd_538401] using wordTrace_append hprefix tailTrace_538401
  have hstable : (prefixWord ++ tailWord_538401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538401).length < 2 ^ (prefixWord ++ tailWord_538401).sum := by decide
  have hdescent : baseEnd_538401 < baseStart_538401 := by decide
  rcases family_descends (prefixWord ++ tailWord_538401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538404 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_538404 : Nat := 118140960795 + 538404 * 2 ^ 59
def prefixEnd_538404 : Nat := 4983230072969 + 3 ^ 40 * 538404 * 2
def baseEnd_538404 : Nat := 276460038303416725573931

theorem tailTrace_538404 : CollatzResearch.WordTrace tailWord_538404 prefixEnd_538404 276460038303416725573931 := by
  unfold tailWord_538404
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818603570730867463815133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13091471427641156618420177 9818603570730867463815133)
  ·
    refine ⟨3681976339024075298930675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9818603570730867463815133 3681976339024075298930675)
    ·
      refine ⟨5522964508536112948396013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3681976339024075298930675 5522964508536112948396013)
      ·
        refine ⟨2071111690701042355648505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5522964508536112948396013 2071111690701042355648505)
        ·
          refine ⟨1553333768025781766736379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2071111690701042355648505 1553333768025781766736379)
          ·
            refine ⟨2330000652038672650104569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1553333768025781766736379 2330000652038672650104569)
            ·
              refine ⟨1747500489029004487578427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2330000652038672650104569 1747500489029004487578427)
              ·
                refine ⟨2621250733543506731367641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747500489029004487578427 2621250733543506731367641)
                ·
                  refine ⟨1965938050157630048525731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2621250733543506731367641 1965938050157630048525731)
                  ·
                    refine ⟨2948907075236445072788597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1965938050157630048525731 2948907075236445072788597)
                    ·
                      refine ⟨276460038303416725573931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2948907075236445072788597 276460038303416725573931)
                      ·
                        rfl

theorem cell23_538404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_538404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538404 prefixEnd_538404 := by exact prefixLift 538404
  have htrace : WordTrace (prefixWord ++ tailWord_538404) baseStart_538404 baseEnd_538404 := by
    simpa [prefixWord, tailWord_538404, baseEnd_538404] using wordTrace_append hprefix tailTrace_538404
  have hstable : (prefixWord ++ tailWord_538404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538404).length < 2 ^ (prefixWord ++ tailWord_538404).sum := by decide
  have hdescent : baseEnd_538404 < baseStart_538404 := by decide
  rcases family_descends (prefixWord ++ tailWord_538404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538418 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2]
def baseStart_538418 : Nat := 118140960795 + 538418 * 2 ^ 59
def prefixEnd_538418 : Nat := 4983230072969 + 3 ^ 40 * 538418 * 2
def baseEnd_538418 : Nat := 276467227032579670798867

theorem tailTrace_538418 : CollatzResearch.WordTrace tailWord_538418 prefixEnd_538418 276467227032579670798867 := by
  unfold tailWord_538418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4909429440852753829659977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13091811842274010212426605 4909429440852753829659977)
  ·
    refine ⟨3682072080639565372244983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4909429440852753829659977 3682072080639565372244983)
    ·
      refine ⟨5523108120959348058367475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3682072080639565372244983 5523108120959348058367475)
      ·
        refine ⟨8284662181439022087551213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5523108120959348058367475 8284662181439022087551213)
        ·
          refine ⟨3106748318039633282831705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8284662181439022087551213 3106748318039633282831705)
          ·
            refine ⟨2330061238529724962123779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3106748318039633282831705 2330061238529724962123779)
            ·
              refine ⟨3495091857794587443185669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330061238529724962123779 3495091857794587443185669)
              ·
                refine ⟨655329723336485145597313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3495091857794587443185669 655329723336485145597313)
                ·
                  refine ⟨491497292502363859197985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655329723336485145597313 491497292502363859197985)
                  ·
                    refine ⟨368622969376772894398489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 491497292502363859197985 368622969376772894398489)
                    ·
                      refine ⟨276467227032579670798867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368622969376772894398489 276467227032579670798867)
                      ·
                        rfl

theorem cell23_538418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_538418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538418 prefixEnd_538418 := by exact prefixLift 538418
  have htrace : WordTrace (prefixWord ++ tailWord_538418) baseStart_538418 baseEnd_538418 := by
    simpa [prefixWord, tailWord_538418, baseEnd_538418] using wordTrace_append hprefix tailTrace_538418
  have hstable : (prefixWord ++ tailWord_538418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538418).length < 2 ^ (prefixWord ++ tailWord_538418).sum := by decide
  have hdescent : baseEnd_538418 < baseStart_538418 := by decide
  rcases family_descends (prefixWord ++ tailWord_538418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538437 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_538437 : Nat := 118140960795 + 538437 * 2 ^ 59
def prefixEnd_538437 : Nat := 4983230072969 + 3 ^ 40 * 538437 * 2
def baseEnd_538437 : Nat := 92158994388338365487093

theorem tailTrace_538437 : CollatzResearch.WordTrace tailWord_538437 prefixEnd_538437 92158994388338365487093 := by
  unfold tailWord_538437
  simp only [CollatzResearch.WordTrace]
  refine ⟨19638410750342181563581565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13092273833561454375721043 19638410750342181563581565)
  ·
    refine ⟨7364404031378318086343087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19638410750342181563581565 7364404031378318086343087)
    ·
      refine ⟨11046606047067477129514631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7364404031378318086343087 11046606047067477129514631)
      ·
        refine ⟨16569909070601215694271947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11046606047067477129514631 16569909070601215694271947)
        ·
          refine ⟨24854863605901823541407921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16569909070601215694271947 24854863605901823541407921)
          ·
            refine ⟨18641147704426367656055941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24854863605901823541407921 18641147704426367656055941)
            ·
              refine ⟨3495215194579943935510489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18641147704426367656055941 3495215194579943935510489)
              ·
                refine ⟨2621411395934957951632867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3495215194579943935510489 2621411395934957951632867)
                ·
                  refine ⟨3932117093902436927449301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621411395934957951632867 3932117093902436927449301)
                  ·
                    refine ⟨92158994388338365487093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3932117093902436927449301 92158994388338365487093)
                    ·
                      rfl

theorem cell23_538437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_538437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538437 prefixEnd_538437 := by exact prefixLift 538437
  have htrace : WordTrace (prefixWord ++ tailWord_538437) baseStart_538437 baseEnd_538437 := by
    simpa [prefixWord, tailWord_538437, baseEnd_538437] using wordTrace_append hprefix tailTrace_538437
  have hstable : (prefixWord ++ tailWord_538437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538437).length < 2 ^ (prefixWord ++ tailWord_538437).sum := by decide
  have hdescent : baseEnd_538437 < baseStart_538437 := by decide
  rcases family_descends (prefixWord ++ tailWord_538437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538551 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 6, 3, 2]
def baseStart_538551 : Nat := 118140960795 + 538551 * 2 ^ 59
def prefixEnd_538551 : Nat := 4983230072969 + 3 ^ 40 * 538551 * 2
def baseEnd_538551 : Nat := 276535519959627650435755

theorem tailTrace_538551 : CollatzResearch.WordTrace tailWord_538551 prefixEnd_538551 276535519959627650435755 := by
  unfold tailWord_538551
  simp only [CollatzResearch.WordTrace]
  refine ⟨19642568671929179033231507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13095045781286119355487671 19642568671929179033231507)
  ·
    refine ⟨29463853007893768549847261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19642568671929179033231507 29463853007893768549847261)
    ·
      refine ⟨11048944877960163206192723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29463853007893768549847261 11048944877960163206192723)
      ·
        refine ⟨16573417316940244809289085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11048944877960163206192723 16573417316940244809289085)
        ·
          refine ⟨6215031493852591803483407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16573417316940244809289085 6215031493852591803483407)
          ·
            refine ⟨9322547240778887705225111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6215031493852591803483407 9322547240778887705225111)
            ·
              refine ⟨13983820861168331557837667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9322547240778887705225111 13983820861168331557837667)
              ·
                refine ⟨20975731291752497336756501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13983820861168331557837667 20975731291752497336756501)
                ·
                  refine ⟨983237404300898312660461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20975731291752497336756501 983237404300898312660461)
                  ·
                    refine ⟨368714026612836867247673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 983237404300898312660461 368714026612836867247673)
                    ·
                      refine ⟨276535519959627650435755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368714026612836867247673 276535519959627650435755)
                      ·
                        rfl

theorem cell23_538551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_538551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538551 prefixEnd_538551 := by exact prefixLift 538551
  have htrace : WordTrace (prefixWord ++ tailWord_538551) baseStart_538551 baseEnd_538551 := by
    simpa [prefixWord, tailWord_538551, baseEnd_538551] using wordTrace_append hprefix tailTrace_538551
  have hstable : (prefixWord ++ tailWord_538551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538551).length < 2 ^ (prefixWord ++ tailWord_538551).sum := by decide
  have hdescent : baseEnd_538551 < baseStart_538551 := by decide
  rcases family_descends (prefixWord ++ tailWord_538551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538568 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 2, 3, 2]
def baseStart_538568 : Nat := 118140960795 + 538568 * 2 ^ 59
def prefixEnd_538568 : Nat := 4983230072969 + 3 ^ 40 * 538568 * 2
def baseEnd_538568 : Nat := 276544249130754083923177

theorem tailTrace_538568 : CollatzResearch.WordTrace tailWord_538568 prefixEnd_538568 276544249130754083923177 := by
  unfold tailWord_538568
  simp only [CollatzResearch.WordTrace]
  refine ⟨9821594356433795468300179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13095459141911727291066905 9821594356433795468300179)
  ·
    refine ⟨14732391534650693202450269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9821594356433795468300179 14732391534650693202450269)
    ·
      refine ⟨5524646825494009950918851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14732391534650693202450269 5524646825494009950918851)
      ·
        refine ⟨8286970238241014926378277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5524646825494009950918851 8286970238241014926378277)
        ·
          refine ⟨1553806919670190298695927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8286970238241014926378277 1553806919670190298695927)
          ·
            refine ⟨2330710379505285448043891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1553806919670190298695927 2330710379505285448043891)
            ·
              refine ⟨3496065569257928172065837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330710379505285448043891 3496065569257928172065837)
              ·
                refine ⟨1311024588471723064524689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3496065569257928172065837 1311024588471723064524689)
                ·
                  refine ⟨983268441353792298393517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1311024588471723064524689 983268441353792298393517)
                  ·
                    refine ⟨368725665507672111897569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 983268441353792298393517 368725665507672111897569)
                    ·
                      refine ⟨276544249130754083923177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368725665507672111897569 276544249130754083923177)
                      ·
                        rfl

theorem cell23_538568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_538568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538568 prefixEnd_538568 := by exact prefixLift 538568
  have htrace : WordTrace (prefixWord ++ tailWord_538568) baseStart_538568 baseEnd_538568 := by
    simpa [prefixWord, tailWord_538568, baseEnd_538568] using wordTrace_append hprefix tailTrace_538568
  have hstable : (prefixWord ++ tailWord_538568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538568).length < 2 ^ (prefixWord ++ tailWord_538568).sum := by decide
  have hdescent : baseEnd_538568 < baseStart_538568 := by decide
  rcases family_descends (prefixWord ++ tailWord_538568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538632 : List Nat := [2, 1, 3, 2, 1, 2, 4, 3, 1, 2, 2]
def baseStart_538632 : Nat := 118140960795 + 538632 * 2 ^ 59
def prefixEnd_538632 : Nat := 4983230072969 + 3 ^ 40 * 538632 * 2
def baseEnd_538632 : Nat := 276577111892641833522883

theorem tailTrace_538632 : CollatzResearch.WordTrace tailWord_538632 prefixEnd_538632 276577111892641833522883 := by
  unfold tailWord_538632
  simp only [CollatzResearch.WordTrace]
  refine ⟨9822761492317864933465075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13097015323090486577953433 9822761492317864933465075)
  ·
    refine ⟨14734142238476797400197613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9822761492317864933465075 14734142238476797400197613)
    ·
      refine ⟨5525303339428799025074105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14734142238476797400197613 5525303339428799025074105)
      ·
        refine ⟨4143977504571599268805579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5525303339428799025074105 4143977504571599268805579)
        ·
          refine ⟨6215966256857398903208369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4143977504571599268805579 6215966256857398903208369)
          ·
            refine ⟨4661974692643049177406277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6215966256857398903208369 4661974692643049177406277)
            ·
              refine ⟨874120254870571720763677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4661974692643049177406277 874120254870571720763677)
              ·
                refine ⟨327795095576464395286379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 874120254870571720763677 327795095576464395286379)
                ·
                  refine ⟨491692643364696592929569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327795095576464395286379 491692643364696592929569)
                  ·
                    refine ⟨368769482523522444697177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 491692643364696592929569 368769482523522444697177)
                    ·
                      refine ⟨276577111892641833522883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368769482523522444697177 276577111892641833522883)
                      ·
                        rfl

theorem cell23_538632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_538632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538632 prefixEnd_538632 := by exact prefixLift 538632
  have htrace : WordTrace (prefixWord ++ tailWord_538632) baseStart_538632 baseEnd_538632 := by
    simpa [prefixWord, tailWord_538632, baseEnd_538632] using wordTrace_append hprefix tailTrace_538632
  have hstable : (prefixWord ++ tailWord_538632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538632).length < 2 ^ (prefixWord ++ tailWord_538632).sum := by decide
  have hdescent : baseEnd_538632 < baseStart_538632 := by decide
  rcases family_descends (prefixWord ++ tailWord_538632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538648 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 4, 1, 3]
def baseStart_538648 : Nat := 118140960795 + 538648 * 2 ^ 59
def prefixEnd_538648 : Nat := 4983230072969 + 3 ^ 40 * 538648 * 2
def baseEnd_538648 : Nat := 276585327583113770922809

theorem tailTrace_538648 : CollatzResearch.WordTrace tailWord_538648 prefixEnd_538648 276585327583113770922809 := by
  unfold tailWord_538648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9823053276288882299756299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13097404368385176399675065 9823053276288882299756299)
  ·
    refine ⟨14734579914433323449634449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9823053276288882299756299 14734579914433323449634449)
    ·
      refine ⟨11050934935824992587225837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14734579914433323449634449 11050934935824992587225837)
      ·
        refine ⟨4144100600934372220209689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11050934935824992587225837 4144100600934372220209689)
        ·
          refine ⟨3108075450700779165157267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4144100600934372220209689 3108075450700779165157267)
          ·
            refine ⟨4662113176051168747735901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3108075450700779165157267 4662113176051168747735901)
            ·
              refine ⟨1748292441019188280400963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4662113176051168747735901 1748292441019188280400963)
              ·
                refine ⟨2622438661528782420601445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1748292441019188280400963 2622438661528782420601445)
                ·
                  refine ⟨491707249036646703862771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2622438661528782420601445 491707249036646703862771)
                  ·
                    refine ⟨737560873554970055794157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 491707249036646703862771 737560873554970055794157)
                    ·
                      refine ⟨276585327583113770922809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 737560873554970055794157 276585327583113770922809)
                      ·
                        rfl

theorem cell23_538648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_538648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538648 prefixEnd_538648 := by exact prefixLift 538648
  have htrace : WordTrace (prefixWord ++ tailWord_538648) baseStart_538648 baseEnd_538648 := by
    simpa [prefixWord, tailWord_538648, baseEnd_538648] using wordTrace_append hprefix tailTrace_538648
  have hstable : (prefixWord ++ tailWord_538648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538648).length < 2 ^ (prefixWord ++ tailWord_538648).sum := by decide
  have hdescent : baseEnd_538648 < baseStart_538648 := by decide
  rcases family_descends (prefixWord ++ tailWord_538648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538705 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 2, 2, 2]
def baseStart_538705 : Nat := 118140960795 + 538705 * 2 ^ 59
def prefixEnd_538705 : Nat := 4983230072969 + 3 ^ 40 * 538705 * 2
def baseEnd_538705 : Nat := 276614595980420047910047

theorem tailTrace_538705 : CollatzResearch.WordTrace tailWord_538705 prefixEnd_538705 276614595980420047910047 := by
  unfold tailWord_538705
  simp only [CollatzResearch.WordTrace]
  refine ⟨19648185513371263334337569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13098790342247508889558379 19648185513371263334337569)
  ·
    refine ⟨14736139135028447500753177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19648185513371263334337569 14736139135028447500753177)
    ·
      refine ⟨11052104351271335625564883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14736139135028447500753177 11052104351271335625564883)
      ·
        refine ⟨16578156526907003438347325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11052104351271335625564883 16578156526907003438347325)
        ·
          refine ⟨6216808697590126289380247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16578156526907003438347325 6216808697590126289380247)
          ·
            refine ⟨9325213046385189434070371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6216808697590126289380247 9325213046385189434070371)
            ·
              refine ⟨13987819569577784151105557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9325213046385189434070371 13987819569577784151105557)
              ·
                refine ⟨655679042323958632083073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13987819569577784151105557 655679042323958632083073)
                ·
                  refine ⟨491759281742968974062305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655679042323958632083073 491759281742968974062305)
                  ·
                    refine ⟨368819461307226730546729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 491759281742968974062305 368819461307226730546729)
                    ·
                      refine ⟨276614595980420047910047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368819461307226730546729 276614595980420047910047)
                      ·
                        rfl

theorem cell23_538705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_538705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538705 prefixEnd_538705 := by exact prefixLift 538705
  have htrace : WordTrace (prefixWord ++ tailWord_538705) baseStart_538705 baseEnd_538705 := by
    simpa [prefixWord, tailWord_538705, baseEnd_538705] using wordTrace_append hprefix tailTrace_538705
  have hstable : (prefixWord ++ tailWord_538705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538705).length < 2 ^ (prefixWord ++ tailWord_538705).sum := by decide
  have hdescent : baseEnd_538705 < baseStart_538705 := by decide
  rcases family_descends (prefixWord ++ tailWord_538705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538711 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 7]
def baseStart_538711 : Nat := 118140960795 + 538711 * 2 ^ 59
def prefixEnd_538711 : Nat := 4983230072969 + 3 ^ 40 * 538711 * 2
def baseEnd_538711 : Nat := 30735297429371891603891

theorem tailTrace_538711 : CollatzResearch.WordTrace tailWord_538711 prefixEnd_538711 30735297429371891603891 := by
  unfold tailWord_538711
  simp only [CollatzResearch.WordTrace]
  refine ⟨19648404351349526359055987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13098936234233017572703991 19648404351349526359055987)
  ·
    refine ⟨29472606527024289538583981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19648404351349526359055987 29472606527024289538583981)
    ·
      refine ⟨11052227447634108576968993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29472606527024289538583981 11052227447634108576968993)
      ·
        refine ⟨8289170585725581432726745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11052227447634108576968993 8289170585725581432726745)
        ·
          refine ⟨6216877939294186074545059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8289170585725581432726745 6216877939294186074545059)
          ·
            refine ⟨9325316908941279111817589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6216877939294186074545059 9325316908941279111817589)
            ·
              refine ⟨874248460213244916732899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9325316908941279111817589 874248460213244916732899)
              ·
                refine ⟨1311372690319867375099349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 874248460213244916732899 1311372690319867375099349)
                ·
                  refine ⟨30735297429371891603891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1311372690319867375099349 30735297429371891603891)
                  ·
                    rfl

theorem cell23_538711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 7].length) (baseStart_538711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538711 prefixEnd_538711 := by exact prefixLift 538711
  have htrace : WordTrace (prefixWord ++ tailWord_538711) baseStart_538711 baseEnd_538711 := by
    simpa [prefixWord, tailWord_538711, baseEnd_538711] using wordTrace_append hprefix tailTrace_538711
  have hstable : (prefixWord ++ tailWord_538711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538711).length < 2 ^ (prefixWord ++ tailWord_538711).sum := by decide
  have hdescent : baseEnd_538711 < baseStart_538711 := by decide
  rcases family_descends (prefixWord ++ tailWord_538711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538721 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_538721 : Nat := 118140960795 + 538721 * 2 ^ 59
def prefixEnd_538721 : Nat := 4983230072969 + 3 ^ 40 * 538721 * 2
def baseEnd_538721 : Nat := 276622811670891985309973

theorem tailTrace_538721 : CollatzResearch.WordTrace tailWord_538721 prefixEnd_538721 276622811670891985309973 := by
  unfold tailWord_538721
  simp only [CollatzResearch.WordTrace]
  refine ⟨19648769081313298066920017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13099179387542198711280011 19648769081313298066920017)
  ·
    refine ⟨14736576810984973550190013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19648769081313298066920017 14736576810984973550190013)
    ·
      refine ⟨5526216304119365081321255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14736576810984973550190013 5526216304119365081321255)
      ·
        refine ⟨8289324456179047621981883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5526216304119365081321255 8289324456179047621981883)
        ·
          refine ⟨12433986684268571432972825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8289324456179047621981883 12433986684268571432972825)
          ·
            refine ⟨9325490013201428574729619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12433986684268571432972825 9325490013201428574729619)
            ·
              refine ⟨13988235019802142862094429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9325490013201428574729619 13988235019802142862094429)
              ·
                refine ⟨5245588132425803573285411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13988235019802142862094429 5245588132425803573285411)
                ·
                  refine ⟨7868382198638705359928117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5245588132425803573285411 7868382198638705359928117)
                  ·
                    refine ⟨737660831122378627493261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7868382198638705359928117 737660831122378627493261)
                    ·
                      refine ⟨276622811670891985309973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 737660831122378627493261 276622811670891985309973)
                      ·
                        rfl

theorem cell23_538721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_538721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538721 prefixEnd_538721 := by exact prefixLift 538721
  have htrace : WordTrace (prefixWord ++ tailWord_538721) baseStart_538721 baseEnd_538721 := by
    simpa [prefixWord, tailWord_538721, baseEnd_538721] using wordTrace_append hprefix tailTrace_538721
  have hstable : (prefixWord ++ tailWord_538721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538721).length < 2 ^ (prefixWord ++ tailWord_538721).sum := by decide
  have hdescent : baseEnd_538721 < baseStart_538721 := by decide
  rcases family_descends (prefixWord ++ tailWord_538721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538762 : List Nat := [3, 1, 2, 3, 1, 4, 2, 2, 5]
def baseStart_538762 : Nat := 118140960795 + 538762 * 2 ^ 59
def prefixEnd_538762 : Nat := 4983230072969 + 3 ^ 40 * 538762 * 2
def baseEnd_538762 : Nat := 30738207153080702766365

theorem tailTrace_538762 : CollatzResearch.WordTrace tailWord_538762 prefixEnd_538762 30738207153080702766365 := by
  unfold tailWord_538762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4912566118541190517290635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13100176316109841379441693 4912566118541190517290635)
  ·
    refine ⟨7368849177811785775935953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4912566118541190517290635 7368849177811785775935953)
    ·
      refine ⟨5526636883358839331951965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7368849177811785775935953 5526636883358839331951965)
      ·
        refine ⟨2072488831259564749481987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5526636883358839331951965 2072488831259564749481987)
        ·
          refine ⟨3108733246889347124222981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2072488831259564749481987 3108733246889347124222981)
          ·
            refine ⟨582887483791752585791809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3108733246889347124222981 582887483791752585791809)
            ·
              refine ⟨437165612843814439343857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582887483791752585791809 437165612843814439343857)
              ·
                refine ⟨327874209632860829507893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437165612843814439343857 327874209632860829507893)
                ·
                  refine ⟨30738207153080702766365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 327874209632860829507893 30738207153080702766365)
                  ·
                    rfl

theorem cell23_538762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_538762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538762 prefixEnd_538762 := by exact prefixLift 538762
  have htrace : WordTrace (prefixWord ++ tailWord_538762) baseStart_538762 baseEnd_538762 := by
    simpa [prefixWord, tailWord_538762, baseEnd_538762] using wordTrace_append hprefix tailTrace_538762
  have hstable : (prefixWord ++ tailWord_538762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538762).length < 2 ^ (prefixWord ++ tailWord_538762).sum := by decide
  have hdescent : baseEnd_538762 < baseStart_538762 := by decide
  rcases family_descends (prefixWord ++ tailWord_538762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538772 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_538772 : Nat := 118140960795 + 538772 * 2 ^ 59
def prefixEnd_538772 : Nat := 4983230072969 + 3 ^ 40 * 538772 * 2
def baseEnd_538772 : Nat := 276648999184271285772239

theorem tailTrace_538772 : CollatzResearch.WordTrace tailWord_538772 prefixEnd_538772 276648999184271285772239 := by
  unfold tailWord_538772
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825314602064266888513285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13100419469419022518017713 9825314602064266888513285)
  ·
    refine ⟨1842246487887050041596241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9825314602064266888513285 1842246487887050041596241)
    ·
      refine ⟨1381684865915287531197181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1842246487887050041596241 1381684865915287531197181)
      ·
        refine ⟨518131824718232824198943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1381684865915287531197181 518131824718232824198943)
        ·
          refine ⟨777197737077349236298415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518131824718232824198943 777197737077349236298415)
          ·
            refine ⟨1165796605616023854447623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777197737077349236298415 1165796605616023854447623)
            ·
              refine ⟨1748694908424035781671435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165796605616023854447623 1748694908424035781671435)
              ·
                refine ⟨2623042362636053672507153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1748694908424035781671435 2623042362636053672507153)
                ·
                  refine ⟨1967281771977040254380365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2623042362636053672507153 1967281771977040254380365)
                  ·
                    refine ⟨737730664491390095392637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1967281771977040254380365 737730664491390095392637)
                    ·
                      refine ⟨276648999184271285772239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 737730664491390095392637 276648999184271285772239)
                      ·
                        rfl

theorem cell23_538772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_538772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538772 prefixEnd_538772 := by exact prefixLift 538772
  have htrace : WordTrace (prefixWord ++ tailWord_538772) baseStart_538772 baseEnd_538772 := by
    simpa [prefixWord, tailWord_538772, baseEnd_538772] using wordTrace_append hprefix tailTrace_538772
  have hstable : (prefixWord ++ tailWord_538772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538772).length < 2 ^ (prefixWord ++ tailWord_538772).sum := by decide
  have hdescent : baseEnd_538772 < baseStart_538772 := by decide
  rcases family_descends (prefixWord ++ tailWord_538772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538821 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_538821 : Nat := 118140960795 + 538821 * 2 ^ 59
def prefixEnd_538821 : Nat := 4983230072969 + 3 ^ 40 * 538821 * 2
def baseEnd_538821 : Nat := 276674159736341594059513

theorem tailTrace_538821 : CollatzResearch.WordTrace tailWord_538821 prefixEnd_538821 276674159736341594059513 := by
  unfold tailWord_538821
  simp only [CollatzResearch.WordTrace]
  refine ⟨19652416380951015145560317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13101610920634010097040211 19652416380951015145560317)
  ·
    refine ⟨7369656142856630679585119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19652416380951015145560317 7369656142856630679585119)
    ·
      refine ⟨11054484214284946019377679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7369656142856630679585119 11054484214284946019377679)
      ·
        refine ⟨16581726321427419029066519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11054484214284946019377679 16581726321427419029066519)
        ·
          refine ⟨24872589482141128543599779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16581726321427419029066519 24872589482141128543599779)
          ·
            refine ⟨37308884223211692815399669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24872589482141128543599779 37308884223211692815399669)
            ·
              refine ⟨3497707895926096201443719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37308884223211692815399669 3497707895926096201443719)
              ·
                refine ⟨5246561843889144302165579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497707895926096201443719 5246561843889144302165579)
                ·
                  refine ⟨7869842765833716453248369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5246561843889144302165579 7869842765833716453248369)
                  ·
                    refine ⟨5902382074375287339936277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7869842765833716453248369 5902382074375287339936277)
                    ·
                      refine ⟨276674159736341594059513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5902382074375287339936277 276674159736341594059513)
                      ·
                        rfl

theorem cell23_538821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_538821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538821 prefixEnd_538821 := by exact prefixLift 538821
  have htrace : WordTrace (prefixWord ++ tailWord_538821) baseStart_538821 baseEnd_538821 := by
    simpa [prefixWord, tailWord_538821, baseEnd_538821] using wordTrace_append hprefix tailTrace_538821
  have hstable : (prefixWord ++ tailWord_538821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538821).length < 2 ^ (prefixWord ++ tailWord_538821).sum := by decide
  have hdescent : baseEnd_538821 < baseStart_538821 := by decide
  rcases family_descends (prefixWord ++ tailWord_538821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538841 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_538841 : Nat := 118140960795 + 538841 * 2 ^ 59
def prefixEnd_538841 : Nat := 4983230072969 + 3 ^ 40 * 538841 * 2
def baseEnd_538841 : Nat := 276684429349431515809421

theorem tailTrace_538841 : CollatzResearch.WordTrace tailWord_538841 prefixEnd_538841 276684429349431515809421 := by
  unfold tailWord_538841
  simp only [CollatzResearch.WordTrace]
  refine ⟨19653145840878558561288377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13102097227252372374192251 19653145840878558561288377)
  ·
    refine ⟨14739859380658918920966283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19653145840878558561288377 14739859380658918920966283)
    ·
      refine ⟨22109789070988378381449425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14739859380658918920966283 22109789070988378381449425)
      ·
        refine ⟨16582341803241283786087069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22109789070988378381449425 16582341803241283786087069)
        ·
          refine ⟨6218378176215481419782651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16582341803241283786087069 6218378176215481419782651)
          ·
            refine ⟨9327567264323222129673977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6218378176215481419782651 9327567264323222129673977)
            ·
              refine ⟨6995675448242416597255483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9327567264323222129673977 6995675448242416597255483)
              ·
                refine ⟨10493513172363624895883225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6995675448242416597255483 10493513172363624895883225)
                ·
                  refine ⟨7870134879272718671912419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10493513172363624895883225 7870134879272718671912419)
                  ·
                    refine ⟨11805202318909078007868629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7870134879272718671912419 11805202318909078007868629)
                    ·
                      refine ⟨276684429349431515809421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11805202318909078007868629 276684429349431515809421)
                      ·
                        rfl

theorem cell23_538841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_538841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538841 prefixEnd_538841 := by exact prefixLift 538841
  have htrace : WordTrace (prefixWord ++ tailWord_538841) baseStart_538841 baseEnd_538841 := by
    simpa [prefixWord, tailWord_538841, baseEnd_538841] using wordTrace_append hprefix tailTrace_538841
  have hstable : (prefixWord ++ tailWord_538841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538841).length < 2 ^ (prefixWord ++ tailWord_538841).sum := by decide
  have hdescent : baseEnd_538841 < baseStart_538841 := by decide
  rcases family_descends (prefixWord ++ tailWord_538841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538879 : List Nat := [1, 1, 2, 2, 1, 4, 5, 2, 1, 1, 3]
def baseStart_538879 : Nat := 118140960795 + 538879 * 2 ^ 59
def prefixEnd_538879 : Nat := 4983230072969 + 3 ^ 40 * 538879 * 2
def baseEnd_538879 : Nat := 276703941614302367134247

theorem tailTrace_538879 : CollatzResearch.WordTrace tailWord_538879 prefixEnd_538879 276703941614302367134247 := by
  unfold tailWord_538879
  simp only [CollatzResearch.WordTrace]
  refine ⟨19654531814740891051171691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13103021209827260700781127 19654531814740891051171691)
  ·
    refine ⟨29481797722111336576757537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19654531814740891051171691 29481797722111336576757537)
    ·
      refine ⟨22111348291583502432568153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29481797722111336576757537 22111348291583502432568153)
      ·
        refine ⟨16583511218687626824426115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22111348291583502432568153 16583511218687626824426115)
        ·
          refine ⟨24875266828031440236639173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16583511218687626824426115 24875266828031440236639173)
          ·
            refine ⟨4664112530255895044369845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24875266828031440236639173 4664112530255895044369845)
            ·
              refine ⟨437260549711490160409673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4664112530255895044369845 437260549711490160409673)
              ·
                refine ⟨327945412283617620307255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437260549711490160409673 327945412283617620307255)
                ·
                  refine ⟨491918118425426430460883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327945412283617620307255 491918118425426430460883)
                  ·
                    refine ⟨737877177638139645691325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 491918118425426430460883 737877177638139645691325)
                    ·
                      refine ⟨276703941614302367134247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 737877177638139645691325 276703941614302367134247)
                      ·
                        rfl

theorem cell23_538879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 1, 1, 3].length) (baseStart_538879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538879 prefixEnd_538879 := by exact prefixLift 538879
  have htrace : WordTrace (prefixWord ++ tailWord_538879) baseStart_538879 baseEnd_538879 := by
    simpa [prefixWord, tailWord_538879, baseEnd_538879] using wordTrace_append hprefix tailTrace_538879
  have hstable : (prefixWord ++ tailWord_538879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538879).length < 2 ^ (prefixWord ++ tailWord_538879).sum := by decide
  have hdescent : baseEnd_538879 < baseStart_538879 := by decide
  rcases family_descends (prefixWord ++ tailWord_538879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538925 : List Nat := [1, 5, 3, 1, 2, 11]
def baseStart_538925 : Nat := 118140960795 + 538925 * 2 ^ 59
def prefixEnd_538925 : Nat := 4983230072969 + 3 ^ 40 * 538925 * 2
def baseEnd_538925 : Nat := 1138796550306210646745

theorem tailTrace_538925 : CollatzResearch.WordTrace tailWord_538925 prefixEnd_538925 1138796550306210646745 := by
  unfold tailWord_538925
  simp only [CollatzResearch.WordTrace]
  refine ⟨19656209572574240907346229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13104139715049493938230819 19656209572574240907346229)
  ·
    refine ⟨1842769647428835085063709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19656209572574240907346229 1842769647428835085063709)
    ·
      refine ⟨691038617785813156898891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1842769647428835085063709 691038617785813156898891)
      ·
        refine ⟨1036557926678719735348337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691038617785813156898891 1036557926678719735348337)
        ·
          refine ⟨777418445009039801511253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1036557926678719735348337 777418445009039801511253)
          ·
            refine ⟨1138796550306210646745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 777418445009039801511253 1138796550306210646745)
            ·
              rfl

theorem cell23_538925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 11].length) (baseStart_538925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538925 prefixEnd_538925 := by exact prefixLift 538925
  have htrace : WordTrace (prefixWord ++ tailWord_538925) baseStart_538925 baseEnd_538925 := by
    simpa [prefixWord, tailWord_538925, baseEnd_538925] using wordTrace_append hprefix tailTrace_538925
  have hstable : (prefixWord ++ tailWord_538925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538925).length < 2 ^ (prefixWord ++ tailWord_538925).sum := by decide
  have hdescent : baseEnd_538925 < baseStart_538925 := by decide
  rcases family_descends (prefixWord ++ tailWord_538925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538935 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 4, 1, 3]
def baseStart_538935 : Nat := 118140960795 + 538935 * 2 ^ 59
def prefixEnd_538935 : Nat := 4983230072969 + 3 ^ 40 * 538935 * 2
def baseEnd_538935 : Nat := 276732696530954148033989

theorem tailTrace_538935 : CollatzResearch.WordTrace tailWord_538935 prefixEnd_538935 276732696530954148033989 := by
  unfold tailWord_538935
  simp only [CollatzResearch.WordTrace]
  refine ⟨19656574302538012615210259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13104382868358675076806839 19656574302538012615210259)
  ·
    refine ⟨29484861453807018922815389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19656574302538012615210259 29484861453807018922815389)
    ·
      refine ⟨11056823045177632096055771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29484861453807018922815389 11056823045177632096055771)
      ·
        refine ⟨16585234567766448144083657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11056823045177632096055771 16585234567766448144083657)
        ·
          refine ⟨12438925925824836108062743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16585234567766448144083657 12438925925824836108062743)
          ·
            refine ⟨18658388888737254162094115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12438925925824836108062743 18658388888737254162094115)
            ·
              refine ⟨27987583333105881243141173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18658388888737254162094115 27987583333105881243141173)
              ·
                refine ⟨2623835937478676366544485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27987583333105881243141173 2623835937478676366544485)
                ·
                  refine ⟨491969238277251818727091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2623835937478676366544485 491969238277251818727091)
                  ·
                    refine ⟨737953857415877728090637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 491969238277251818727091 737953857415877728090637)
                    ·
                      refine ⟨276732696530954148033989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 737953857415877728090637 276732696530954148033989)
                      ·
                        rfl

theorem cell23_538935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_538935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538935 prefixEnd_538935 := by exact prefixLift 538935
  have htrace : WordTrace (prefixWord ++ tailWord_538935) baseStart_538935 baseEnd_538935 := by
    simpa [prefixWord, tailWord_538935, baseEnd_538935] using wordTrace_append hprefix tailTrace_538935
  have hstable : (prefixWord ++ tailWord_538935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538935).length < 2 ^ (prefixWord ++ tailWord_538935).sum := by decide
  have hdescent : baseEnd_538935 < baseStart_538935 := by decide
  rcases family_descends (prefixWord ++ tailWord_538935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538936 : List Nat := [2, 1, 2, 1, 3, 1, 6, 2, 1, 2, 2]
def baseStart_538936 : Nat := 118140960795 + 538936 * 2 ^ 59
def prefixEnd_538936 : Nat := 4983230072969 + 3 ^ 40 * 538936 * 2
def baseEnd_538936 : Nat := 276733210011608644121485

theorem tailTrace_538936 : CollatzResearch.WordTrace tailWord_538936 prefixEnd_538936 276733210011608644121485 := by
  unfold tailWord_538936
  simp only [CollatzResearch.WordTrace]
  refine ⟨9828305387767194892998331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13104407183689593190664441 9828305387767194892998331)
  ·
    refine ⟨14742458081650792339497497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9828305387767194892998331 14742458081650792339497497)
    ·
      refine ⟨11056843561238094254623123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14742458081650792339497497 11056843561238094254623123)
      ·
        refine ⟨16585265341857141381934685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11056843561238094254623123 16585265341857141381934685)
        ·
          refine ⟨6219474503196428018225507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16585265341857141381934685 6219474503196428018225507)
          ·
            refine ⟨9329211754794642027338261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6219474503196428018225507 9329211754794642027338261)
            ·
              refine ⟨437306801005998845031481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9329211754794642027338261 437306801005998845031481)
              ·
                refine ⟨327980100754499133773611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437306801005998845031481 327980100754499133773611)
                ·
                  refine ⟨491970151131748700660417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327980100754499133773611 491970151131748700660417)
                  ·
                    refine ⟨368977613348811525495313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 491970151131748700660417 368977613348811525495313)
                    ·
                      refine ⟨276733210011608644121485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368977613348811525495313 276733210011608644121485)
                      ·
                        rfl

theorem cell23_538936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 1, 2, 2].length) (baseStart_538936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538936 prefixEnd_538936 := by exact prefixLift 538936
  have htrace : WordTrace (prefixWord ++ tailWord_538936) baseStart_538936 baseEnd_538936 := by
    simpa [prefixWord, tailWord_538936, baseEnd_538936] using wordTrace_append hprefix tailTrace_538936
  have hstable : (prefixWord ++ tailWord_538936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538936).length < 2 ^ (prefixWord ++ tailWord_538936).sum := by decide
  have hdescent : baseEnd_538936 < baseStart_538936 := by decide
  rcases family_descends (prefixWord ++ tailWord_538936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538938 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_538938 : Nat := 118140960795 + 538938 * 2 ^ 59
def prefixEnd_538938 : Nat := 4983230072969 + 3 ^ 40 * 538938 * 2
def baseEnd_538938 : Nat := 92244745657639212098825

theorem tailTrace_538938 : CollatzResearch.WordTrace tailWord_538938 prefixEnd_538938 92244745657639212098825 := by
  unfold tailWord_538938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4914170930381786031892367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13104455814351429418379645 4914170930381786031892367)
  ·
    refine ⟨7371256395572679047838551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4914170930381786031892367 7371256395572679047838551)
    ·
      refine ⟨11056884593359018571757827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7371256395572679047838551 11056884593359018571757827)
      ·
        refine ⟨16585326890038527857636741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11056884593359018571757827 16585326890038527857636741)
        ·
          refine ⟨3109748791882223973306889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16585326890038527857636741 3109748791882223973306889)
          ·
            refine ⟨2332311593911667979980167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3109748791882223973306889 2332311593911667979980167)
            ·
              refine ⟨3498467390867501969970251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332311593911667979980167 3498467390867501969970251)
              ·
                refine ⟨5247701086301252954955377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498467390867501969970251 5247701086301252954955377)
                ·
                  refine ⟨3935775814725939716216533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5247701086301252954955377 3935775814725939716216533)
                  ·
                    refine ⟨92244745657639212098825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3935775814725939716216533 92244745657639212098825)
                    ·
                      rfl

theorem cell23_538938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_538938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538938 prefixEnd_538938 := by exact prefixLift 538938
  have htrace : WordTrace (prefixWord ++ tailWord_538938) baseStart_538938 baseEnd_538938 := by
    simpa [prefixWord, tailWord_538938, baseEnd_538938] using wordTrace_append hprefix tailTrace_538938
  have hstable : (prefixWord ++ tailWord_538938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538938).length < 2 ^ (prefixWord ++ tailWord_538938).sum := by decide
  have hdescent : baseEnd_538938 < baseStart_538938 := by decide
  rcases family_descends (prefixWord ++ tailWord_538938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538952 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_538952 : Nat := 118140960795 + 538952 * 2 ^ 59
def prefixEnd_538952 : Nat := 4983230072969 + 3 ^ 40 * 538952 * 2
def baseEnd_538952 : Nat := 276741425702080581521411

theorem tailTrace_538952 : CollatzResearch.WordTrace tailWord_538952 prefixEnd_538952 276741425702080581521411 := by
  unfold tailWord_538952
  simp only [CollatzResearch.WordTrace]
  refine ⟨9828597171738212259289555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13104796228984283012386073 9828597171738212259289555)
  ·
    refine ⟨14742895757607318388934333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9828597171738212259289555 14742895757607318388934333)
    ·
      refine ⟨5528585909102744395850375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14742895757607318388934333 5528585909102744395850375)
      ·
        refine ⟨8292878863654116593775563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5528585909102744395850375 8292878863654116593775563)
        ·
          refine ⟨12439318295481174890663345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8292878863654116593775563 12439318295481174890663345)
          ·
            refine ⟨9329488721610881167997509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12439318295481174890663345 9329488721610881167997509)
            ·
              refine ⟨1749279135302040218999533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9329488721610881167997509 1749279135302040218999533)
              ·
                refine ⟨655979675738265082124825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1749279135302040218999533 655979675738265082124825)
                ·
                  refine ⟨491984756803698811593619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655979675738265082124825 491984756803698811593619)
                  ·
                    refine ⟨737977135205548217390429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 491984756803698811593619 737977135205548217390429)
                    ·
                      refine ⟨276741425702080581521411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 737977135205548217390429 276741425702080581521411)
                      ·
                        rfl

theorem cell23_538952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_538952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538952 prefixEnd_538952 := by exact prefixLift 538952
  have htrace : WordTrace (prefixWord ++ tailWord_538952) baseStart_538952 baseEnd_538952 := by
    simpa [prefixWord, tailWord_538952, baseEnd_538952] using wordTrace_append hprefix tailTrace_538952
  have hstable : (prefixWord ++ tailWord_538952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538952).length < 2 ^ (prefixWord ++ tailWord_538952).sum := by decide
  have hdescent : baseEnd_538952 < baseStart_538952 := by decide
  rcases family_descends (prefixWord ++ tailWord_538952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538962 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_538962 : Nat := 118140960795 + 538962 * 2 ^ 59
def prefixEnd_538962 : Nat := 4983230072969 + 3 ^ 40 * 538962 * 2
def baseEnd_538962 : Nat := 276746560508625542396365

theorem tailTrace_538962 : CollatzResearch.WordTrace tailWord_538962 prefixEnd_538962 276746560508625542396365 := by
  unfold tailWord_538962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4914389768360049056610785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13105039382293464150962093 4914389768360049056610785)
  ·
    refine ⟨3685792326270036792458089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4914389768360049056610785 3685792326270036792458089)
    ·
      refine ⟨2764344244702527594343567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3685792326270036792458089 2764344244702527594343567)
      ·
        refine ⟨4146516367053791391515351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2764344244702527594343567 4146516367053791391515351)
        ·
          refine ⟨6219774550580687087273027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4146516367053791391515351 6219774550580687087273027)
          ·
            refine ⟨9329661825871030630909541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6219774550580687087273027 9329661825871030630909541)
            ·
              refine ⟨1749311592350818243295539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9329661825871030630909541 1749311592350818243295539)
              ·
                refine ⟨2623967388526227364943309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749311592350818243295539 2623967388526227364943309)
                ·
                  refine ⟨983987770697335261853741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2623967388526227364943309 983987770697335261853741)
                  ·
                    refine ⟨368995414011500723195153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 983987770697335261853741 368995414011500723195153)
                    ·
                      refine ⟨276746560508625542396365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 368995414011500723195153 276746560508625542396365)
                      ·
                        rfl

theorem cell23_538962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_538962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538962 prefixEnd_538962 := by exact prefixLift 538962
  have htrace : WordTrace (prefixWord ++ tailWord_538962) baseStart_538962 baseEnd_538962 := by
    simpa [prefixWord, tailWord_538962, baseEnd_538962] using wordTrace_append hprefix tailTrace_538962
  have hstable : (prefixWord ++ tailWord_538962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538962).length < 2 ^ (prefixWord ++ tailWord_538962).sum := by decide
  have hdescent : baseEnd_538962 < baseStart_538962 := by decide
  rcases family_descends (prefixWord ++ tailWord_538962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538986 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_538986 : Nat := 118140960795 + 538986 * 2 ^ 59
def prefixEnd_538986 : Nat := 4983230072969 + 3 ^ 40 * 538986 * 2
def baseEnd_538986 : Nat := 276758884044333448496255

theorem tailTrace_538986 : CollatzResearch.WordTrace tailWord_538986 prefixEnd_538986 276758884044333448496255 := by
  unfold tailWord_538986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4914608606338312081329203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13105622950235498883544541 4914608606338312081329203)
  ·
    refine ⟨7371912909507468121993805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4914608606338312081329203 7371912909507468121993805)
    ·
      refine ⟨2764467341065300545747677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7371912909507468121993805 2764467341065300545747677)
      ·
        refine ⟨1036675252899487704655379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2764467341065300545747677 1036675252899487704655379)
        ·
          refine ⟨1555012879349231556983069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036675252899487704655379 1555012879349231556983069)
          ·
            refine ⟨583129829755961833868651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1555012879349231556983069 583129829755961833868651)
            ·
              refine ⟨874694744633942750802977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583129829755961833868651 874694744633942750802977)
              ·
                refine ⟨656021058475457063102233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874694744633942750802977 656021058475457063102233)
                ·
                  refine ⟨492015793856592797326675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 656021058475457063102233 492015793856592797326675)
                  ·
                    refine ⟨738023690784889195990013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 492015793856592797326675 738023690784889195990013)
                    ·
                      refine ⟨276758884044333448496255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 738023690784889195990013 276758884044333448496255)
                      ·
                        rfl

theorem cell23_538986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_538986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_538986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_538986 prefixEnd_538986 := by exact prefixLift 538986
  have htrace : WordTrace (prefixWord ++ tailWord_538986) baseStart_538986 baseEnd_538986 := by
    simpa [prefixWord, tailWord_538986, baseEnd_538986] using wordTrace_append hprefix tailTrace_538986
  have hstable : (prefixWord ++ tailWord_538986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538986).length < 2 ^ (prefixWord ++ tailWord_538986).sum := by decide
  have hdescent : baseEnd_538986 < baseStart_538986 := by decide
  rcases family_descends (prefixWord ++ tailWord_538986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539005 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_539005 : Nat := 118140960795 + 539005 * 2 ^ 59
def prefixEnd_539005 : Nat := 4983230072969 + 3 ^ 40 * 539005 * 2
def baseEnd_539005 : Nat := 276768640176768874158667

theorem tailTrace_539005 : CollatzResearch.WordTrace tailWord_539005 prefixEnd_539005 276768640176768874158667 := by
  unfold tailWord_539005
  simp only [CollatzResearch.WordTrace]
  refine ⟨19659127412284414570258469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13106084941522943046838979 19659127412284414570258469)
  ·
    refine ⟨3686086389803327731923463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19659127412284414570258469 3686086389803327731923463)
    ·
      refine ⟨5529129584704991597885195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3686086389803327731923463 5529129584704991597885195)
      ·
        refine ⟨8293694377057487396827793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5529129584704991597885195 8293694377057487396827793)
        ·
          refine ⟨6220270782793115547620845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8293694377057487396827793 6220270782793115547620845)
          ·
            refine ⟨2332601543547418330357817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6220270782793115547620845 2332601543547418330357817)
            ·
              refine ⟨1749451157660563747768363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2332601543547418330357817 1749451157660563747768363)
              ·
                refine ⟨2624176736490845621652545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749451157660563747768363 2624176736490845621652545)
                ·
                  refine ⟨1968132552368134216239409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2624176736490845621652545 1968132552368134216239409)
                  ·
                    refine ⟨1476099414276100662179557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1968132552368134216239409 1476099414276100662179557)
                    ·
                      refine ⟨276768640176768874158667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1476099414276100662179557 276768640176768874158667)
                      ·
                        rfl

theorem cell23_539005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_539005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539005 prefixEnd_539005 := by exact prefixLift 539005
  have htrace : WordTrace (prefixWord ++ tailWord_539005) baseStart_539005 baseEnd_539005 := by
    simpa [prefixWord, tailWord_539005, baseEnd_539005] using wordTrace_append hprefix tailTrace_539005
  have hstable : (prefixWord ++ tailWord_539005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539005).length < 2 ^ (prefixWord ++ tailWord_539005).sum := by decide
  have hdescent : baseEnd_539005 < baseStart_539005 := by decide
  rcases family_descends (prefixWord ++ tailWord_539005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539009 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_539009 : Nat := 118140960795 + 539009 * 2 ^ 59
def prefixEnd_539009 : Nat := 4983230072969 + 3 ^ 40 * 539009 * 2
def baseEnd_539009 : Nat := 276770694099386858508649

theorem tailTrace_539009 : CollatzResearch.WordTrace tailWord_539009 prefixEnd_539009 276770694099386858508649 := by
  unfold tailWord_539009
  simp only [CollatzResearch.WordTrace]
  refine ⟨19659273304269923253404081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13106182202846615502269387 19659273304269923253404081)
  ·
    refine ⟨14744454978202442440053061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19659273304269923253404081 14744454978202442440053061)
    ·
      refine ⟨2764585308412957957509949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14744454978202442440053061 2764585308412957957509949)
      ·
        refine ⟨1036719490654859234066231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2764585308412957957509949 1036719490654859234066231)
        ·
          refine ⟨1555079235982288851099347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036719490654859234066231 1555079235982288851099347)
          ·
            refine ⟨2332618853973433276649021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555079235982288851099347 2332618853973433276649021)
            ·
              refine ⟨874732070240037478743383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2332618853973433276649021 874732070240037478743383)
              ·
                refine ⟨1312098105360056218115075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 874732070240037478743383 1312098105360056218115075)
                ·
                  refine ⟨1968147158040084327172613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312098105360056218115075 1968147158040084327172613)
                  ·
                    refine ⟨369027592132515811344865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1968147158040084327172613 369027592132515811344865)
                    ·
                      refine ⟨276770694099386858508649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 369027592132515811344865 276770694099386858508649)
                      ·
                        rfl

theorem cell23_539009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_539009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539009 prefixEnd_539009 := by exact prefixLift 539009
  have htrace : WordTrace (prefixWord ++ tailWord_539009) baseStart_539009 baseEnd_539009 := by
    simpa [prefixWord, tailWord_539009, baseEnd_539009] using wordTrace_append hprefix tailTrace_539009
  have hstable : (prefixWord ++ tailWord_539009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539009).length < 2 ^ (prefixWord ++ tailWord_539009).sum := by decide
  have hdescent : baseEnd_539009 < baseStart_539009 := by decide
  rcases family_descends (prefixWord ++ tailWord_539009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539045 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_539045 : Nat := 118140960795 + 539045 * 2 ^ 59
def prefixEnd_539045 : Nat := 4983230072969 + 3 ^ 40 * 539045 * 2
def baseEnd_539045 : Nat := 92263059800982905886161

theorem tailTrace_539045 : CollatzResearch.WordTrace tailWord_539045 prefixEnd_539045 92263059800982905886161 := by
  unfold tailWord_539045
  simp only [CollatzResearch.WordTrace]
  refine ⟨19660586332139501401714589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13107057554759667601143059 19660586332139501401714589)
  ·
    refine ⟨7372719874552313025642971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19660586332139501401714589 7372719874552313025642971)
    ·
      refine ⟨11059079811828469538464457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7372719874552313025642971 11059079811828469538464457)
      ·
        refine ⟨8294309858871352153848343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11059079811828469538464457 8294309858871352153848343)
        ·
          refine ⟨12441464788307028230772515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8294309858871352153848343 12441464788307028230772515)
          ·
            refine ⟨18662197182460542346158773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12441464788307028230772515 18662197182460542346158773)
            ·
              refine ⟨1749580985855675844952385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18662197182460542346158773 1749580985855675844952385)
              ·
                refine ⟨1312185739391756883714289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1749580985855675844952385 1312185739391756883714289)
                ·
                  refine ⟨984139304543817662785717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1312185739391756883714289 984139304543817662785717)
                  ·
                    refine ⟨92263059800982905886161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 984139304543817662785717 92263059800982905886161)
                    ·
                      rfl

theorem cell23_539045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_539045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539045 prefixEnd_539045 := by exact prefixLift 539045
  have htrace : WordTrace (prefixWord ++ tailWord_539045) baseStart_539045 baseEnd_539045 := by
    simpa [prefixWord, tailWord_539045, baseEnd_539045] using wordTrace_append hprefix tailTrace_539045
  have hstable : (prefixWord ++ tailWord_539045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539045).length < 2 ^ (prefixWord ++ tailWord_539045).sum := by decide
  have hdescent : baseEnd_539045 < baseStart_539045 := by decide
  rcases family_descends (prefixWord ++ tailWord_539045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539060 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_539060 : Nat := 118140960795 + 539060 * 2 ^ 59
def prefixEnd_539060 : Nat := 4983230072969 + 3 ^ 40 * 539060 * 2
def baseEnd_539060 : Nat := 276796881612766158970915

theorem tailTrace_539060 : CollatzResearch.WordTrace tailWord_539060 prefixEnd_539060 276796881612766158970915 := by
  unfold tailWord_539060
  simp only [CollatzResearch.WordTrace]
  refine ⟨9830566713542579481755317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13107422284723439309007089 9830566713542579481755317)
  ·
    refine ⟨921615629394616826414561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9830566713542579481755317 921615629394616826414561)
    ·
      refine ⟨691211722045962619810921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 921615629394616826414561 691211722045962619810921)
      ·
        refine ⟨518408791534471964858191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 691211722045962619810921 518408791534471964858191)
        ·
          refine ⟨777613187301707947287287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518408791534471964858191 777613187301707947287287)
          ·
            refine ⟨1166419780952561920930931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777613187301707947287287 1166419780952561920930931)
            ·
              refine ⟨1749629671428842881396397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166419780952561920930931 1749629671428842881396397)
              ·
                refine ⟨656111126785816080523649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1749629671428842881396397 656111126785816080523649)
                ·
                  refine ⟨492083345089362060392737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 656111126785816080523649 492083345089362060392737)
                  ·
                    refine ⟨369062508817021545294553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 492083345089362060392737 369062508817021545294553)
                    ·
                      refine ⟨276796881612766158970915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 369062508817021545294553 276796881612766158970915)
                      ·
                        rfl

theorem cell23_539060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_539060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539060 prefixEnd_539060 := by exact prefixLift 539060
  have htrace : WordTrace (prefixWord ++ tailWord_539060) baseStart_539060 baseEnd_539060 := by
    simpa [prefixWord, tailWord_539060, baseEnd_539060] using wordTrace_append hprefix tailTrace_539060
  have hstable : (prefixWord ++ tailWord_539060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539060).length < 2 ^ (prefixWord ++ tailWord_539060).sum := by decide
  have hdescent : baseEnd_539060 < baseStart_539060 := by decide
  rcases family_descends (prefixWord ++ tailWord_539060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539075 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 5, 4]
def baseStart_539075 : Nat := 118140960795 + 539075 * 2 ^ 59
def prefixEnd_539075 : Nat := 4983230072969 + 3 ^ 40 * 539075 * 2
def baseEnd_539075 : Nat := 92268194607527866761115

theorem tailTrace_539075 : CollatzResearch.WordTrace tailWord_539075 prefixEnd_539075 92268194607527866761115 := by
  unfold tailWord_539075
  simp only [CollatzResearch.WordTrace]
  refine ⟨19661680522030816525306679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13107787014687211016871119 19661680522030816525306679)
  ·
    refine ⟨29492520783046224787960019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19661680522030816525306679 29492520783046224787960019)
    ·
      refine ⟨44238781174569337181940029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29492520783046224787960019 44238781174569337181940029)
      ·
        refine ⟨16589542940463501443227511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44238781174569337181940029 16589542940463501443227511)
        ·
          refine ⟨24884314410695252164841267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16589542940463501443227511 24884314410695252164841267)
          ·
            refine ⟨37326471616042878247261901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24884314410695252164841267 37326471616042878247261901)
            ·
              refine ⟨13997426856016079342723213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37326471616042878247261901 13997426856016079342723213)
              ·
                refine ⟨5249035071006029753521205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13997426856016079342723213 5249035071006029753521205)
                ·
                  refine ⟨492097037906815289392613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5249035071006029753521205 492097037906815289392613)
                  ·
                    refine ⟨92268194607527866761115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 492097037906815289392613 92268194607527866761115)
                    ·
                      rfl

theorem cell23_539075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 4].length) (baseStart_539075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539075 prefixEnd_539075 := by exact prefixLift 539075
  have htrace : WordTrace (prefixWord ++ tailWord_539075) baseStart_539075 baseEnd_539075 := by
    simpa [prefixWord, tailWord_539075, baseEnd_539075] using wordTrace_append hprefix tailTrace_539075
  have hstable : (prefixWord ++ tailWord_539075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539075).length < 2 ^ (prefixWord ++ tailWord_539075).sum := by decide
  have hdescent : baseEnd_539075 < baseStart_539075 := by decide
  rcases family_descends (prefixWord ++ tailWord_539075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539082 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_539082 : Nat := 118140960795 + 539082 * 2 ^ 59
def prefixEnd_539082 : Nat := 4983230072969 + 3 ^ 40 * 539082 * 2
def baseEnd_539082 : Nat := 276808178187165072895813

theorem tailTrace_539082 : CollatzResearch.WordTrace tailWord_539082 prefixEnd_539082 276808178187165072895813 := by
  unfold tailWord_539082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4915483958251364180202875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13107957222003637813874333 4915483958251364180202875)
  ·
    refine ⟨7373225937377046270304313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4915483958251364180202875 7373225937377046270304313)
    ·
      refine ⟨5529919453032784702728235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7373225937377046270304313 5529919453032784702728235)
      ·
        refine ⟨8294879179549177054092353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5529919453032784702728235 8294879179549177054092353)
        ·
          refine ⟨6221159384661882790569265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8294879179549177054092353 6221159384661882790569265)
          ·
            refine ⟨4665869538496412092926949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6221159384661882790569265 4665869538496412092926949)
            ·
              refine ⟨874850538468077267423803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4665869538496412092926949 874850538468077267423803)
              ·
                refine ⟨1312275807702115901135705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 874850538468077267423803 1312275807702115901135705)
                ·
                  refine ⟨984206855776586925851779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1312275807702115901135705 984206855776586925851779)
                  ·
                    refine ⟨1476310283664880388777669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 984206855776586925851779 1476310283664880388777669)
                    ·
                      refine ⟨276808178187165072895813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1476310283664880388777669 276808178187165072895813)
                      ·
                        rfl

theorem cell23_539082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_539082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539082 prefixEnd_539082 := by exact prefixLift 539082
  have htrace : WordTrace (prefixWord ++ tailWord_539082) baseStart_539082 baseEnd_539082 := by
    simpa [prefixWord, tailWord_539082, baseEnd_539082] using wordTrace_append hprefix tailTrace_539082
  have hstable : (prefixWord ++ tailWord_539082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539082).length < 2 ^ (prefixWord ++ tailWord_539082).sum := by decide
  have hdescent : baseEnd_539082 < baseStart_539082 := by decide
  rcases family_descends (prefixWord ++ tailWord_539082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539135 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 3, 5]
def baseStart_539135 : Nat := 118140960795 + 539135 * 2 ^ 59
def prefixEnd_539135 : Nat := 4983230072969 + 3 ^ 40 * 539135 * 2
def baseEnd_539135 : Nat := 92278464220617788511023

theorem tailTrace_539135 : CollatzResearch.WordTrace tailWord_539135 prefixEnd_539135 92278464220617788511023 := by
  unfold tailWord_539135
  simp only [CollatzResearch.WordTrace]
  refine ⟨19663868901813446772490859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13109245934542297848327239 19663868901813446772490859)
  ·
    refine ⟨29495803352720170158736289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19663868901813446772490859 29495803352720170158736289)
    ·
      refine ⟨22121852514540127619052217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29495803352720170158736289 22121852514540127619052217)
      ·
        refine ⟨16591389385905095714289163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22121852514540127619052217 16591389385905095714289163)
        ·
          refine ⟨24887084078857643571433745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16591389385905095714289163 24887084078857643571433745)
          ·
            refine ⟨18665313059143232678575309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24887084078857643571433745 18665313059143232678575309)
            ·
              refine ⟨6999492397178712254465741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18665313059143232678575309 6999492397178712254465741)
              ·
                refine ⟨2624809648942017095424653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6999492397178712254465741 2624809648942017095424653)
                ·
                  refine ⟨984303618353256410784245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2624809648942017095424653 984303618353256410784245)
                  ·
                    refine ⟨92278464220617788511023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 984303618353256410784245 92278464220617788511023)
                    ·
                      rfl

theorem cell23_539135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_539135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539135 prefixEnd_539135 := by exact prefixLift 539135
  have htrace : WordTrace (prefixWord ++ tailWord_539135) baseStart_539135 baseEnd_539135 := by
    simpa [prefixWord, tailWord_539135, baseEnd_539135] using wordTrace_append hprefix tailTrace_539135
  have hstable : (prefixWord ++ tailWord_539135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539135).length < 2 ^ (prefixWord ++ tailWord_539135).sum := by decide
  have hdescent : baseEnd_539135 < baseStart_539135 := by decide
  rcases family_descends (prefixWord ++ tailWord_539135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539156 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 6]
def baseStart_539156 : Nat := 118140960795 + 539156 * 2 ^ 59
def prefixEnd_539156 : Nat := 4983230072969 + 3 ^ 40 * 539156 * 2
def baseEnd_539156 : Nat := 30760686195066420374497

theorem tailTrace_539156 : CollatzResearch.WordTrace tailWord_539156 prefixEnd_539156 30760686195066420374497 := by
  unfold tailWord_539156
  simp only [CollatzResearch.WordTrace]
  refine ⟨9832317417368683679502661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13109756556491578239336881 9832317417368683679502661)
  ·
    refine ⟨1843559515756628189906749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9832317417368683679502661 1843559515756628189906749)
    ·
      refine ⟨691334818408735571215031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1843559515756628189906749 691334818408735571215031)
      ·
        refine ⟨1037002227613103356822547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691334818408735571215031 1037002227613103356822547)
        ·
          refine ⟨1555503341419655035233821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037002227613103356822547 1555503341419655035233821)
          ·
            refine ⟨583313753032370638212683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1555503341419655035233821 583313753032370638212683)
            ·
              refine ⟨874970629548555957319025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583313753032370638212683 874970629548555957319025)
              ·
                refine ⟨656227972161416967989269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874970629548555957319025 656227972161416967989269)
                ·
                  refine ⟨30760686195066420374497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 656227972161416967989269 30760686195066420374497)
                  ·
                    rfl

theorem cell23_539156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_539156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539156 prefixEnd_539156 := by exact prefixLift 539156
  have htrace : WordTrace (prefixWord ++ tailWord_539156) baseStart_539156 baseEnd_539156 := by
    simpa [prefixWord, tailWord_539156, baseEnd_539156] using wordTrace_append hprefix tailTrace_539156
  have hstable : (prefixWord ++ tailWord_539156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539156).length < 2 ^ (prefixWord ++ tailWord_539156).sum := by decide
  have hdescent : baseEnd_539156 < baseStart_539156 := by decide
  rcases family_descends (prefixWord ++ tailWord_539156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539189 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_539189 : Nat := 118140960795 + 539189 * 2 ^ 59
def prefixEnd_539189 : Nat := 4983230072969 + 3 ^ 40 * 539189 * 2
def baseEnd_539189 : Nat := 276863120617196154257821

theorem tailTrace_539189 : CollatzResearch.WordTrace tailWord_539189 prefixEnd_539189 276863120617196154257821 := by
  unfold tailWord_539189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19665838443617813994956621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13110558962411875996637747 19665838443617813994956621)
  ·
    refine ⟨7374689416356680248108733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19665838443617813994956621 7374689416356680248108733)
    ·
      refine ⟨2765508531133755093040775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7374689416356680248108733 2765508531133755093040775)
      ·
        refine ⟨4148262796700632639561163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2765508531133755093040775 4148262796700632639561163)
        ·
          refine ⟨6222394195050948959341745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148262796700632639561163 6222394195050948959341745)
          ·
            refine ⟨4666795646288211719506309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6222394195050948959341745 4666795646288211719506309)
            ·
              refine ⟨875024183679039697407433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4666795646288211719506309 875024183679039697407433)
              ·
                refine ⟨656268137759279773055575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875024183679039697407433 656268137759279773055575)
                ·
                  refine ⟨984402206638919659583363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656268137759279773055575 984402206638919659583363)
                  ·
                    refine ⟨1476603309958379489375045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 984402206638919659583363 1476603309958379489375045)
                    ·
                      refine ⟨276863120617196154257821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1476603309958379489375045 276863120617196154257821)
                      ·
                        rfl

theorem cell23_539189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_539189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_539189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_539189 prefixEnd_539189 := by exact prefixLift 539189
  have htrace : WordTrace (prefixWord ++ tailWord_539189) baseStart_539189 baseEnd_539189 := by
    simpa [prefixWord, tailWord_539189, baseEnd_539189] using wordTrace_append hprefix tailTrace_539189
  have hstable : (prefixWord ++ tailWord_539189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539189).length < 2 ^ (prefixWord ++ tailWord_539189).sum := by decide
  have hdescent : baseEnd_539189 < baseStart_539189 := by decide
  rcases family_descends (prefixWord ++ tailWord_539189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
