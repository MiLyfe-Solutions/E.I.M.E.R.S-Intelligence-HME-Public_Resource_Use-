import V185TrunkScan23Chunk0362

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2146947 : List Nat := [1, 1, 1, 3, 3, 1, 6, 2, 1, 2, 2]
def baseStart_2146947 : Nat := 118140960795 + 2146947 * 2 ^ 59
def prefixEnd_2146947 : Nat := 4983230072969 + 3 ^ 40 * 2146947 * 2
def baseEnd_2146947 : Nat := 1102415750728516793688877

theorem tailTrace_2146947 : CollatzResearch.WordTrace tailWord_2146947 prefixEnd_2146947 1102415750728516793688877 := by
  unfold tailWord_2146947
  simp only [CollatzResearch.WordTrace]
  refine ⟨78305590152985163200671095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52203726768656775467114063 78305590152985163200671095)
  ·
    refine ⟨117458385229477744801006643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78305590152985163200671095 117458385229477744801006643)
    ·
      refine ⟨176187577844216617201509965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117458385229477744801006643 176187577844216617201509965)
      ·
        refine ⟨66070341691581231450566237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176187577844216617201509965 66070341691581231450566237)
        ·
          refine ⟨24776378134342961793962339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66070341691581231450566237 24776378134342961793962339)
          ·
            refine ⟨37164567201514442690943509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24776378134342961793962339 37164567201514442690943509)
            ·
              refine ⟨1742089087570989501137977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37164567201514442690943509 1742089087570989501137977)
              ·
                refine ⟨1306566815678242125853483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1742089087570989501137977 1306566815678242125853483)
                ·
                  refine ⟨1959850223517363188780225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306566815678242125853483 1959850223517363188780225)
                  ·
                    refine ⟨1469887667638022391585169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1959850223517363188780225 1469887667638022391585169)
                    ·
                      refine ⟨1102415750728516793688877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1469887667638022391585169 1102415750728516793688877)
                      ·
                        rfl

theorem cell23_2146947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 1, 2, 2].length) (baseStart_2146947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146947 prefixEnd_2146947 := by exact prefixLift 2146947
  have htrace : WordTrace (prefixWord ++ tailWord_2146947) baseStart_2146947 baseEnd_2146947 := by
    simpa [prefixWord, tailWord_2146947, baseEnd_2146947] using wordTrace_append hprefix tailTrace_2146947
  have hstable : (prefixWord ++ tailWord_2146947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146947).length < 2 ^ (prefixWord ++ tailWord_2146947).sum := by decide
  have hdescent : baseEnd_2146947 < baseStart_2146947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146949 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_2146949 : Nat := 118140960795 + 2146949 * 2 ^ 59
def prefixEnd_2146949 : Nat := 4983230072969 + 3 ^ 40 * 2146949 * 2
def baseEnd_2146949 : Nat := 367472259229941928621289

theorem tailTrace_2146949 : CollatzResearch.WordTrace tailWord_2146949 prefixEnd_2146949 367472259229941928621289 := by
  unfold tailWord_2146949
  simp only [CollatzResearch.WordTrace]
  refine ⟨78305663098977917542243901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52203775399318611694829267 78305663098977917542243901)
  ·
    refine ⟨29364623662116719078341463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78305663098977917542243901 29364623662116719078341463)
    ·
      refine ⟨44046935493175078617512195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29364623662116719078341463 44046935493175078617512195)
      ·
        refine ⟨66070403239762617926268293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44046935493175078617512195 66070403239762617926268293)
        ·
          refine ⟨12388200607455490861175305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66070403239762617926268293 12388200607455490861175305)
          ·
            refine ⟨9291150455591618145881479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12388200607455490861175305 9291150455591618145881479)
            ·
              refine ⟨13936725683387427218822219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9291150455591618145881479 13936725683387427218822219)
              ·
                refine ⟨20905088525081140828233329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13936725683387427218822219 20905088525081140828233329)
                ·
                  refine ⟨15678816393810855621174997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20905088525081140828233329 15678816393810855621174997)
                  ·
                    refine ⟨367472259229941928621289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15678816393810855621174997 367472259229941928621289)
                    ·
                      rfl

theorem cell23_2146949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_2146949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146949 prefixEnd_2146949 := by exact prefixLift 2146949
  have htrace : WordTrace (prefixWord ++ tailWord_2146949) baseStart_2146949 baseEnd_2146949 := by
    simpa [prefixWord, tailWord_2146949, baseEnd_2146949] using wordTrace_append hprefix tailTrace_2146949
  have hstable : (prefixWord ++ tailWord_2146949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146949).length < 2 ^ (prefixWord ++ tailWord_2146949).sum := by decide
  have hdescent : baseEnd_2146949 < baseStart_2146949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146969 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_2146969 : Nat := 118140960795 + 2146969 * 2 ^ 59
def prefixEnd_2146969 : Nat := 4983230072969 + 3 ^ 40 * 2146969 * 2
def baseEnd_2146969 : Nat := 1102427047302915707613775

theorem tailTrace_2146969 : CollatzResearch.WordTrace tailWord_2146969 prefixEnd_2146969 1102427047302915707613775 := by
  unfold tailWord_2146969
  simp only [CollatzResearch.WordTrace]
  refine ⟨78306392558905460957971961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52204261705936973971981307 78306392558905460957971961)
  ·
    refine ⟨58729794419179095718478971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78306392558905460957971961 58729794419179095718478971)
    ·
      refine ⟨88094691628768643577718457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58729794419179095718478971 88094691628768643577718457)
      ·
        refine ⟨66071018721576482683288843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88094691628768643577718457 66071018721576482683288843)
        ·
          refine ⟨99106528082364724024933265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66071018721576482683288843 99106528082364724024933265)
          ·
            refine ⟨74329896061773543018699949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99106528082364724024933265 74329896061773543018699949)
            ·
              refine ⟨27873711023165078632012481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74329896061773543018699949 27873711023165078632012481)
              ·
                refine ⟨20905283267373808974009361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27873711023165078632012481 20905283267373808974009361)
                ·
                  refine ⟨15678962450530356730507021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20905283267373808974009361 15678962450530356730507021)
                  ·
                    refine ⟨5879610918948883773940133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15678962450530356730507021 5879610918948883773940133)
                    ·
                      refine ⟨1102427047302915707613775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5879610918948883773940133 1102427047302915707613775)
                      ·
                        rfl

theorem cell23_2146969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_2146969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146969 prefixEnd_2146969 := by exact prefixLift 2146969
  have htrace : WordTrace (prefixWord ++ tailWord_2146969) baseStart_2146969 baseEnd_2146969 := by
    simpa [prefixWord, tailWord_2146969, baseEnd_2146969] using wordTrace_append hprefix tailTrace_2146969
  have hstable : (prefixWord ++ tailWord_2146969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146969).length < 2 ^ (prefixWord ++ tailWord_2146969).sum := by decide
  have hdescent : baseEnd_2146969 < baseStart_2146969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146973 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_2146973 : Nat := 118140960795 + 2146973 * 2 ^ 59
def prefixEnd_2146973 : Nat := 4983230072969 + 3 ^ 40 * 2146973 * 2
def baseEnd_2146973 : Nat := 1102429101225533691963757

theorem tailTrace_2146973 : CollatzResearch.WordTrace tailWord_2146973 prefixEnd_2146973 1102429101225533691963757 := by
  unfold tailWord_2146973
  simp only [CollatzResearch.WordTrace]
  refine ⟨78306538450890969641117573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52204358967260646427411715 78306538450890969641117573)
  ·
    refine ⟨14682475959542056807709545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78306538450890969641117573 14682475959542056807709545)
    ·
      refine ⟨11011856969656542605782159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14682475959542056807709545 11011856969656542605782159)
      ·
        refine ⟨16517785454484813908673239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11011856969656542605782159 16517785454484813908673239)
        ·
          refine ⟨24776678181727220863009859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16517785454484813908673239 24776678181727220863009859)
          ·
            refine ⟨37165017272590831294514789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24776678181727220863009859 37165017272590831294514789)
            ·
              refine ⟨6968440738610780867721523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37165017272590831294514789 6968440738610780867721523)
              ·
                refine ⟨10452661107916171301582285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6968440738610780867721523 10452661107916171301582285)
                ·
                  refine ⟨3919747915468564238093357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10452661107916171301582285 3919747915468564238093357)
                  ·
                    refine ⟨1469905468300711589285009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3919747915468564238093357 1469905468300711589285009)
                    ·
                      refine ⟨1102429101225533691963757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1469905468300711589285009 1102429101225533691963757)
                      ·
                        rfl

theorem cell23_2146973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_2146973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146973 prefixEnd_2146973 := by exact prefixLift 2146973
  have htrace : WordTrace (prefixWord ++ tailWord_2146973) baseStart_2146973 baseEnd_2146973 := by
    simpa [prefixWord, tailWord_2146973, baseEnd_2146973] using wordTrace_append hprefix tailTrace_2146973
  have hstable : (prefixWord ++ tailWord_2146973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146973).length < 2 ^ (prefixWord ++ tailWord_2146973).sum := by decide
  have hdescent : baseEnd_2146973 < baseStart_2146973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146997 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2146997 : Nat := 118140960795 + 2146997 * 2 ^ 59
def prefixEnd_2146997 : Nat := 4983230072969 + 3 ^ 40 * 2146997 * 2
def baseEnd_2146997 : Nat := 1102441424761241598063647

theorem tailTrace_2146997 : CollatzResearch.WordTrace tailWord_2146997 prefixEnd_2146997 1102441424761241598063647 := by
  unfold tailWord_2146997
  simp only [CollatzResearch.WordTrace]
  refine ⟨78307413802804021739991245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52204942535202681159994163 78307413802804021739991245)
  ·
    refine ⟨29365280176051508152496717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78307413802804021739991245 29365280176051508152496717)
    ·
      refine ⟨11011980066019315557186269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29365280176051508152496717 11011980066019315557186269)
      ·
        refine ⟨4129492524757243333944851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11011980066019315557186269 4129492524757243333944851)
        ·
          refine ⟨6194238787135865000917277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4129492524757243333944851 6194238787135865000917277)
          ·
            refine ⟨2322839545175949375343979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6194238787135865000917277 2322839545175949375343979)
            ·
              refine ⟨3484259317763924063015969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2322839545175949375343979 3484259317763924063015969)
              ·
                refine ⟨2613194488322943047261977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3484259317763924063015969 2613194488322943047261977)
                ·
                  refine ⟨1959895866242207285446483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2613194488322943047261977 1959895866242207285446483)
                  ·
                    refine ⟨2939843799363310928169725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1959895866242207285446483 2939843799363310928169725)
                    ·
                      refine ⟨1102441424761241598063647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2939843799363310928169725 1102441424761241598063647)
                      ·
                        rfl

theorem cell23_2146997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2146997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146997 prefixEnd_2146997 := by exact prefixLift 2146997
  have htrace : WordTrace (prefixWord ++ tailWord_2146997) baseStart_2146997 baseEnd_2146997 := by
    simpa [prefixWord, tailWord_2146997, baseEnd_2146997] using wordTrace_append hprefix tailTrace_2146997
  have hstable : (prefixWord ++ tailWord_2146997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146997).length < 2 ^ (prefixWord ++ tailWord_2146997).sum := by decide
  have hdescent : baseEnd_2146997 < baseStart_2146997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147014 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2147014 : Nat := 118140960795 + 2147014 * 2 ^ 59
def prefixEnd_2147014 : Nat := 4983230072969 + 3 ^ 40 * 2147014 * 2
def baseEnd_2147014 : Nat := 1102450153932368031551069

theorem tailTrace_2147014 : CollatzResearch.WordTrace tailWord_2147014 prefixEnd_2147014 1102450153932368031551069 := by
  unfold tailWord_2147014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447126057616951051355003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52205355895828289095573397 2447126057616951051355003)
  ·
    refine ⟨3670689086425426577032505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2447126057616951051355003 3670689086425426577032505)
    ·
      refine ⟨2753016814819069932774379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3670689086425426577032505 2753016814819069932774379)
      ·
        refine ⟨4129525222228604899161569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753016814819069932774379 4129525222228604899161569)
        ·
          refine ⟨3097143916671453674371177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4129525222228604899161569 3097143916671453674371177)
          ·
            refine ⟨2322857937503590255778383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3097143916671453674371177 2322857937503590255778383)
            ·
              refine ⟨3484286906255385383667575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2322857937503590255778383 3484286906255385383667575)
              ·
                refine ⟨5226430359383078075501363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484286906255385383667575 5226430359383078075501363)
                ·
                  refine ⟨7839645539074617113252045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5226430359383078075501363 7839645539074617113252045)
                  ·
                    refine ⟨2939867077152981417469517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7839645539074617113252045 2939867077152981417469517)
                    ·
                      refine ⟨1102450153932368031551069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2939867077152981417469517 1102450153932368031551069)
                      ·
                        rfl

theorem cell23_2147014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2147014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147014 prefixEnd_2147014 := by exact prefixLift 2147014
  have htrace : WordTrace (prefixWord ++ tailWord_2147014) baseStart_2147014 baseEnd_2147014 := by
    simpa [prefixWord, tailWord_2147014, baseEnd_2147014] using wordTrace_append hprefix tailTrace_2147014
  have hstable : (prefixWord ++ tailWord_2147014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147014).length < 2 ^ (prefixWord ++ tailWord_2147014).sum := by decide
  have hdescent : baseEnd_2147014 < baseStart_2147014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147016 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_2147016 : Nat := 118140960795 + 2147016 * 2 ^ 59
def prefixEnd_2147016 : Nat := 4983230072969 + 3 ^ 40 * 2147016 * 2
def baseEnd_2147016 : Nat := 1102451180893677023726059

theorem tailTrace_2147016 : CollatzResearch.WordTrace tailWord_2147016 prefixEnd_2147016 1102451180893677023726059 := by
  unfold tailWord_2147016
  simp only [CollatzResearch.WordTrace]
  refine ⟨39154053394867593992466451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52205404526490125323288601 39154053394867593992466451)
  ·
    refine ⟨58731080092301390988699677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39154053394867593992466451 58731080092301390988699677)
    ·
      refine ⟨22024155034613021620762379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58731080092301390988699677 22024155034613021620762379)
      ·
        refine ⟨33036232551919532431143569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22024155034613021620762379 33036232551919532431143569)
        ·
          refine ⟨24777174413939649323357677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33036232551919532431143569 24777174413939649323357677)
          ·
            refine ⟨9291440405227368496259129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24777174413939649323357677 9291440405227368496259129)
            ·
              refine ⟨6968580303920526372194347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9291440405227368496259129 6968580303920526372194347)
              ·
                refine ⟨10452870455880789558291521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6968580303920526372194347 10452870455880789558291521)
                ·
                  refine ⟨7839652841910592168718641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10452870455880789558291521 7839652841910592168718641)
                  ·
                    refine ⟨5879739631432944126538981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7839652841910592168718641 5879739631432944126538981)
                    ·
                      refine ⟨1102451180893677023726059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5879739631432944126538981 1102451180893677023726059)
                      ·
                        rfl

theorem cell23_2147016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_2147016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147016 prefixEnd_2147016 := by exact prefixLift 2147016
  have htrace : WordTrace (prefixWord ++ tailWord_2147016) baseStart_2147016 baseEnd_2147016 := by
    simpa [prefixWord, tailWord_2147016, baseEnd_2147016] using wordTrace_append hprefix tailTrace_2147016
  have hstable : (prefixWord ++ tailWord_2147016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147016).length < 2 ^ (prefixWord ++ tailWord_2147016).sum := by decide
  have hdescent : baseEnd_2147016 < baseStart_2147016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147020 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2147020 : Nat := 118140960795 + 2147020 * 2 ^ 59
def prefixEnd_2147020 : Nat := 4983230072969 + 3 ^ 40 * 2147020 * 2
def baseEnd_2147020 : Nat := 1102453234816295008076041

theorem tailTrace_2147020 : CollatzResearch.WordTrace tailWord_2147020 prefixEnd_2147020 1102453234816295008076041 := by
  unfold tailWord_2147020
  simp only [CollatzResearch.WordTrace]
  refine ⟨39154126340860348334039257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52205501787813797778719009 39154126340860348334039257)
  ·
    refine ⟨29365594755645261250529443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39154126340860348334039257 29365594755645261250529443)
    ·
      refine ⟨44048392133467891875794165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29365594755645261250529443 44048392133467891875794165)
      ·
        refine ⟨4129536762512614863355703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44048392133467891875794165 4129536762512614863355703)
        ·
          refine ⟨6194305143768922295033555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4129536762512614863355703 6194305143768922295033555)
          ·
            refine ⟨9291457715653383442550333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6194305143768922295033555 9291457715653383442550333)
            ·
              refine ⟨3484296643370018790956375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9291457715653383442550333 3484296643370018790956375)
              ·
                refine ⟨5226444965055028186434563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484296643370018790956375 5226444965055028186434563)
                ·
                  refine ⟨7839667447582542279651845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5226444965055028186434563 7839667447582542279651845)
                  ·
                    refine ⟨1469937646421726677434721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7839667447582542279651845 1469937646421726677434721)
                    ·
                      refine ⟨1102453234816295008076041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1469937646421726677434721 1102453234816295008076041)
                      ·
                        rfl

theorem cell23_2147020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2147020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147020 prefixEnd_2147020 := by exact prefixLift 2147020
  have htrace : WordTrace (prefixWord ++ tailWord_2147020) baseStart_2147020 baseEnd_2147020 := by
    simpa [prefixWord, tailWord_2147020, baseEnd_2147020] using wordTrace_append hprefix tailTrace_2147020
  have hstable : (prefixWord ++ tailWord_2147020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147020).length < 2 ^ (prefixWord ++ tailWord_2147020).sum := by decide
  have hdescent : baseEnd_2147020 < baseStart_2147020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147056 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 2, 5]
def baseStart_2147056 : Nat := 118140960795 + 2147056 * 2 ^ 59
def prefixEnd_2147056 : Nat := 4983230072969 + 3 ^ 40 * 2147056 * 2
def baseEnd_2147056 : Nat := 367490573373285622408625

theorem tailTrace_2147056 : CollatzResearch.WordTrace tailWord_2147056 prefixEnd_2147056 367490573373285622408625 := by
  unfold tailWord_2147056
  simp only [CollatzResearch.WordTrace]
  refine ⟨39154782854795137408194511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52206377139726849877592681 39154782854795137408194511)
  ·
    refine ⟨58732174282192706112291767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39154782854795137408194511 58732174282192706112291767)
    ·
      refine ⟨88098261423289059168437651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58732174282192706112291767 88098261423289059168437651)
      ·
        refine ⟨132147392134933588752656477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88098261423289059168437651 132147392134933588752656477)
        ·
          refine ⟨49555272050600095782246179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132147392134933588752656477 49555272050600095782246179)
          ·
            refine ⟨74332908075900143673369269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49555272050600095782246179 74332908075900143673369269)
            ·
              refine ⟨6968710132115638469378369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74332908075900143673369269 6968710132115638469378369)
              ·
                refine ⟨5226532599086728852033777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6968710132115638469378369 5226532599086728852033777)
                ·
                  refine ⟨3919899449315046639025333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5226532599086728852033777 3919899449315046639025333)
                  ·
                    refine ⟨367490573373285622408625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3919899449315046639025333 367490573373285622408625)
                    ·
                      rfl

theorem cell23_2147056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_2147056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147056 prefixEnd_2147056 := by exact prefixLift 2147056
  have htrace : WordTrace (prefixWord ++ tailWord_2147056) baseStart_2147056 baseEnd_2147056 := by
    simpa [prefixWord, tailWord_2147056, baseEnd_2147056] using wordTrace_append hprefix tailTrace_2147056
  have hstable : (prefixWord ++ tailWord_2147056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147056).length < 2 ^ (prefixWord ++ tailWord_2147056).sum := by decide
  have hdescent : baseEnd_2147056 < baseStart_2147056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147093 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_2147093 : Nat := 118140960795 + 2147093 * 2 ^ 59
def prefixEnd_2147093 : Nat := 4983230072969 + 3 ^ 40 * 2147093 * 2
def baseEnd_2147093 : Nat := 1102490718904073222463205

theorem tailTrace_2147093 : CollatzResearch.WordTrace tailWord_2147093 prefixEnd_2147093 1102490718904073222463205 := by
  unfold tailWord_2147093
  simp only [CollatzResearch.WordTrace]
  refine ⟨78310915210456230135485933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52207276806970820090323955 78310915210456230135485933)
  ·
    refine ⟨29366593203921086300807225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78310915210456230135485933 29366593203921086300807225)
    ·
      refine ⟨22024944902940814725605419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29366593203921086300807225 22024944902940814725605419)
      ·
        refine ⟨33037417354411222088408129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22024944902940814725605419 33037417354411222088408129)
        ·
          refine ⟨24778063015808416566306097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33037417354411222088408129 24778063015808416566306097)
          ·
            refine ⟨18583547261856312424729573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24778063015808416566306097 18583547261856312424729573)
            ·
              refine ⟨3484415111598058579636795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18583547261856312424729573 3484415111598058579636795)
              ·
                refine ⟨5226622667397087869455193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484415111598058579636795 5226622667397087869455193)
                ·
                  refine ⟨3919967000547815902091395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5226622667397087869455193 3919967000547815902091395)
                  ·
                    refine ⟨5879950500821723853137093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3919967000547815902091395 5879950500821723853137093)
                    ·
                      refine ⟨1102490718904073222463205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5879950500821723853137093 1102490718904073222463205)
                      ·
                        rfl

theorem cell23_2147093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_2147093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147093 prefixEnd_2147093 := by exact prefixLift 2147093
  have htrace : WordTrace (prefixWord ++ tailWord_2147093) baseStart_2147093 baseEnd_2147093 := by
    simpa [prefixWord, tailWord_2147093, baseEnd_2147093] using wordTrace_append hprefix tailTrace_2147093
  have hstable : (prefixWord ++ tailWord_2147093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147093).length < 2 ^ (prefixWord ++ tailWord_2147093).sum := by decide
  have hdescent : baseEnd_2147093 < baseStart_2147093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147137 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2147137 : Nat := 118140960795 + 2147137 * 2 ^ 59
def prefixEnd_2147137 : Nat := 4983230072969 + 3 ^ 40 * 2147137 * 2
def baseEnd_2147137 : Nat := 367504437350957016771001

theorem tailTrace_2147137 : CollatzResearch.WordTrace tailWord_2147137 prefixEnd_2147137 367504437350957016771001 := by
  unfold tailWord_2147137
  simp only [CollatzResearch.WordTrace]
  refine ⟨78312520022296825650087665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52208346681531217100058443 78312520022296825650087665)
  ·
    refine ⟨58734390016722619237565749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78312520022296825650087665 58734390016722619237565749)
    ·
      refine ⟨5506349064067745553521789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58734390016722619237565749 5506349064067745553521789)
      ·
        refine ⟨2064880899025404582570671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5506349064067745553521789 2064880899025404582570671)
        ·
          refine ⟨3097321348538106873856007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2064880899025404582570671 3097321348538106873856007)
          ·
            refine ⟨4645982022807160310784011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097321348538106873856007 4645982022807160310784011)
            ·
              refine ⟨6968973034210740466176017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4645982022807160310784011 6968973034210740466176017)
              ·
                refine ⟨5226729775658055349632013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6968973034210740466176017 5226729775658055349632013)
                ·
                  refine ⟨1960023665871770756112005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5226729775658055349632013 1960023665871770756112005)
                  ·
                    refine ⟨367504437350957016771001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1960023665871770756112005 367504437350957016771001)
                    ·
                      rfl

theorem cell23_2147137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2147137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147137 prefixEnd_2147137 := by exact prefixLift 2147137
  have htrace : WordTrace (prefixWord ++ tailWord_2147137) baseStart_2147137 baseEnd_2147137 := by
    simpa [prefixWord, tailWord_2147137, baseEnd_2147137] using wordTrace_append hprefix tailTrace_2147137
  have hstable : (prefixWord ++ tailWord_2147137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147137).length < 2 ^ (prefixWord ++ tailWord_2147137).sum := by decide
  have hdescent : baseEnd_2147137 < baseStart_2147137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147193 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 1, 6]
def baseStart_2147193 : Nat := 118140960795 + 2147193 * 2 ^ 59
def prefixEnd_2147193 : Nat := 4983230072969 + 3 ^ 40 * 2147193 * 2
def baseEnd_2147193 : Nat := 367514022323174277070915

theorem tailTrace_2147193 : CollatzResearch.WordTrace tailWord_2147193 prefixEnd_2147193 367514022323174277070915 := by
  unfold tailWord_2147193
  simp only [CollatzResearch.WordTrace]
  refine ⟨78314562510093947214126233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52209708340062631476084155 78314562510093947214126233)
  ·
    refine ⟨58735921882570460410594675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78314562510093947214126233 58735921882570460410594675)
    ·
      refine ⟨88103882823855690615892013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58735921882570460410594675 88103882823855690615892013)
      ·
        refine ⟨33038956058945883980959505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88103882823855690615892013 33038956058945883980959505)
        ·
          refine ⟨24779217044209412985719629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33038956058945883980959505 24779217044209412985719629)
          ·
            refine ⟨9292206391578529869644861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24779217044209412985719629 9292206391578529869644861)
            ·
              refine ⟨3484577396841948701116823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9292206391578529869644861 3484577396841948701116823)
              ·
                refine ⟨5226866095262923051675235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484577396841948701116823 5226866095262923051675235)
                ·
                  refine ⟨7840299142894384577512853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5226866095262923051675235 7840299142894384577512853)
                  ·
                    refine ⟨367514022323174277070915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7840299142894384577512853 367514022323174277070915)
                    ·
                      rfl

theorem cell23_2147193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 6].length) (baseStart_2147193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147193 prefixEnd_2147193 := by exact prefixLift 2147193
  have htrace : WordTrace (prefixWord ++ tailWord_2147193) baseStart_2147193 baseEnd_2147193 := by
    simpa [prefixWord, tailWord_2147193, baseEnd_2147193] using wordTrace_append hprefix tailTrace_2147193
  have hstable : (prefixWord ++ tailWord_2147193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147193).length < 2 ^ (prefixWord ++ tailWord_2147193).sum := by decide
  have hdescent : baseEnd_2147193 < baseStart_2147193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147200 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 5, 2, 2]
def baseStart_2147200 : Nat := 118140960795 + 2147200 * 2 ^ 59
def prefixEnd_2147200 : Nat := 4983230072969 + 3 ^ 40 * 2147200 * 2
def baseEnd_2147200 : Nat := 1102545661334104303825213

theorem tailTrace_2147200 : CollatzResearch.WordTrace tailWord_2147200 prefixEnd_2147200 1102545661334104303825213 := by
  unfold tailWord_2147200
  simp only [CollatzResearch.WordTrace]
  refine ⟨39157408910534293704815527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52209878547379058273087369 39157408910534293704815527)
  ·
    refine ⟨58736113365801440557223291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39157408910534293704815527 58736113365801440557223291)
    ·
      refine ⟨88104170048702160835834937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58736113365801440557223291 88104170048702160835834937)
      ·
        refine ⟨66078127536526620626876203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88104170048702160835834937 66078127536526620626876203)
        ·
          refine ⟨99117191304789930940314305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66078127536526620626876203 99117191304789930940314305)
          ·
            refine ⟨74337893478592448205235729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99117191304789930940314305 74337893478592448205235729)
            ·
              refine ⟨55753420108944336153926797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74337893478592448205235729 55753420108944336153926797)
              ·
                refine ⟨20907532540854126057722549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55753420108944336153926797 20907532540854126057722549)
                ·
                  refine ⟨1960081175705074317911489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20907532540854126057722549 1960081175705074317911489)
                  ·
                    refine ⟨1470060881778805738433617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1960081175705074317911489 1470060881778805738433617)
                    ·
                      refine ⟨1102545661334104303825213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470060881778805738433617 1102545661334104303825213)
                      ·
                        rfl

theorem cell23_2147200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_2147200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147200 prefixEnd_2147200 := by exact prefixLift 2147200
  have htrace : WordTrace (prefixWord ++ tailWord_2147200) baseStart_2147200 baseEnd_2147200 := by
    simpa [prefixWord, tailWord_2147200, baseEnd_2147200] using wordTrace_append hprefix tailTrace_2147200
  have hstable : (prefixWord ++ tailWord_2147200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147200).length < 2 ^ (prefixWord ++ tailWord_2147200).sum := by decide
  have hdescent : baseEnd_2147200 < baseStart_2147200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147210 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_2147210 : Nat := 118140960795 + 2147210 * 2 ^ 59
def prefixEnd_2147210 : Nat := 4983230072969 + 3 ^ 40 * 2147210 * 2
def baseEnd_2147210 : Nat := 367516932046883088233389

theorem tailTrace_2147210 : CollatzResearch.WordTrace tailWord_2147210 prefixEnd_2147210 367516932046883088233389 := by
  unfold tailWord_2147210
  simp only [CollatzResearch.WordTrace]
  refine ⟨19578795637758089779373771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52210121700688239411663389 19578795637758089779373771)
  ·
    refine ⟨29368193456637134669060657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19578795637758089779373771 29368193456637134669060657)
    ·
      refine ⟨22026145092477851001795493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29368193456637134669060657 22026145092477851001795493)
      ·
        refine ⟨4129902204839597062836655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22026145092477851001795493 4129902204839597062836655)
        ·
          refine ⟨6194853307259395594254983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4129902204839597062836655 6194853307259395594254983)
          ·
            refine ⟨9292279960889093391382475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6194853307259395594254983 9292279960889093391382475)
            ·
              refine ⟨13938419941333640087073713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9292279960889093391382475 13938419941333640087073713)
              ·
                refine ⟨10453814956000230065305285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13938419941333640087073713 10453814956000230065305285)
                ·
                  refine ⟨1960090304250043137244741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10453814956000230065305285 1960090304250043137244741)
                  ·
                    refine ⟨367516932046883088233389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1960090304250043137244741 367516932046883088233389)
                    ·
                      rfl

theorem cell23_2147210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_2147210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147210 prefixEnd_2147210 := by exact prefixLift 2147210
  have htrace : WordTrace (prefixWord ++ tailWord_2147210) baseStart_2147210 baseEnd_2147210 := by
    simpa [prefixWord, tailWord_2147210, baseEnd_2147210] using wordTrace_append hprefix tailTrace_2147210
  have hstable : (prefixWord ++ tailWord_2147210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147210).length < 2 ^ (prefixWord ++ tailWord_2147210).sum := by decide
  have hdescent : baseEnd_2147210 < baseStart_2147210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147220 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_2147220 : Nat := 118140960795 + 2147220 * 2 ^ 59
def prefixEnd_2147220 : Nat := 4983230072969 + 3 ^ 40 * 2147220 * 2
def baseEnd_2147220 : Nat := 1102555930947194225575121

theorem tailTrace_2147220 : CollatzResearch.WordTrace tailWord_2147220 prefixEnd_2147220 1102555930947194225575121 := by
  unfold tailWord_2147220
  simp only [CollatzResearch.WordTrace]
  refine ⟨39157773640498065412679557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52210364853997420550239409 39157773640498065412679557)
  ·
    refine ⟨7342082557593387264877417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39157773640498065412679557 7342082557593387264877417)
    ·
      refine ⟨5506561918195040448658063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7342082557593387264877417 5506561918195040448658063)
      ·
        refine ⟨8259842877292560672987095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5506561918195040448658063 8259842877292560672987095)
        ·
          refine ⟨12389764315938841009480643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8259842877292560672987095 12389764315938841009480643)
          ·
            refine ⟨18584646473908261514220965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12389764315938841009480643 18584646473908261514220965)
            ·
              refine ⟨3484621213857799033916431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18584646473908261514220965 3484621213857799033916431)
              ·
                refine ⟨5226931820786698550874647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484621213857799033916431 5226931820786698550874647)
                ·
                  refine ⟨7840397731180047826311971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5226931820786698550874647 7840397731180047826311971)
                  ·
                    refine ⟨11760596596770071739467957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7840397731180047826311971 11760596596770071739467957)
                    ·
                      refine ⟨1102555930947194225575121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11760596596770071739467957 1102555930947194225575121)
                      ·
                        rfl

theorem cell23_2147220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_2147220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147220 prefixEnd_2147220 := by exact prefixLift 2147220
  have htrace : WordTrace (prefixWord ++ tailWord_2147220) baseStart_2147220 baseEnd_2147220 := by
    simpa [prefixWord, tailWord_2147220, baseEnd_2147220] using wordTrace_append hprefix tailTrace_2147220
  have hstable : (prefixWord ++ tailWord_2147220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147220).length < 2 ^ (prefixWord ++ tailWord_2147220).sum := by decide
  have hdescent : baseEnd_2147220 < baseStart_2147220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147234 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_2147234 : Nat := 118140960795 + 2147234 * 2 ^ 59
def prefixEnd_2147234 : Nat := 4983230072969 + 3 ^ 40 * 2147234 * 2
def baseEnd_2147234 : Nat := 1102563119676357170800057

theorem tailTrace_2147234 : CollatzResearch.WordTrace tailWord_2147234 prefixEnd_2147234 1102563119676357170800057 := by
  unfold tailWord_2147234
  simp only [CollatzResearch.WordTrace]
  refine ⟨19579014475736352804092189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52210705268630274144245837 19579014475736352804092189)
  ·
    refine ⟨7342130428401132301534571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19579014475736352804092189 7342130428401132301534571)
    ·
      refine ⟨11013195642601698452301857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7342130428401132301534571 11013195642601698452301857)
      ·
        refine ⟨8259896731951273839226393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11013195642601698452301857 8259896731951273839226393)
        ·
          refine ⟨6194922548963455379419795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8259896731951273839226393 6194922548963455379419795)
          ·
            refine ⟨9292383823445183069129693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6194922548963455379419795 9292383823445183069129693)
            ·
              refine ⟨3484643933791943650923635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9292383823445183069129693 3484643933791943650923635)
              ·
                refine ⟨5226965900687915476385453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484643933791943650923635 5226965900687915476385453)
                ·
                  refine ⟨1960112212757968303644545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5226965900687915476385453 1960112212757968303644545)
                  ·
                    refine ⟨1470084159568476227733409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1960112212757968303644545 1470084159568476227733409)
                    ·
                      refine ⟨1102563119676357170800057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470084159568476227733409 1102563119676357170800057)
                      ·
                        rfl

theorem cell23_2147234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_2147234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147234 prefixEnd_2147234 := by exact prefixLift 2147234
  have htrace : WordTrace (prefixWord ++ tailWord_2147234) baseStart_2147234 baseEnd_2147234 := by
    simpa [prefixWord, tailWord_2147234, baseEnd_2147234] using wordTrace_append hprefix tailTrace_2147234
  have hstable : (prefixWord ++ tailWord_2147234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147234).length < 2 ^ (prefixWord ++ tailWord_2147234).sum := by decide
  have hdescent : baseEnd_2147234 < baseStart_2147234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147284 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2147284 : Nat := 118140960795 + 2147284 * 2 ^ 59
def prefixEnd_2147284 : Nat := 4983230072969 + 3 ^ 40 * 2147284 * 2
def baseEnd_2147284 : Nat := 1102588793709081975174827

theorem tailTrace_2147284 : CollatzResearch.WordTrace tailWord_2147284 prefixEnd_2147284 1102588793709081975174827 := by
  unfold tailWord_2147284
  simp only [CollatzResearch.WordTrace]
  refine ⟨39158940776382134877844453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52211921035176179837125937 39158940776382134877844453)
  ·
    refine ⟨7342301395571650289595835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39158940776382134877844453 7342301395571650289595835)
    ·
      refine ⟨11013452093357475434393753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7342301395571650289595835 11013452093357475434393753)
      ·
        refine ⟨8260089070018106575795315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11013452093357475434393753 8260089070018106575795315)
        ·
          refine ⟨12390133605027159863692973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8260089070018106575795315 12390133605027159863692973)
          ·
            refine ⟨4646300101885184948884865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12390133605027159863692973 4646300101885184948884865)
            ·
              refine ⟨3484725076413888711663649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4646300101885184948884865 3484725076413888711663649)
              ·
                refine ⟨2613543807310416533747737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3484725076413888711663649 2613543807310416533747737)
                ·
                  refine ⟨1960157855482812400310803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2613543807310416533747737 1960157855482812400310803)
                  ·
                    refine ⟨2940236783224218600466205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1960157855482812400310803 2940236783224218600466205)
                    ·
                      refine ⟨1102588793709081975174827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2940236783224218600466205 1102588793709081975174827)
                      ·
                        rfl

theorem cell23_2147284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2147284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147284 prefixEnd_2147284 := by exact prefixLift 2147284
  have htrace : WordTrace (prefixWord ++ tailWord_2147284) baseStart_2147284 baseEnd_2147284 := by
    simpa [prefixWord, tailWord_2147284, baseEnd_2147284] using wordTrace_append hprefix tailTrace_2147284
  have hstable : (prefixWord ++ tailWord_2147284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147284).length < 2 ^ (prefixWord ++ tailWord_2147284).sum := by decide
  have hdescent : baseEnd_2147284 < baseStart_2147284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147285 : List Nat := [1, 3, 2, 3, 4, 1, 2, 2, 1, 2, 2]
def baseStart_2147285 : Nat := 118140960795 + 2147285 * 2 ^ 59
def prefixEnd_2147285 : Nat := 4983230072969 + 3 ^ 40 * 2147285 * 2
def baseEnd_2147285 : Nat := 1102589307189736471262323

theorem tailTrace_2147285 : CollatzResearch.WordTrace tailWord_2147285 prefixEnd_2147285 1102589307189736471262323 := by
  unfold tailWord_2147285
  simp only [CollatzResearch.WordTrace]
  refine ⟨78317918025760646926475309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52211945350507097950983539 78317918025760646926475309)
  ·
    refine ⟨29369219259660242597428241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78317918025760646926475309 29369219259660242597428241)
    ·
      refine ⟨22026914444745181948071181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29369219259660242597428241 22026914444745181948071181)
      ·
        refine ⟨8260092916779443230526693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22026914444745181948071181 8260092916779443230526693)
        ·
          refine ⟨1548767421896145605723755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8260092916779443230526693 1548767421896145605723755)
          ·
            refine ⟨2323151132844218408585633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548767421896145605723755 2323151132844218408585633)
            ·
              refine ⟨1742363349633163806439225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323151132844218408585633 1742363349633163806439225)
              ·
                refine ⟨1306772512224872854829419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1742363349633163806439225 1306772512224872854829419)
                ·
                  refine ⟨1960158768337309282244129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306772512224872854829419 1960158768337309282244129)
                  ·
                    refine ⟨1470119076252981961683097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1960158768337309282244129 1470119076252981961683097)
                    ·
                      refine ⟨1102589307189736471262323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470119076252981961683097 1102589307189736471262323)
                      ·
                        rfl

theorem cell23_2147285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_2147285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147285 prefixEnd_2147285 := by exact prefixLift 2147285
  have htrace : WordTrace (prefixWord ++ tailWord_2147285) baseStart_2147285 baseEnd_2147285 := by
    simpa [prefixWord, tailWord_2147285, baseEnd_2147285] using wordTrace_append hprefix tailTrace_2147285
  have hstable : (prefixWord ++ tailWord_2147285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147285).length < 2 ^ (prefixWord ++ tailWord_2147285).sum := by decide
  have hdescent : baseEnd_2147285 < baseStart_2147285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147313 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 9]
def baseStart_2147313 : Nat := 118140960795 + 2147313 * 2 ^ 59
def prefixEnd_2147313 : Nat := 4983230072969 + 3 ^ 40 * 2147313 * 2
def baseEnd_2147313 : Nat := 122511520516451373523577

theorem tailTrace_2147313 : CollatzResearch.WordTrace tailWord_2147313 prefixEnd_2147313 122511520516451373523577 := by
  unfold tailWord_2147313
  simp only [CollatzResearch.WordTrace]
  refine ⟨78318939269659207708494593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52212626179772805138996395 78318939269659207708494593)
  ·
    refine ⟨58739204452244405781370945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78318939269659207708494593 58739204452244405781370945)
    ·
      refine ⟨44054403339183304336028209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58739204452244405781370945 44054403339183304336028209)
      ·
        refine ⟨33040802504387478252021157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44054403339183304336028209 33040802504387478252021157)
        ·
          refine ⟨6195150469572652172253967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33040802504387478252021157 6195150469572652172253967)
          ·
            refine ⟨9292725704358978258380951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6195150469572652172253967 9292725704358978258380951)
            ·
              refine ⟨13939088556538467387571427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9292725704358978258380951 13939088556538467387571427)
              ·
                refine ⟨20908632834807701081357141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13939088556538467387571427 20908632834807701081357141)
                ·
                  refine ⟨122511520516451373523577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20908632834807701081357141 122511520516451373523577)
                  ·
                    rfl

theorem cell23_2147313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 9].length) (baseStart_2147313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147313 prefixEnd_2147313 := by exact prefixLift 2147313
  have htrace : WordTrace (prefixWord ++ tailWord_2147313) baseStart_2147313 baseEnd_2147313 := by
    simpa [prefixWord, tailWord_2147313, baseEnd_2147313] using wordTrace_append hprefix tailTrace_2147313
  have hstable : (prefixWord ++ tailWord_2147313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147313).length < 2 ^ (prefixWord ++ tailWord_2147313).sum := by decide
  have hdescent : baseEnd_2147313 < baseStart_2147313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147323 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 3]
def baseStart_2147323 : Nat := 118140960795 + 2147323 * 2 ^ 59
def prefixEnd_2147323 : Nat := 4983230072969 + 3 ^ 40 * 2147323 * 2
def baseEnd_2147323 : Nat := 1102608819454607322587147

theorem tailTrace_2147323 : CollatzResearch.WordTrace tailWord_2147323 prefixEnd_2147323 1102608819454607322587147 := by
  unfold tailWord_2147323
  simp only [CollatzResearch.WordTrace]
  refine ⟨78319303999622979416358623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52212869333081986277572415 78319303999622979416358623)
  ·
    refine ⟨117478955999434469124537935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78319303999622979416358623 117478955999434469124537935)
    ·
      refine ⟨176218433999151703686806903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117478955999434469124537935 176218433999151703686806903)
      ·
        refine ⟨264327650998727555530210355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176218433999151703686806903 264327650998727555530210355)
        ·
          refine ⟨396491476498091333295315533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264327650998727555530210355 396491476498091333295315533)
          ·
            refine ⟨148684303686784249985743325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396491476498091333295315533 148684303686784249985743325)
            ·
              refine ⟨55756613882544093744653747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148684303686784249985743325 55756613882544093744653747)
              ·
                refine ⟨83634920823816140616980621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55756613882544093744653747 83634920823816140616980621)
                ·
                  refine ⟨31363095308931052731367733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83634920823816140616980621 31363095308931052731367733)
                  ·
                    refine ⟨2940290185212286193565725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31363095308931052731367733 2940290185212286193565725)
                    ·
                      refine ⟨1102608819454607322587147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2940290185212286193565725 1102608819454607322587147)
                      ·
                        rfl

theorem cell23_2147323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 3].length) (baseStart_2147323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147323 prefixEnd_2147323 := by exact prefixLift 2147323
  have htrace : WordTrace (prefixWord ++ tailWord_2147323) baseStart_2147323 baseEnd_2147323 := by
    simpa [prefixWord, tailWord_2147323, baseEnd_2147323] using wordTrace_append hprefix tailTrace_2147323
  have hstable : (prefixWord ++ tailWord_2147323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147323).length < 2 ^ (prefixWord ++ tailWord_2147323).sum := by decide
  have hdescent : baseEnd_2147323 < baseStart_2147323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147340 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 2, 3, 3]
def baseStart_2147340 : Nat := 118140960795 + 2147340 * 2 ^ 59
def prefixEnd_2147340 : Nat := 4983230072969 + 3 ^ 40 * 2147340 * 2
def baseEnd_2147340 : Nat := 1102617548625733756074569

theorem tailTrace_2147340 : CollatzResearch.WordTrace tailWord_2147340 prefixEnd_2147340 1102617548625733756074569 := by
  unfold tailWord_2147340
  simp only [CollatzResearch.WordTrace]
  refine ⟨39159962020280695659863737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52213282693707594213151649 39159962020280695659863737)
  ·
    refine ⟨29369971515210521744897803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39159962020280695659863737 29369971515210521744897803)
    ·
      refine ⟨44054957272815782617346705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29369971515210521744897803 44054957272815782617346705)
      ·
        refine ⟨33041217954611836963010029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44054957272815782617346705 33041217954611836963010029)
        ·
          refine ⟨12390456732979438861128761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33041217954611836963010029 12390456732979438861128761)
          ·
            refine ⟨9292842549734579145846571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12390456732979438861128761 9292842549734579145846571)
            ·
              refine ⟨13939263824601868718769857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9292842549734579145846571 13939263824601868718769857)
              ·
                refine ⟨10454447868451401539077393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13939263824601868718769857 10454447868451401539077393)
                ·
                  refine ⟨7840835901338551154308045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10454447868451401539077393 7840835901338551154308045)
                  ·
                    refine ⟨2940313463001956682865517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7840835901338551154308045 2940313463001956682865517)
                    ·
                      refine ⟨1102617548625733756074569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2940313463001956682865517 1102617548625733756074569)
                      ·
                        rfl

theorem cell23_2147340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_2147340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147340 prefixEnd_2147340 := by exact prefixLift 2147340
  have htrace : WordTrace (prefixWord ++ tailWord_2147340) baseStart_2147340 baseEnd_2147340 := by
    simpa [prefixWord, tailWord_2147340, baseEnd_2147340] using wordTrace_append hprefix tailTrace_2147340
  have hstable : (prefixWord ++ tailWord_2147340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147340).length < 2 ^ (prefixWord ++ tailWord_2147340).sum := by decide
  have hdescent : baseEnd_2147340 < baseStart_2147340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147353 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_2147353 : Nat := 118140960795 + 2147353 * 2 ^ 59
def prefixEnd_2147353 : Nat := 4983230072969 + 3 ^ 40 * 2147353 * 2
def baseEnd_2147353 : Nat := 1102624223874242205212009

theorem tailTrace_2147353 : CollatzResearch.WordTrace tailWord_2147353 prefixEnd_2147353 1102624223874242205212009 := by
  unfold tailWord_2147353
  simp only [CollatzResearch.WordTrace]
  refine ⟨78320398189514294539950713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52213598793009529693300475 78320398189514294539950713)
  ·
    refine ⟨58740298642135720904963035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78320398189514294539950713 58740298642135720904963035)
    ·
      refine ⟨88110447963203581357444553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58740298642135720904963035 88110447963203581357444553)
      ·
        refine ⟨66082835972402686018083415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88110447963203581357444553 66082835972402686018083415)
        ·
          refine ⟨99124253958604029027125123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66082835972402686018083415 99124253958604029027125123)
          ·
            refine ⟨148686380937906043540687685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99124253958604029027125123 148686380937906043540687685)
            ·
              refine ⟨27878696425857383163878941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148686380937906043540687685 27878696425857383163878941)
              ·
                refine ⟨10454511159696518686454603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27878696425857383163878941 10454511159696518686454603)
                ·
                  refine ⟨15681766739544778029681905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10454511159696518686454603 15681766739544778029681905)
                  ·
                    refine ⟨11761325054658583522261429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15681766739544778029681905 11761325054658583522261429)
                    ·
                      refine ⟨1102624223874242205212009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11761325054658583522261429 1102624223874242205212009)
                      ·
                        rfl

theorem cell23_2147353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_2147353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147353 prefixEnd_2147353 := by exact prefixLift 2147353
  have htrace : WordTrace (prefixWord ++ tailWord_2147353) baseStart_2147353 baseEnd_2147353 := by
    simpa [prefixWord, tailWord_2147353, baseEnd_2147353] using wordTrace_append hprefix tailTrace_2147353
  have hstable : (prefixWord ++ tailWord_2147353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147353).length < 2 ^ (prefixWord ++ tailWord_2147353).sum := by decide
  have hdescent : baseEnd_2147353 < baseStart_2147353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147383 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_2147383 : Nat := 118140960795 + 2147383 * 2 ^ 59
def prefixEnd_2147383 : Nat := 4983230072969 + 3 ^ 40 * 2147383 * 2
def baseEnd_2147383 : Nat := 1102639628293877087836871

theorem tailTrace_2147383 : CollatzResearch.WordTrace tailWord_2147383 prefixEnd_2147383 1102639628293877087836871 := by
  unfold tailWord_2147383
  simp only [CollatzResearch.WordTrace]
  refine ⟨78321492379405609663542803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52214328252937073109028535 78321492379405609663542803)
  ·
    refine ⟨117482238569108414495314205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78321492379405609663542803 117482238569108414495314205)
    ·
      refine ⟨44055839463415655435742827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117482238569108414495314205 44055839463415655435742827)
      ·
        refine ⟨66083759195123483153614241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44055839463415655435742827 66083759195123483153614241)
        ·
          refine ⟨49562819396342612365210681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66083759195123483153614241 49562819396342612365210681)
          ·
            refine ⟨37172114547256959273908011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49562819396342612365210681 37172114547256959273908011)
            ·
              refine ⟨55758171820885438910862017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37172114547256959273908011 55758171820885438910862017)
              ·
                refine ⟨41818628865664079183146513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55758171820885438910862017 41818628865664079183146513)
                ·
                  refine ⟨31363971649248059387359885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41818628865664079183146513 31363971649248059387359885)
                  ·
                    refine ⟨11761489368468022270259957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31363971649248059387359885 11761489368468022270259957)
                    ·
                      refine ⟨1102639628293877087836871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11761489368468022270259957 1102639628293877087836871)
                      ·
                        rfl

theorem cell23_2147383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_2147383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147383 prefixEnd_2147383 := by exact prefixLift 2147383
  have htrace : WordTrace (prefixWord ++ tailWord_2147383) baseStart_2147383 baseEnd_2147383 := by
    simpa [prefixWord, tailWord_2147383, baseEnd_2147383] using wordTrace_append hprefix tailTrace_2147383
  have hstable : (prefixWord ++ tailWord_2147383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147383).length < 2 ^ (prefixWord ++ tailWord_2147383).sum := by decide
  have hdescent : baseEnd_2147383 < baseStart_2147383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147434 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2147434 : Nat := 118140960795 + 2147434 * 2 ^ 59
def prefixEnd_2147434 : Nat := 4983230072969 + 3 ^ 40 * 2147434 * 2
def baseEnd_2147434 : Nat := 1102665815807256388299137

theorem tailTrace_2147434 : CollatzResearch.WordTrace tailWord_2147434 prefixEnd_2147434 1102665815807256388299137 := by
  unfold tailWord_2147434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19580838125555211343412339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52215568334813896915766237 19580838125555211343412339)
  ·
    refine ⟨29371257188332817015118509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19580838125555211343412339 29371257188332817015118509)
    ·
      refine ⟨11014221445624806380669441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29371257188332817015118509 11014221445624806380669441)
      ·
        refine ⟨8260666084218604785502081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11014221445624806380669441 8260666084218604785502081)
        ·
          refine ⟨6195499563163953589126561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8260666084218604785502081 6195499563163953589126561)
          ·
            refine ⟨4646624672372965191844921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6195499563163953589126561 4646624672372965191844921)
            ·
              refine ⟨3484968504279723893883691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4646624672372965191844921 3484968504279723893883691)
              ·
                refine ⟨5227452756419585840825537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484968504279723893883691 5227452756419585840825537)
                ·
                  refine ⟨3920589567314689380619153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5227452756419585840825537 3920589567314689380619153)
                  ·
                    refine ⟨2940442175486017035464365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3920589567314689380619153 2940442175486017035464365)
                    ·
                      refine ⟨1102665815807256388299137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2940442175486017035464365 1102665815807256388299137)
                      ·
                        rfl

theorem cell23_2147434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2147434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147434 prefixEnd_2147434 := by exact prefixLift 2147434
  have htrace : WordTrace (prefixWord ++ tailWord_2147434) baseStart_2147434 baseEnd_2147434 := by
    simpa [prefixWord, tailWord_2147434, baseEnd_2147434] using wordTrace_append hprefix tailTrace_2147434
  have hstable : (prefixWord ++ tailWord_2147434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147434).length < 2 ^ (prefixWord ++ tailWord_2147434).sum := by decide
  have hdescent : baseEnd_2147434 < baseStart_2147434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147443 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 7]
def baseStart_2147443 : Nat := 118140960795 + 2147443 * 2 ^ 59
def prefixEnd_2147443 : Nat := 4983230072969 + 3 ^ 40 * 2147443 * 2
def baseEnd_2147443 : Nat := 1102670437133146853086595

theorem tailTrace_2147443 : CollatzResearch.WordTrace tailWord_2147443 prefixEnd_2147443 1102670437133146853086595 := by
  unfold tailWord_2147443
  simp only [CollatzResearch.WordTrace]
  refine ⟨78323680759188239910726983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52215787172792159940484655 78323680759188239910726983)
  ·
    refine ⟨117485521138782359866090475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78323680759188239910726983 117485521138782359866090475)
    ·
      refine ⟨176228281708173539799135713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117485521138782359866090475 176228281708173539799135713)
      ·
        refine ⟨132171211281130154849351785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176228281708173539799135713 132171211281130154849351785)
        ·
          refine ⟨99128408460847616137013839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132171211281130154849351785 99128408460847616137013839)
          ·
            refine ⟨148692612691271424205520759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99128408460847616137013839 148692612691271424205520759)
            ·
              refine ⟨223038919036907136308281139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148692612691271424205520759 223038919036907136308281139)
              ·
                refine ⟨334558378555360704462421709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223038919036907136308281139 334558378555360704462421709)
                ·
                  refine ⟨125459391958260264173408141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334558378555360704462421709 125459391958260264173408141)
                  ·
                    refine ⟨47047271984347599065028053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125459391958260264173408141 47047271984347599065028053)
                    ·
                      refine ⟨1102670437133146853086595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47047271984347599065028053 1102670437133146853086595)
                      ·
                        rfl

theorem cell23_2147443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_2147443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147443 prefixEnd_2147443 := by exact prefixLift 2147443
  have htrace : WordTrace (prefixWord ++ tailWord_2147443) baseStart_2147443 baseEnd_2147443 := by
    simpa [prefixWord, tailWord_2147443, baseEnd_2147443] using wordTrace_append hprefix tailTrace_2147443
  have hstable : (prefixWord ++ tailWord_2147443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147443).length < 2 ^ (prefixWord ++ tailWord_2147443).sum := by decide
  have hdescent : baseEnd_2147443 < baseStart_2147443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147498 : List Nat := [3, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_2147498 : Nat := 118140960795 + 2147498 * 2 ^ 59
def prefixEnd_2147498 : Nat := 4983230072969 + 3 ^ 40 * 2147498 * 2
def baseEnd_2147498 : Nat := 1102698678569144137898843

theorem tailTrace_2147498 : CollatzResearch.WordTrace tailWord_2147498 prefixEnd_2147498 1102698678569144137898843 := by
  unfold tailWord_2147498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19581421693497246075994787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52217124515992656202652765 19581421693497246075994787)
  ·
    refine ⟨29372132540245869113992181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19581421693497246075994787 29372132540245869113992181)
    ·
      refine ⟨2753637425648050229436767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29372132540245869113992181 2753637425648050229436767)
      ·
        refine ⟨4130456138472075344155151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753637425648050229436767 4130456138472075344155151)
        ·
          refine ⟨6195684207708113016232727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4130456138472075344155151 6195684207708113016232727)
          ·
            refine ⟨9293526311562169524349091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6195684207708113016232727 9293526311562169524349091)
            ·
              refine ⟨13940289467343254286523637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9293526311562169524349091 13940289467343254286523637)
              ·
                refine ⟨1306902137563430089361591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13940289467343254286523637 1306902137563430089361591)
                ·
                  refine ⟨1960353206345145134042387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306902137563430089361591 1960353206345145134042387)
                  ·
                    refine ⟨2940529809517717701063581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1960353206345145134042387 2940529809517717701063581)
                    ·
                      refine ⟨1102698678569144137898843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2940529809517717701063581 1102698678569144137898843)
                      ·
                        rfl

theorem cell23_2147498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_2147498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147498 prefixEnd_2147498 := by exact prefixLift 2147498
  have htrace : WordTrace (prefixWord ++ tailWord_2147498) baseStart_2147498 baseEnd_2147498 := by
    simpa [prefixWord, tailWord_2147498, baseEnd_2147498] using wordTrace_append hprefix tailTrace_2147498
  have hstable : (prefixWord ++ tailWord_2147498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147498).length < 2 ^ (prefixWord ++ tailWord_2147498).sum := by decide
  have hdescent : baseEnd_2147498 < baseStart_2147498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147500 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_2147500 : Nat := 118140960795 + 2147500 * 2 ^ 59
def prefixEnd_2147500 : Nat := 4983230072969 + 3 ^ 40 * 2147500 * 2
def baseEnd_2147500 : Nat := 1102699705530453130073833

theorem tailTrace_2147500 : CollatzResearch.WordTrace tailWord_2147500 prefixEnd_2147500 1102699705530453130073833 := by
  unfold tailWord_2147500
  simp only [CollatzResearch.WordTrace]
  refine ⟨39162879859990869322775977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52217173146654492430367969 39162879859990869322775977)
  ·
    refine ⟨29372159894993151992081983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39162879859990869322775977 29372159894993151992081983)
    ·
      refine ⟨44058239842489727988122975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29372159894993151992081983 44058239842489727988122975)
      ·
        refine ⟨66087359763734591982184463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44058239842489727988122975 66087359763734591982184463)
        ·
          refine ⟨99131039645601887973276695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66087359763734591982184463 99131039645601887973276695)
          ·
            refine ⟨148696559468402831959915043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99131039645601887973276695 148696559468402831959915043)
            ·
              refine ⟨223044839202604247939872565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148696559468402831959915043 223044839202604247939872565)
              ·
                refine ⟨20910453675244148244363053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223044839202604247939872565 20910453675244148244363053)
                ·
                  refine ⟨7841420128216555591636145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20910453675244148244363053 7841420128216555591636145)
                  ·
                    refine ⟨5881065096162416693727109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7841420128216555591636145 5881065096162416693727109)
                    ·
                      refine ⟨1102699705530453130073833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5881065096162416693727109 1102699705530453130073833)
                      ·
                        rfl

theorem cell23_2147500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_2147500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147500 prefixEnd_2147500 := by exact prefixLift 2147500
  have htrace : WordTrace (prefixWord ++ tailWord_2147500) baseStart_2147500 baseEnd_2147500 := by
    simpa [prefixWord, tailWord_2147500, baseEnd_2147500] using wordTrace_append hprefix tailTrace_2147500
  have hstable : (prefixWord ++ tailWord_2147500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147500).length < 2 ^ (prefixWord ++ tailWord_2147500).sum := by decide
  have hdescent : baseEnd_2147500 < baseStart_2147500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147524 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2147524 : Nat := 118140960795 + 2147524 * 2 ^ 59
def prefixEnd_2147524 : Nat := 4983230072969 + 3 ^ 40 * 2147524 * 2
def baseEnd_2147524 : Nat := 1102712029066161036173723

theorem tailTrace_2147524 : CollatzResearch.WordTrace tailWord_2147524 prefixEnd_2147524 1102712029066161036173723 := by
  unfold tailWord_2147524
  simp only [CollatzResearch.WordTrace]
  refine ⟨39163317535947395372212813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52217756714596527162950417 39163317535947395372212813)
  ·
    refine ⟨14686244075980273264579805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39163317535947395372212813 14686244075980273264579805)
    ·
      refine ⟨5507341528492602474217427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14686244075980273264579805 5507341528492602474217427)
      ·
        refine ⟨8261012292738903711326141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5507341528492602474217427 8261012292738903711326141)
        ·
          refine ⟨3097879609777088891747303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8261012292738903711326141 3097879609777088891747303)
          ·
            refine ⟨4646819414665633337620955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097879609777088891747303 4646819414665633337620955)
            ·
              refine ⟨6970229121998450006431433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4646819414665633337620955 6970229121998450006431433)
              ·
                refine ⟨5227671841498837504823575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6970229121998450006431433 5227671841498837504823575)
                ·
                  refine ⟨7841507762248256257235363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5227671841498837504823575 7841507762248256257235363)
                  ·
                    refine ⟨11762261643372384385853045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7841507762248256257235363 11762261643372384385853045)
                    ·
                      refine ⟨1102712029066161036173723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11762261643372384385853045 1102712029066161036173723)
                      ·
                        rfl

theorem cell23_2147524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2147524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147524 prefixEnd_2147524 := by exact prefixLift 2147524
  have htrace : WordTrace (prefixWord ++ tailWord_2147524) baseStart_2147524 baseEnd_2147524 := by
    simpa [prefixWord, tailWord_2147524, baseEnd_2147524] using wordTrace_append hprefix tailTrace_2147524
  have hstable : (prefixWord ++ tailWord_2147524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147524).length < 2 ^ (prefixWord ++ tailWord_2147524).sum := by decide
  have hdescent : baseEnd_2147524 < baseStart_2147524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147541 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2147541 : Nat := 118140960795 + 2147541 * 2 ^ 59
def prefixEnd_2147541 : Nat := 4983230072969 + 3 ^ 40 * 2147541 * 2
def baseEnd_2147541 : Nat := 1102720758237287469661145

theorem tailTrace_2147541 : CollatzResearch.WordTrace tailWord_2147541 prefixEnd_2147541 1102720758237287469661145 := by
  unfold tailWord_2147541
  simp only [CollatzResearch.WordTrace]
  refine ⟨78327255112833202647794477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52218170075222135098529651 78327255112833202647794477)
  ·
    refine ⟨29372720667312450992922929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78327255112833202647794477 29372720667312450992922929)
    ·
      refine ⟨22029540500484338244692197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29372720667312450992922929 22029540500484338244692197)
      ·
        refine ⟨4130538843840813420879787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22029540500484338244692197 4130538843840813420879787)
        ·
          refine ⟨6195808265761220131319681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4130538843840813420879787 6195808265761220131319681)
          ·
            refine ⟨4646856199320915098489761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6195808265761220131319681 4646856199320915098489761)
            ·
              refine ⟨3485142149490686323867321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4646856199320915098489761 3485142149490686323867321)
              ·
                refine ⟨2613856612118014742900491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3485142149490686323867321 2613856612118014742900491)
                ·
                  refine ⟨3920784918177022114350737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613856612118014742900491 3920784918177022114350737)
                  ·
                    refine ⟨2940588688632766585763053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3920784918177022114350737 2940588688632766585763053)
                    ·
                      refine ⟨1102720758237287469661145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2940588688632766585763053 1102720758237287469661145)
                      ·
                        rfl

theorem cell23_2147541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2147541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147541 prefixEnd_2147541 := by exact prefixLift 2147541
  have htrace : WordTrace (prefixWord ++ tailWord_2147541) baseStart_2147541 baseEnd_2147541 := by
    simpa [prefixWord, tailWord_2147541, baseEnd_2147541] using wordTrace_append hprefix tailTrace_2147541
  have hstable : (prefixWord ++ tailWord_2147541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147541).length < 2 ^ (prefixWord ++ tailWord_2147541).sum := by decide
  have hdescent : baseEnd_2147541 < baseStart_2147541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147544 : List Nat := [2, 1, 2, 2, 5, 2, 2, 7]
def baseStart_2147544 : Nat := 118140960795 + 2147544 * 2 ^ 59
def prefixEnd_2147544 : Nat := 4983230072969 + 3 ^ 40 * 2147544 * 2
def baseEnd_2147544 : Nat := 40841566617750035478653

theorem tailTrace_2147544 : CollatzResearch.WordTrace tailWord_2147544 prefixEnd_2147544 40841566617750035478653 := by
  unfold tailWord_2147544
  simp only [CollatzResearch.WordTrace]
  refine ⟨39163682265911167080076843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52218243021214889440102457 39163682265911167080076843)
  ·
    refine ⟨58745523398866750620115265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39163682265911167080076843 58745523398866750620115265)
    ·
      refine ⟨44059142549150062965086449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58745523398866750620115265 44059142549150062965086449)
      ·
        refine ⟨33044356911862547223814837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44059142549150062965086449 33044356911862547223814837)
        ·
          refine ⟨3097908460487113802232641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33044356911862547223814837 3097908460487113802232641)
          ·
            refine ⟨2323431345365335351674481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3097908460487113802232641 2323431345365335351674481)
            ·
              refine ⟨1742573509024001513755861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323431345365335351674481 1742573509024001513755861)
              ·
                refine ⟨40841566617750035478653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1742573509024001513755861 40841566617750035478653)
                ·
                  rfl

theorem cell23_2147544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 7].length) (baseStart_2147544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147544 prefixEnd_2147544 := by exact prefixLift 2147544
  have htrace : WordTrace (prefixWord ++ tailWord_2147544) baseStart_2147544 baseEnd_2147544 := by
    simpa [prefixWord, tailWord_2147544, baseEnd_2147544] using wordTrace_append hprefix tailTrace_2147544
  have hstable : (prefixWord ++ tailWord_2147544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147544).length < 2 ^ (prefixWord ++ tailWord_2147544).sum := by decide
  have hdescent : baseEnd_2147544 < baseStart_2147544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147588 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_2147588 : Nat := 118140960795 + 2147588 * 2 ^ 59
def prefixEnd_2147588 : Nat := 4983230072969 + 3 ^ 40 * 2147588 * 2
def baseEnd_2147588 : Nat := 1102744891828048785773429

theorem tailTrace_2147588 : CollatzResearch.WordTrace tailWord_2147588 prefixEnd_2147588 1102744891828048785773429 := by
  unfold tailWord_2147588
  simp only [CollatzResearch.WordTrace]
  refine ⟨39164484671831464837377709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52219312895775286449836945 39164484671831464837377709)
  ·
    refine ⟨14686681751936799314016641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39164484671831464837377709 14686681751936799314016641)
    ·
      refine ⟨11015011313952599485512481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14686681751936799314016641 11015011313952599485512481)
      ·
        refine ⟨8261258485464449614134361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11015011313952599485512481 8261258485464449614134361)
        ·
          refine ⟨6195943864098337210600771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8261258485464449614134361 6195943864098337210600771)
          ·
            refine ⟨9293915796147505815901157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6195943864098337210600771 9293915796147505815901157)
            ·
              refine ⟨1742609211777657340481467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9293915796147505815901157 1742609211777657340481467)
              ·
                refine ⟨2613913817666486010722201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742609211777657340481467 2613913817666486010722201)
                ·
                  refine ⟨1960435363249864508041651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2613913817666486010722201 1960435363249864508041651)
                  ·
                    refine ⟨2940653044874796762062477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1960435363249864508041651 2940653044874796762062477)
                    ·
                      refine ⟨1102744891828048785773429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2940653044874796762062477 1102744891828048785773429)
                      ·
                        rfl

theorem cell23_2147588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_2147588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147588 prefixEnd_2147588 := by exact prefixLift 2147588
  have htrace : WordTrace (prefixWord ++ tailWord_2147588) baseStart_2147588 baseEnd_2147588 := by
    simpa [prefixWord, tailWord_2147588, baseEnd_2147588] using wordTrace_append hprefix tailTrace_2147588
  have hstable : (prefixWord ++ tailWord_2147588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147588).length < 2 ^ (prefixWord ++ tailWord_2147588).sum := by decide
  have hdescent : baseEnd_2147588 < baseStart_2147588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147594 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2]
def baseStart_2147594 : Nat := 118140960795 + 2147594 * 2 ^ 59
def prefixEnd_2147594 : Nat := 4983230072969 + 3 ^ 40 * 2147594 * 2
def baseEnd_2147594 : Nat := 1102747972711975762298401

theorem tailTrace_2147594 : CollatzResearch.WordTrace tailWord_2147594 prefixEnd_2147594 1102747972711975762298401 := by
  unfold tailWord_2147594
  simp only [CollatzResearch.WordTrace]
  refine ⟨19582297045410298174868459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52219458787760795132982557 19582297045410298174868459)
  ·
    refine ⟨29373445568115447262302689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19582297045410298174868459 29373445568115447262302689)
    ·
      refine ⟨22030084176086585446727017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29373445568115447262302689 22030084176086585446727017)
      ·
        refine ⟨16522563132064939085045263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22030084176086585446727017 16522563132064939085045263)
        ·
          refine ⟨24783844698097408627567895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16522563132064939085045263 24783844698097408627567895)
          ·
            refine ⟨37175767047146112941351843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24783844698097408627567895 37175767047146112941351843)
            ·
              refine ⟨55763650570719169412027765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37175767047146112941351843 55763650570719169412027765)
              ·
                refine ⟨5227842241004922132377603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55763650570719169412027765 5227842241004922132377603)
                ·
                  refine ⟨7841763361507383198566405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5227842241004922132377603 7841763361507383198566405)
                  ·
                    refine ⟨1470330630282634349731201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7841763361507383198566405 1470330630282634349731201)
                    ·
                      refine ⟨1102747972711975762298401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470330630282634349731201 1102747972711975762298401)
                      ·
                        rfl

theorem cell23_2147594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_2147594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147594 prefixEnd_2147594 := by exact prefixLift 2147594
  have htrace : WordTrace (prefixWord ++ tailWord_2147594) baseStart_2147594 baseEnd_2147594 := by
    simpa [prefixWord, tailWord_2147594, baseEnd_2147594] using wordTrace_append hprefix tailTrace_2147594
  have hstable : (prefixWord ++ tailWord_2147594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147594).length < 2 ^ (prefixWord ++ tailWord_2147594).sum := by decide
  have hdescent : baseEnd_2147594 < baseStart_2147594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147598 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2]
def baseStart_2147598 : Nat := 118140960795 + 2147598 * 2 ^ 59
def prefixEnd_2147598 : Nat := 4983230072969 + 3 ^ 40 * 2147598 * 2
def baseEnd_2147598 : Nat := 1102750026634593746648383

theorem tailTrace_2147598 : CollatzResearch.WordTrace tailWord_2147598 prefixEnd_2147598 1102750026634593746648383 := by
  unfold tailWord_2147598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9791166759203337672827431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52219556049084467588412965 9791166759203337672827431)
  ·
    refine ⟨14686750138805006509241147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9791166759203337672827431 14686750138805006509241147)
    ·
      refine ⟨22030125208207509763861721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14686750138805006509241147 22030125208207509763861721)
      ·
        refine ⟨16522593906155632322896291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22030125208207509763861721 16522593906155632322896291)
        ·
          refine ⟨24783890859233448484344437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16522593906155632322896291 24783890859233448484344437)
          ·
            refine ⟨2323489768053135795407291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24783890859233448484344437 2323489768053135795407291)
            ·
              refine ⟨3485234652079703693110937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323489768053135795407291 3485234652079703693110937)
              ·
                refine ⟨2613925989059777769833203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3485234652079703693110937 2613925989059777769833203)
                ·
                  refine ⟨3920888983589666654749805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613925989059777769833203 3920888983589666654749805)
                  ·
                    refine ⟨1470333368846124995531177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3920888983589666654749805 1470333368846124995531177)
                    ·
                      refine ⟨1102750026634593746648383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470333368846124995531177 1102750026634593746648383)
                      ·
                        rfl

theorem cell23_2147598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_2147598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147598 prefixEnd_2147598 := by exact prefixLift 2147598
  have htrace : WordTrace (prefixWord ++ tailWord_2147598) baseStart_2147598 baseEnd_2147598 := by
    simpa [prefixWord, tailWord_2147598, baseEnd_2147598] using wordTrace_append hprefix tailTrace_2147598
  have hstable : (prefixWord ++ tailWord_2147598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147598).length < 2 ^ (prefixWord ++ tailWord_2147598).sum := by decide
  have hdescent : baseEnd_2147598 < baseStart_2147598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147644 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_2147644 : Nat := 118140960795 + 2147644 * 2 ^ 59
def prefixEnd_2147644 : Nat := 4983230072969 + 3 ^ 40 * 2147644 * 2
def baseEnd_2147644 : Nat := 1102773646744700566673171

theorem tailTrace_2147644 : CollatzResearch.WordTrace tailWord_2147644 prefixEnd_2147644 1102773646744700566673171 := by
  unfold tailWord_2147644
  simp only [CollatzResearch.WordTrace]
  refine ⟨39165505915730025619396993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52220674554306700825862657 39165505915730025619396993)
  ·
    refine ⟨29374129436797519214547745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39165505915730025619396993 29374129436797519214547745)
    ·
      refine ⟨22030597077598139410910809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29374129436797519214547745 22030597077598139410910809)
      ·
        refine ⟨16522947808198604558183107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22030597077598139410910809 16522947808198604558183107)
        ·
          refine ⟨24784421712297906837274661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16522947808198604558183107 24784421712297906837274661)
          ·
            refine ⟨4647079071055857531988999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24784421712297906837274661 4647079071055857531988999)
            ·
              refine ⟨6970618606583786297983499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4647079071055857531988999 6970618606583786297983499)
              ·
                refine ⟨10455927909875679446975249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6970618606583786297983499 10455927909875679446975249)
                ·
                  refine ⟨7841945932406759585231437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10455927909875679446975249 7841945932406759585231437)
                  ·
                    refine ⟨2940729724652534844461789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7841945932406759585231437 2940729724652534844461789)
                    ·
                      refine ⟨1102773646744700566673171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2940729724652534844461789 1102773646744700566673171)
                      ·
                        rfl

theorem cell23_2147644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_2147644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147644 prefixEnd_2147644 := by exact prefixLift 2147644
  have htrace : WordTrace (prefixWord ++ tailWord_2147644) baseStart_2147644 baseEnd_2147644 := by
    simpa [prefixWord, tailWord_2147644, baseEnd_2147644] using wordTrace_append hprefix tailTrace_2147644
  have hstable : (prefixWord ++ tailWord_2147644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147644).length < 2 ^ (prefixWord ++ tailWord_2147644).sum := by decide
  have hdescent : baseEnd_2147644 < baseStart_2147644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147667 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 4]
def baseStart_2147667 : Nat := 118140960795 + 2147667 * 2 ^ 59
def prefixEnd_2147667 : Nat := 4983230072969 + 3 ^ 40 * 2147667 * 2
def baseEnd_2147667 : Nat := 1102785456799753976685565

theorem tailTrace_2147667 : CollatzResearch.WordTrace tailWord_2147667 prefixEnd_2147667 1102785456799753976685565 := by
  unfold tailWord_2147667
  simp only [CollatzResearch.WordTrace]
  refine ⟨78331850710376726166881255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52221233806917817444587503 78331850710376726166881255)
  ·
    refine ⟨117497776065565089250321883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78331850710376726166881255 117497776065565089250321883)
    ·
      refine ⟨176246664098347633875482825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117497776065565089250321883 176246664098347633875482825)
      ·
        refine ⟨132184998073760725406612119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176246664098347633875482825 132184998073760725406612119)
        ·
          refine ⟨198277497110641088109918179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132184998073760725406612119 198277497110641088109918179)
          ·
            refine ⟨297416245665961632164877269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198277497110641088109918179 297416245665961632164877269)
            ·
              refine ⟨6970693257795975753864311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 297416245665961632164877269 6970693257795975753864311)
              ·
                refine ⟨10456039886693963630796467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6970693257795975753864311 10456039886693963630796467)
                ·
                  refine ⟨15684059830040945446194701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10456039886693963630796467 15684059830040945446194701)
                  ·
                    refine ⟨5881522436265354542323013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15684059830040945446194701 5881522436265354542323013)
                    ·
                      refine ⟨1102785456799753976685565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5881522436265354542323013 1102785456799753976685565)
                      ·
                        rfl

theorem cell23_2147667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_2147667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147667 prefixEnd_2147667 := by exact prefixLift 2147667
  have htrace : WordTrace (prefixWord ++ tailWord_2147667) baseStart_2147667 baseEnd_2147667 := by
    simpa [prefixWord, tailWord_2147667, baseEnd_2147667] using wordTrace_append hprefix tailTrace_2147667
  have hstable : (prefixWord ++ tailWord_2147667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147667).length < 2 ^ (prefixWord ++ tailWord_2147667).sum := by decide
  have hdescent : baseEnd_2147667 < baseStart_2147667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147761 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 4, 3, 2]
def baseStart_2147761 : Nat := 118140960795 + 2147761 * 2 ^ 59
def prefixEnd_2147761 : Nat := 4983230072969 + 3 ^ 40 * 2147761 * 2
def baseEnd_2147761 : Nat := 1102833723981276608910133

theorem tailTrace_2147761 : CollatzResearch.WordTrace tailWord_2147761 prefixEnd_2147761 1102833723981276608910133 := by
  unfold tailWord_2147761
  simp only [CollatzResearch.WordTrace]
  refine ⟨78335279172036180220803137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52223519448024120147202091 78335279172036180220803137)
  ·
    refine ⟨58751459379027135165602353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78335279172036180220803137 58751459379027135165602353)
    ·
      refine ⟨44063594534270351374201765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58751459379027135165602353 44063594534270351374201765)
      ·
        refine ⟨8261923975175690882662831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44063594534270351374201765 8261923975175690882662831)
        ·
          refine ⟨12392885962763536323994247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8261923975175690882662831 12392885962763536323994247)
          ·
            refine ⟨18589328944145304485991371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12392885962763536323994247 18589328944145304485991371)
            ·
              refine ⟨27883993416217956728987057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18589328944145304485991371 27883993416217956728987057)
              ·
                refine ⟨20912995062163467546740293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27883993416217956728987057 20912995062163467546740293)
                ·
                  refine ⟨3921186574155650165013805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20912995062163467546740293 3921186574155650165013805)
                  ·
                    refine ⟨1470444965308368811880177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3921186574155650165013805 1470444965308368811880177)
                    ·
                      refine ⟨1102833723981276608910133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470444965308368811880177 1102833723981276608910133)
                      ·
                        rfl

theorem cell23_2147761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_2147761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147761 prefixEnd_2147761 := by exact prefixLift 2147761
  have htrace : WordTrace (prefixWord ++ tailWord_2147761) baseStart_2147761 baseEnd_2147761 := by
    simpa [prefixWord, tailWord_2147761, baseEnd_2147761] using wordTrace_append hprefix tailTrace_2147761
  have hstable : (prefixWord ++ tailWord_2147761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147761).length < 2 ^ (prefixWord ++ tailWord_2147761).sum := by decide
  have hdescent : baseEnd_2147761 < baseStart_2147761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147784 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 1, 6]
def baseStart_2147784 : Nat := 118140960795 + 2147784 * 2 ^ 59
def prefixEnd_2147784 : Nat := 4983230072969 + 3 ^ 40 * 2147784 * 2
def baseEnd_2147784 : Nat := 367615178012110006307509

theorem tailTrace_2147784 : CollatzResearch.WordTrace tailWord_2147784 prefixEnd_2147784 367615178012110006307509 := by
  unfold tailWord_2147784
  simp only [CollatzResearch.WordTrace]
  refine ⟨39168059025476427574445203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52224078700635236765926937 39168059025476427574445203)
  ·
    refine ⟨58752088538214641361667805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39168059025476427574445203 58752088538214641361667805)
    ·
      refine ⟨22032033201830490510625427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58752088538214641361667805 22032033201830490510625427)
      ·
        refine ⟨33048049802745735765938141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22032033201830490510625427 33048049802745735765938141)
        ·
          refine ⟨12393018676029650912226803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33048049802745735765938141 12393018676029650912226803)
          ·
            refine ⟨18589528014044476368340205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12393018676029650912226803 18589528014044476368340205)
            ·
              refine ⟨6971073005266678638127577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18589528014044476368340205 6971073005266678638127577)
              ·
                refine ⟨5228304753950008978595683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6971073005266678638127577 5228304753950008978595683)
                ·
                  refine ⟨7842457130925013467893525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5228304753950008978595683 7842457130925013467893525)
                  ·
                    refine ⟨367615178012110006307509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7842457130925013467893525 367615178012110006307509)
                    ·
                      rfl

theorem cell23_2147784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_2147784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147784 prefixEnd_2147784 := by exact prefixLift 2147784
  have htrace : WordTrace (prefixWord ++ tailWord_2147784) baseStart_2147784 baseEnd_2147784 := by
    simpa [prefixWord, tailWord_2147784, baseEnd_2147784] using wordTrace_append hprefix tailTrace_2147784
  have hstable : (prefixWord ++ tailWord_2147784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147784).length < 2 ^ (prefixWord ++ tailWord_2147784).sum := by decide
  have hdescent : baseEnd_2147784 < baseStart_2147784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147788 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 1, 5]
def baseStart_2147788 : Nat := 118140960795 + 2147788 * 2 ^ 59
def prefixEnd_2147788 : Nat := 4983230072969 + 3 ^ 40 * 2147788 * 2
def baseEnd_2147788 : Nat := 367615862652982667757503

theorem tailTrace_2147788 : CollatzResearch.WordTrace tailWord_2147788 prefixEnd_2147788 367615862652982667757503 := by
  unfold tailWord_2147788
  simp only [CollatzResearch.WordTrace]
  refine ⟨39168131971469181916018009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52224175961958909221357345 39168131971469181916018009)
  ·
    refine ⟨29376098978601886437013507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39168131971469181916018009 29376098978601886437013507)
    ·
      refine ⟨44064148467902829655520261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29376098978601886437013507 44064148467902829655520261)
      ·
        refine ⟨8262027837731780560410049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44064148467902829655520261 8262027837731780560410049)
        ·
          refine ⟨6196520878298835420307537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8262027837731780560410049 6196520878298835420307537)
          ·
            refine ⟨4647390658724126565230653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6196520878298835420307537 4647390658724126565230653)
            ·
              refine ⟨1742771497021547461961495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4647390658724126565230653 1742771497021547461961495)
              ·
                refine ⟨2614157245532321192942243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742771497021547461961495 2614157245532321192942243)
                ·
                  refine ⟨3921235868298481789413365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614157245532321192942243 3921235868298481789413365)
                  ·
                    refine ⟨367615862652982667757503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3921235868298481789413365 367615862652982667757503)
                    ·
                      rfl

theorem cell23_2147788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_2147788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147788 prefixEnd_2147788 := by exact prefixLift 2147788
  have htrace : WordTrace (prefixWord ++ tailWord_2147788) baseStart_2147788 baseEnd_2147788 := by
    simpa [prefixWord, tailWord_2147788, baseEnd_2147788] using wordTrace_append hprefix tailTrace_2147788
  have hstable : (prefixWord ++ tailWord_2147788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147788).length < 2 ^ (prefixWord ++ tailWord_2147788).sum := by decide
  have hdescent : baseEnd_2147788 < baseStart_2147788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147801 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 2, 4]
def baseStart_2147801 : Nat := 118140960795 + 2147801 * 2 ^ 59
def prefixEnd_2147801 : Nat := 4983230072969 + 3 ^ 40 * 2147801 * 2
def baseEnd_2147801 : Nat := 367618087735818817469983

theorem tailTrace_2147801 : CollatzResearch.WordTrace tailWord_2147801 prefixEnd_2147801 367618087735818817469983 := by
  unfold tailWord_2147801
  simp only [CollatzResearch.WordTrace]
  refine ⟨78336738091891267052259257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52224492061260844701506171 78336738091891267052259257)
  ·
    refine ⟨58752553568918450289194443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78336738091891267052259257 58752553568918450289194443)
    ·
      refine ⟨88128830353377675433791665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58752553568918450289194443 88128830353377675433791665)
      ·
        refine ⟨66096622765033256575343749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88128830353377675433791665 66096622765033256575343749)
        ·
          refine ⟨12393116768443735607876953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66096622765033256575343749 12393116768443735607876953)
          ·
            refine ⟨9294837576332801705907715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12393116768443735607876953 9294837576332801705907715)
            ·
              refine ⟨13942256364499202558861573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9294837576332801705907715 13942256364499202558861573)
              ·
                refine ⟨2614173068343600479786545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13942256364499202558861573 2614173068343600479786545)
                ·
                  refine ⟨1960629801257700359839909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2614173068343600479786545 1960629801257700359839909)
                  ·
                    refine ⟨367618087735818817469983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1960629801257700359839909 367618087735818817469983)
                    ·
                      rfl

theorem cell23_2147801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 4].length) (baseStart_2147801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147801 prefixEnd_2147801 := by exact prefixLift 2147801
  have htrace : WordTrace (prefixWord ++ tailWord_2147801) baseStart_2147801 baseEnd_2147801 := by
    simpa [prefixWord, tailWord_2147801, baseEnd_2147801] using wordTrace_append hprefix tailTrace_2147801
  have hstable : (prefixWord ++ tailWord_2147801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147801).length < 2 ^ (prefixWord ++ tailWord_2147801).sum := by decide
  have hdescent : baseEnd_2147801 < baseStart_2147801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147802 : List Nat := [3, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3]
def baseStart_2147802 : Nat := 118140960795 + 2147802 * 2 ^ 59
def prefixEnd_2147802 : Nat := 4983230072969 + 3 ^ 40 * 2147802 * 2
def baseEnd_2147802 : Nat := 1102854776688110948497445

theorem tailTrace_2147802 : CollatzResearch.WordTrace tailWord_2147802 prefixEnd_2147802 1102854776688110948497445 := by
  unfold tailWord_2147802
  simp only [CollatzResearch.WordTrace]
  refine ⟨19584193641221911055761415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52224516376591762815363773 19584193641221911055761415)
  ·
    refine ⟨29376290461832866583642123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19584193641221911055761415 29376290461832866583642123)
    ·
      refine ⟨44064435692749299875463185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29376290461832866583642123 44064435692749299875463185)
      ·
        refine ⟨33048326769561974906597389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44064435692749299875463185 33048326769561974906597389)
        ·
          refine ⟨12393122538585740589974021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33048326769561974906597389 12393122538585740589974021)
          ·
            refine ⟨2323710475984826360620129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12393122538585740589974021 2323710475984826360620129)
            ·
              refine ⟨1742782856988619770465097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323710475984826360620129 1742782856988619770465097)
              ·
                refine ⟨1307087142741464827848823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1742782856988619770465097 1307087142741464827848823)
                ·
                  refine ⟨1960630714112197241773235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307087142741464827848823 1960630714112197241773235)
                  ·
                    refine ⟨2940946071168295862659853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1960630714112197241773235 2940946071168295862659853)
                    ·
                      refine ⟨1102854776688110948497445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2940946071168295862659853 1102854776688110948497445)
                      ·
                        rfl

theorem cell23_2147802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_2147802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147802 prefixEnd_2147802 := by exact prefixLift 2147802
  have htrace : WordTrace (prefixWord ++ tailWord_2147802) baseStart_2147802 baseEnd_2147802 := by
    simpa [prefixWord, tailWord_2147802, baseEnd_2147802] using wordTrace_append hprefix tailTrace_2147802
  have hstable : (prefixWord ++ tailWord_2147802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147802).length < 2 ^ (prefixWord ++ tailWord_2147802).sum := by decide
  have hdescent : baseEnd_2147802 < baseStart_2147802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147811 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2147811 : Nat := 118140960795 + 2147811 * 2 ^ 59
def prefixEnd_2147811 : Nat := 4983230072969 + 3 ^ 40 * 2147811 * 2
def baseEnd_2147811 : Nat := 1102859398014001413284903

theorem tailTrace_2147811 : CollatzResearch.WordTrace tailWord_2147811 prefixEnd_2147811 1102859398014001413284903 := by
  unfold tailWord_2147811
  simp only [CollatzResearch.WordTrace]
  refine ⟨78337102821855038760123287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52224735214570025840082191 78337102821855038760123287)
  ·
    refine ⟨117505654232782558140184931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78337102821855038760123287 117505654232782558140184931)
    ·
      refine ⟨176258481349173837210277397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117505654232782558140184931 176258481349173837210277397)
      ·
        refine ⟨8262116313242523619231753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 176258481349173837210277397 8262116313242523619231753)
        ·
          refine ⟨6196587234931892714423815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8262116313242523619231753 6196587234931892714423815)
          ·
            refine ⟨9294880852397839071635723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6196587234931892714423815 9294880852397839071635723)
            ·
              refine ⟨13942321278596758607453585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9294880852397839071635723 13942321278596758607453585)
              ·
                refine ⟨10456740958947568955590189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13942321278596758607453585 10456740958947568955590189)
                ·
                  refine ⟨3921277859605338358346321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10456740958947568955590189 3921277859605338358346321)
                  ·
                    refine ⟨2940958394704003768759741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3921277859605338358346321 2940958394704003768759741)
                    ·
                      refine ⟨1102859398014001413284903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2940958394704003768759741 1102859398014001413284903)
                      ·
                        rfl

theorem cell23_2147811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2147811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147811 prefixEnd_2147811 := by exact prefixLift 2147811
  have htrace : WordTrace (prefixWord ++ tailWord_2147811) baseStart_2147811 baseEnd_2147811 := by
    simpa [prefixWord, tailWord_2147811, baseEnd_2147811] using wordTrace_append hprefix tailTrace_2147811
  have hstable : (prefixWord ++ tailWord_2147811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147811).length < 2 ^ (prefixWord ++ tailWord_2147811).sum := by decide
  have hdescent : baseEnd_2147811 < baseStart_2147811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147842 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2147842 : Nat := 118140960795 + 2147842 * 2 ^ 59
def prefixEnd_2147842 : Nat := 4983230072969 + 3 ^ 40 * 2147842 * 2
def baseEnd_2147842 : Nat := 1102875315914290791997261

theorem tailTrace_2147842 : CollatzResearch.WordTrace tailWord_2147842 prefixEnd_2147842 1102875315914290791997261 := by
  unfold tailWord_2147842
  simp only [CollatzResearch.WordTrace]
  refine ⟨19584558371185682763625445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52225488989828487369667853 19584558371185682763625445)
  ·
    refine ⟨3672104694597315518179771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19584558371185682763625445 3672104694597315518179771)
    ·
      refine ⟨5508157041895973277269657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3672104694597315518179771 5508157041895973277269657)
      ·
        refine ⟨4131117781421979957952243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5508157041895973277269657 4131117781421979957952243)
        ·
          refine ⟨6196676672132969936928365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4131117781421979957952243 6196676672132969936928365)
          ·
            refine ⟨2323753752049863726348137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6196676672132969936928365 2323753752049863726348137)
            ·
              refine ⟨1742815314037397794761103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323753752049863726348137 1742815314037397794761103)
              ·
                refine ⟨2614222971056096692141655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742815314037397794761103 2614222971056096692141655)
                ·
                  refine ⟨3921334456584145038212483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614222971056096692141655 3921334456584145038212483)
                  ·
                    refine ⟨5882001684876217557318725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3921334456584145038212483 5882001684876217557318725)
                    ·
                      refine ⟨1102875315914290791997261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5882001684876217557318725 1102875315914290791997261)
                      ·
                        rfl

theorem cell23_2147842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2147842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147842 prefixEnd_2147842 := by exact prefixLift 2147842
  have htrace : WordTrace (prefixWord ++ tailWord_2147842) baseStart_2147842 baseEnd_2147842 := by
    simpa [prefixWord, tailWord_2147842, baseEnd_2147842] using wordTrace_append hprefix tailTrace_2147842
  have hstable : (prefixWord ++ tailWord_2147842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147842).length < 2 ^ (prefixWord ++ tailWord_2147842).sum := by decide
  have hdescent : baseEnd_2147842 < baseStart_2147842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147875 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 1, 3, 3]
def baseStart_2147875 : Nat := 118140960795 + 2147875 * 2 ^ 59
def prefixEnd_2147875 : Nat := 4983230072969 + 3 ^ 40 * 2147875 * 2
def baseEnd_2147875 : Nat := 1102892260775889162884609

theorem tailTrace_2147875 : CollatzResearch.WordTrace tailWord_2147875 prefixEnd_2147875 1102892260775889162884609 := by
  unfold tailWord_2147875
  simp only [CollatzResearch.WordTrace]
  refine ⟨78339437093623177690453079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52226291395748785126968719 78339437093623177690453079)
  ·
    refine ⟨117509155640434766535679619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78339437093623177690453079 117509155640434766535679619)
    ·
      refine ⟨176263733460652149803519429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117509155640434766535679619 176263733460652149803519429)
      ·
        refine ⟨33049450023872278088159893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176263733460652149803519429 33049450023872278088159893)
        ·
          refine ⟨1549192969869013035382495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33049450023872278088159893 1549192969869013035382495)
          ·
            refine ⟨2323789454803519553073743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549192969869013035382495 2323789454803519553073743)
            ·
              refine ⟨3485684182205279329610615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323789454803519553073743 3485684182205279329610615)
              ·
                refine ⟨5228526273307918994415923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3485684182205279329610615 5228526273307918994415923)
                ·
                  refine ⟨7842789409961878491623885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5228526273307918994415923 7842789409961878491623885)
                  ·
                    refine ⟨2941046028735704434358957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7842789409961878491623885 2941046028735704434358957)
                    ·
                      refine ⟨1102892260775889162884609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2941046028735704434358957 1102892260775889162884609)
                      ·
                        rfl

theorem cell23_2147875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_2147875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147875 prefixEnd_2147875 := by exact prefixLift 2147875
  have htrace : WordTrace (prefixWord ++ tailWord_2147875) baseStart_2147875 baseEnd_2147875 := by
    simpa [prefixWord, tailWord_2147875, baseEnd_2147875] using wordTrace_append hprefix tailTrace_2147875
  have hstable : (prefixWord ++ tailWord_2147875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147875).length < 2 ^ (prefixWord ++ tailWord_2147875).sum := by decide
  have hdescent : baseEnd_2147875 < baseStart_2147875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147898 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2]
def baseStart_2147898 : Nat := 118140960795 + 2147898 * 2 ^ 59
def prefixEnd_2147898 : Nat := 4983230072969 + 3 ^ 40 * 2147898 * 2
def baseEnd_2147898 : Nat := 1102904070830942572897003

theorem tailTrace_2147898 : CollatzResearch.WordTrace tailWord_2147898 prefixEnd_2147898 1102904070830942572897003 := by
  unfold tailWord_2147898
  simp only [CollatzResearch.WordTrace]
  refine ⟨19585068993134963154635087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52226850648359901745693565 19585068993134963154635087)
  ·
    refine ⟨29377603489702444731952631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19585068993134963154635087 29377603489702444731952631)
    ·
      refine ⟨44066405234553667097928947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29377603489702444731952631 44066405234553667097928947)
      ·
        refine ⟨66099607851830500646893421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44066405234553667097928947 66099607851830500646893421)
        ·
          refine ⟨24787352944436437742585033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66099607851830500646893421 24787352944436437742585033)
          ·
            refine ⟨18590514708327328306938775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24787352944436437742585033 18590514708327328306938775)
            ·
              refine ⟨27885772062490992460408163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18590514708327328306938775 27885772062490992460408163)
              ·
                refine ⟨41828658093736488690612245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27885772062490992460408163 41828658093736488690612245)
                ·
                  refine ⟨1960718348143897907372449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41828658093736488690612245 1960718348143897907372449)
                  ·
                    refine ⟨1470538761107923430529337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1960718348143897907372449 1470538761107923430529337)
                    ·
                      refine ⟨1102904070830942572897003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470538761107923430529337 1102904070830942572897003)
                      ·
                        rfl

theorem cell23_2147898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_2147898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147898 prefixEnd_2147898 := by exact prefixLift 2147898
  have htrace : WordTrace (prefixWord ++ tailWord_2147898) baseStart_2147898 baseEnd_2147898 := by
    simpa [prefixWord, tailWord_2147898, baseEnd_2147898] using wordTrace_append hprefix tailTrace_2147898
  have hstable : (prefixWord ++ tailWord_2147898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147898).length < 2 ^ (prefixWord ++ tailWord_2147898).sum := by decide
  have hdescent : baseEnd_2147898 < baseStart_2147898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147914 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_2147914 : Nat := 118140960795 + 2147914 * 2 ^ 59
def prefixEnd_2147914 : Nat := 4983230072969 + 3 ^ 40 * 2147914 * 2
def baseEnd_2147914 : Nat := 1102912286521414510296929

theorem tailTrace_2147914 : CollatzResearch.WordTrace tailWord_2147914 prefixEnd_2147914 1102912286521414510296929 := by
  unfold tailWord_2147914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19585214885120471837780699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52227239693654591567415197 19585214885120471837780699)
  ·
    refine ⟨29377822327680707756671049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19585214885120471837780699 29377822327680707756671049)
    ·
      refine ⟨22033366745760530817503287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29377822327680707756671049 22033366745760530817503287)
      ·
        refine ⟨33050050118640796226254931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22033366745760530817503287 33050050118640796226254931)
        ·
          refine ⟨49575075177961194339382397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33050050118640796226254931 49575075177961194339382397)
          ·
            refine ⟨18590653191735447877268399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49575075177961194339382397 18590653191735447877268399)
            ·
              refine ⟨27885979787603171815902599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18590653191735447877268399 27885979787603171815902599)
              ·
                refine ⟨41828969681404757723853899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27885979787603171815902599 41828969681404757723853899)
                ·
                  refine ⟨62743454522107136585780849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41828969681404757723853899 62743454522107136585780849)
                  ·
                    refine ⟨47057590891580352439335637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62743454522107136585780849 47057590891580352439335637)
                    ·
                      refine ⟨1102912286521414510296929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47057590891580352439335637 1102912286521414510296929)
                      ·
                        rfl

theorem cell23_2147914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_2147914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147914 prefixEnd_2147914 := by exact prefixLift 2147914
  have htrace : WordTrace (prefixWord ++ tailWord_2147914) baseStart_2147914 baseEnd_2147914 := by
    simpa [prefixWord, tailWord_2147914, baseEnd_2147914] using wordTrace_append hprefix tailTrace_2147914
  have hstable : (prefixWord ++ tailWord_2147914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147914).length < 2 ^ (prefixWord ++ tailWord_2147914).sum := by decide
  have hdescent : baseEnd_2147914 < baseStart_2147914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147932 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_2147932 : Nat := 118140960795 + 2147932 * 2 ^ 59
def prefixEnd_2147932 : Nat := 4983230072969 + 3 ^ 40 * 2147932 * 2
def baseEnd_2147932 : Nat := 1102921529173195439871847

theorem tailTrace_2147932 : CollatzResearch.WordTrace tailWord_2147932 prefixEnd_2147932 1102921529173195439871847 := by
  unfold tailWord_2147932
  simp only [CollatzResearch.WordTrace]
  refine ⟨39170758027208338212639025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52227677369611117616852033 39170758027208338212639025)
  ·
    refine ⟨29378068520406253659479269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39170758027208338212639025 29378068520406253659479269)
    ·
      refine ⟨5508387847576172561152363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29378068520406253659479269 5508387847576172561152363)
      ·
        refine ⟨8262581771364258841728545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5508387847576172561152363 8262581771364258841728545)
        ·
          refine ⟨6196936328523194131296409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8262581771364258841728545 6196936328523194131296409)
          ·
            refine ⟨4647702246392395598472307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6196936328523194131296409 4647702246392395598472307)
            ·
              refine ⟨6971553369588593397708461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4647702246392395598472307 6971553369588593397708461)
              ·
                refine ⟨2614332513595722524140673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6971553369588593397708461 2614332513595722524140673)
                ·
                  refine ⟨1960749385196791893105505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2614332513595722524140673 1960749385196791893105505)
                  ·
                    refine ⟨1470562038897593919829129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1960749385196791893105505 1470562038897593919829129)
                    ·
                      refine ⟨1102921529173195439871847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470562038897593919829129 1102921529173195439871847)
                      ·
                        rfl

theorem cell23_2147932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_2147932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147932 prefixEnd_2147932 := by exact prefixLift 2147932
  have htrace : WordTrace (prefixWord ++ tailWord_2147932) baseStart_2147932 baseEnd_2147932 := by
    simpa [prefixWord, tailWord_2147932, baseEnd_2147932] using wordTrace_append hprefix tailTrace_2147932
  have hstable : (prefixWord ++ tailWord_2147932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147932).length < 2 ^ (prefixWord ++ tailWord_2147932).sum := by decide
  have hdescent : baseEnd_2147932 < baseStart_2147932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147972 : List Nat := [2, 3, 2, 1, 4, 2, 2, 2, 5]
def baseStart_2147972 : Nat := 118140960795 + 2147972 * 2 ^ 59
def prefixEnd_2147972 : Nat := 4983230072969 + 3 ^ 40 * 2147972 * 2
def baseEnd_2147972 : Nat := 122549118711041698152407

theorem tailTrace_2147972 : CollatzResearch.WordTrace tailWord_2147972 prefixEnd_2147972 122549118711041698152407 := by
  unfold tailWord_2147972
  simp only [CollatzResearch.WordTrace]
  refine ⟨39171487487135881628367085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52228649982847842171156113 39171487487135881628367085)
  ·
    refine ⟨14689307807675955610637657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39171487487135881628367085 14689307807675955610637657)
    ·
      refine ⟨11016980855756966707978243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14689307807675955610637657 11016980855756966707978243)
      ·
        refine ⟨16525471283635450061967365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11016980855756966707978243 16525471283635450061967365)
        ·
          refine ⟨3098525865681646886618881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16525471283635450061967365 3098525865681646886618881)
          ·
            refine ⟨2323894399261235164964161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3098525865681646886618881 2323894399261235164964161)
            ·
              refine ⟨1742920799445926373723121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323894399261235164964161 1742920799445926373723121)
              ·
                refine ⟨1307190599584444780292341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1742920799445926373723121 1307190599584444780292341)
                ·
                  refine ⟨122549118711041698152407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1307190599584444780292341 122549118711041698152407)
                  ·
                    rfl

theorem cell23_2147972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_2147972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2147972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2147972 prefixEnd_2147972 := by exact prefixLift 2147972
  have htrace : WordTrace (prefixWord ++ tailWord_2147972) baseStart_2147972 baseEnd_2147972 := by
    simpa [prefixWord, tailWord_2147972, baseEnd_2147972] using wordTrace_append hprefix tailTrace_2147972
  have hstable : (prefixWord ++ tailWord_2147972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147972).length < 2 ^ (prefixWord ++ tailWord_2147972).sum := by decide
  have hdescent : baseEnd_2147972 < baseStart_2147972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148002 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_2148002 : Nat := 118140960795 + 2148002 * 2 ^ 59
def prefixEnd_2148002 : Nat := 4983230072969 + 3 ^ 40 * 2148002 * 2
def baseEnd_2148002 : Nat := 367652490939670055332175

theorem tailTrace_2148002 : CollatzResearch.WordTrace tailWord_2148002 prefixEnd_2148002 367652490939670055332175 := by
  unfold tailWord_2148002
  simp only [CollatzResearch.WordTrace]
  refine ⟨19586017291040769595081565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52229379442775385586884173 19586017291040769595081565)
  ·
    refine ⟨7344756484140288598155587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19586017291040769595081565 7344756484140288598155587)
    ·
      refine ⟨11017134726210432897233381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7344756484140288598155587 11017134726210432897233381)
      ·
        refine ⟨2065712761164456168231259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11017134726210432897233381 2065712761164456168231259)
        ·
          refine ⟨3098569141746684252346889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065712761164456168231259 3098569141746684252346889)
          ·
            refine ⟨2323926856310013189260167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3098569141746684252346889 2323926856310013189260167)
            ·
              refine ⟨3485890284465019783890251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323926856310013189260167 3485890284465019783890251)
              ·
                refine ⟨5228835426697529675835377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3485890284465019783890251 5228835426697529675835377)
                ·
                  refine ⟨3921626570023147256876533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5228835426697529675835377 3921626570023147256876533)
                  ·
                    refine ⟨367652490939670055332175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3921626570023147256876533 367652490939670055332175)
                    ·
                      rfl

theorem cell23_2148002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_2148002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148002 prefixEnd_2148002 := by exact prefixLift 2148002
  have htrace : WordTrace (prefixWord ++ tailWord_2148002) baseStart_2148002 baseEnd_2148002 := by
    simpa [prefixWord, tailWord_2148002, baseEnd_2148002] using wordTrace_append hprefix tailTrace_2148002
  have hstable : (prefixWord ++ tailWord_2148002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148002).length < 2 ^ (prefixWord ++ tailWord_2148002).sum := by decide
  have hdescent : baseEnd_2148002 < baseStart_2148002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148015 : List Nat := [1, 1, 2, 1, 2, 4, 4, 3, 1, 4]
def baseStart_2148015 : Nat := 118140960795 + 2148015 * 2 ^ 59
def prefixEnd_2148015 : Nat := 4983230072969 + 3 ^ 40 * 2148015 * 2
def baseEnd_2148015 : Nat := 367654716022506205044655

theorem tailTrace_2148015 : CollatzResearch.WordTrace tailWord_2148015 prefixEnd_2148015 367654716022506205044655 := by
  unfold tailWord_2148015
  simp only [CollatzResearch.WordTrace]
  refine ⟨78344543313115981600549499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52229695542077321067032999 78344543313115981600549499)
  ·
    refine ⟨117516814969673972400824249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78344543313115981600549499 117516814969673972400824249)
    ·
      refine ⟨88137611227255479300618187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117516814969673972400824249 88137611227255479300618187)
      ·
        refine ⟨132206416840883218950927281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88137611227255479300618187 132206416840883218950927281)
        ·
          refine ⟨99154812630662414213195461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132206416840883218950927281 99154812630662414213195461)
          ·
            refine ⟨18591527368249202664974149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99154812630662414213195461 18591527368249202664974149)
            ·
              refine ⟨3485911381546725499682653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18591527368249202664974149 3485911381546725499682653)
              ·
                refine ⟨1307216768080022062380995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3485911381546725499682653 1307216768080022062380995)
                ·
                  refine ⟨1960825152120033093571493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307216768080022062380995 1960825152120033093571493)
                  ·
                    refine ⟨367654716022506205044655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1960825152120033093571493 367654716022506205044655)
                    ·
                      rfl

theorem cell23_2148015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 1, 4].length) (baseStart_2148015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148015 prefixEnd_2148015 := by exact prefixLift 2148015
  have htrace : WordTrace (prefixWord ++ tailWord_2148015) baseStart_2148015 baseEnd_2148015 := by
    simpa [prefixWord, tailWord_2148015, baseEnd_2148015] using wordTrace_append hprefix tailTrace_2148015
  have hstable : (prefixWord ++ tailWord_2148015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148015).length < 2 ^ (prefixWord ++ tailWord_2148015).sum := by decide
  have hdescent : baseEnd_2148015 < baseStart_2148015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148022 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_2148022 : Nat := 118140960795 + 2148022 * 2 ^ 59
def prefixEnd_2148022 : Nat := 4983230072969 + 3 ^ 40 * 2148022 * 2
def baseEnd_2148022 : Nat := 1102967742432100087746433

theorem tailTrace_2148022 : CollatzResearch.WordTrace tailWord_2148022 prefixEnd_2148022 1102967742432100087746433 := by
  unfold tailWord_2148022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4896549914005663862253395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52229865749393747864036213 4896549914005663862253395)
  ·
    refine ⟨7344824871008495793380093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4896549914005663862253395 7344824871008495793380093)
    ·
      refine ⟨2754309326628185922517535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7344824871008495793380093 2754309326628185922517535)
      ·
        refine ⟨4131463989942278883776303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2754309326628185922517535 4131463989942278883776303)
        ·
          refine ⟨6197195984913418325664455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4131463989942278883776303 6197195984913418325664455)
          ·
            refine ⟨9295793977370127488496683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6197195984913418325664455 9295793977370127488496683)
            ·
              refine ⟨13943690966055191232745025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9295793977370127488496683 13943690966055191232745025)
              ·
                refine ⟨10457768224541393424558769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13943690966055191232745025 10457768224541393424558769)
                ·
                  refine ⟨7843326168406045068419077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10457768224541393424558769 7843326168406045068419077)
                  ·
                    refine ⟨1470623656576133450328577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7843326168406045068419077 1470623656576133450328577)
                    ·
                      refine ⟨1102967742432100087746433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470623656576133450328577 1102967742432100087746433)
                      ·
                        rfl

theorem cell23_2148022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_2148022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148022 prefixEnd_2148022 := by exact prefixLift 2148022
  have htrace : WordTrace (prefixWord ++ tailWord_2148022) baseStart_2148022 baseEnd_2148022 := by
    simpa [prefixWord, tailWord_2148022, baseEnd_2148022] using wordTrace_append hprefix tailTrace_2148022
  have hstable : (prefixWord ++ tailWord_2148022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148022).length < 2 ^ (prefixWord ++ tailWord_2148022).sum := by decide
  have hdescent : baseEnd_2148022 < baseStart_2148022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148028 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 6]
def baseStart_2148028 : Nat := 118140960795 + 2148028 * 2 ^ 59
def prefixEnd_2148028 : Nat := 4983230072969 + 3 ^ 40 * 2148028 * 2
def baseEnd_2148028 : Nat := 122552313701780784919045

theorem tailTrace_2148028 : CollatzResearch.WordTrace tailWord_2148028 prefixEnd_2148028 122552313701780784919045 := by
  unfold tailWord_2148028
  simp only [CollatzResearch.WordTrace]
  refine ⟨39172508731034442410386369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52230011641379256547181825 39172508731034442410386369)
  ·
    refine ⟨29379381548275831807789777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39172508731034442410386369 29379381548275831807789777)
    ·
      refine ⟨22034536161206873855842333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29379381548275831807789777 22034536161206873855842333)
      ·
        refine ⟨8262951060452577695940875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22034536161206873855842333 8262951060452577695940875)
        ·
          refine ⟨12394426590678866543911313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8262951060452577695940875 12394426590678866543911313)
          ·
            refine ⟨9295819943009149907933485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12394426590678866543911313 9295819943009149907933485)
            ·
              refine ⟨3485932478628431215475057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9295819943009149907933485 3485932478628431215475057)
              ·
                refine ⟨2614449358971323411606293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3485932478628431215475057 2614449358971323411606293)
                ·
                  refine ⟨122552313701780784919045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2614449358971323411606293 122552313701780784919045)
                  ·
                    rfl

theorem cell23_2148028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_2148028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148028 prefixEnd_2148028 := by exact prefixLift 2148028
  have htrace : WordTrace (prefixWord ++ tailWord_2148028) baseStart_2148028 baseEnd_2148028 := by
    simpa [prefixWord, tailWord_2148028, baseEnd_2148028] using wordTrace_append hprefix tailTrace_2148028
  have hstable : (prefixWord ++ tailWord_2148028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148028).length < 2 ^ (prefixWord ++ tailWord_2148028).sum := by decide
  have hdescent : baseEnd_2148028 < baseStart_2148028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148048 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 6, 3, 2]
def baseStart_2148048 : Nat := 118140960795 + 2148048 * 2 ^ 59
def prefixEnd_2148048 : Nat := 4983230072969 + 3 ^ 40 * 2148048 * 2
def baseEnd_2148048 : Nat := 1102981092929116986021313

theorem tailTrace_2148048 : CollatzResearch.WordTrace tailWord_2148048 prefixEnd_2148048 1102981092929116986021313 := by
  unfold tailWord_2148048
  simp only [CollatzResearch.WordTrace]
  refine ⟨39172873460998214118250399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52230497947997618824333865 39172873460998214118250399)
  ·
    refine ⟨58759310191497321177375599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39172873460998214118250399 58759310191497321177375599)
    ·
      refine ⟨88138965287245981766063399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58759310191497321177375599 88138965287245981766063399)
      ·
        refine ⟨132208447930868972649095099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88138965287245981766063399 132208447930868972649095099)
        ·
          refine ⟨198312671896303458973642649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132208447930868972649095099 198312671896303458973642649)
          ·
            refine ⟨148734503922227594230231987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198312671896303458973642649 148734503922227594230231987)
            ·
              refine ⟨223101755883341391345347981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148734503922227594230231987 223101755883341391345347981)
              ·
                refine ⟨83663158456253021754505493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223101755883341391345347981 83663158456253021754505493)
                ·
                  refine ⟨3921710552636860394742445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83663158456253021754505493 3921710552636860394742445)
                  ·
                    refine ⟨1470641457238822648028417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3921710552636860394742445 1470641457238822648028417)
                    ·
                      refine ⟨1102981092929116986021313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470641457238822648028417 1102981092929116986021313)
                      ·
                        rfl

theorem cell23_2148048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 3, 2].length) (baseStart_2148048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148048 prefixEnd_2148048 := by exact prefixLift 2148048
  have htrace : WordTrace (prefixWord ++ tailWord_2148048) baseStart_2148048 baseEnd_2148048 := by
    simpa [prefixWord, tailWord_2148048, baseEnd_2148048] using wordTrace_append hprefix tailTrace_2148048
  have hstable : (prefixWord ++ tailWord_2148048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148048).length < 2 ^ (prefixWord ++ tailWord_2148048).sum := by decide
  have hdescent : baseEnd_2148048 < baseStart_2148048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148058 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_2148058 : Nat := 118140960795 + 2148058 * 2 ^ 59
def prefixEnd_2148058 : Nat := 4983230072969 + 3 ^ 40 * 2148058 * 2
def baseEnd_2148058 : Nat := 367662075911887315632089

theorem tailTrace_2148058 : CollatzResearch.WordTrace tailWord_2148058 prefixEnd_2148058 367662075911887315632089 := by
  unfold tailWord_2148058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19586527912990049986091207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52230741101306799962909885 19586527912990049986091207)
  ·
    refine ⟨29379791869485074979136811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19586527912990049986091207 29379791869485074979136811)
    ·
      refine ⟨44069687804227612468705217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29379791869485074979136811 44069687804227612468705217)
      ·
        refine ⟨33052265853170709351528913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44069687804227612468705217 33052265853170709351528913)
        ·
          refine ⟨24789199389878032013646685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33052265853170709351528913 24789199389878032013646685)
          ·
            refine ⟨9295949771204262005117507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24789199389878032013646685 9295949771204262005117507)
            ·
              refine ⟨13943924656806393007676261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9295949771204262005117507 13943924656806393007676261)
              ·
                refine ⟨2614485873151198688939299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13943924656806393007676261 2614485873151198688939299)
                ·
                  refine ⟨3921728809726798033408949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614485873151198688939299 3921728809726798033408949)
                  ·
                    refine ⟨367662075911887315632089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3921728809726798033408949 367662075911887315632089)
                    ·
                      rfl

theorem cell23_2148058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_2148058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148058 prefixEnd_2148058 := by exact prefixLift 2148058
  have htrace : WordTrace (prefixWord ++ tailWord_2148058) baseStart_2148058 baseEnd_2148058 := by
    simpa [prefixWord, tailWord_2148058, baseEnd_2148058] using wordTrace_append hprefix tailTrace_2148058
  have hstable : (prefixWord ++ tailWord_2148058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148058).length < 2 ^ (prefixWord ++ tailWord_2148058).sum := by decide
  have hdescent : baseEnd_2148058 < baseStart_2148058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148091 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 4]
def baseStart_2148091 : Nat := 118140960795 + 2148091 * 2 ^ 59
def prefixEnd_2148091 : Nat := 4983230072969 + 3 ^ 40 * 2148091 * 2
def baseEnd_2148091 : Nat := 1103003172597260317783615

theorem tailTrace_2148091 : CollatzResearch.WordTrace tailWord_2148091 prefixEnd_2148091 1103003172597260317783615 := by
  unfold tailWord_2148091
  simp only [CollatzResearch.WordTrace]
  refine ⟨78347315260840646580316127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52231543507227097720210751 78347315260840646580316127)
  ·
    refine ⟨117520972891260969870474191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78347315260840646580316127 117520972891260969870474191)
    ·
      refine ⟨176281459336891454805711287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117520972891260969870474191 176281459336891454805711287)
      ·
        refine ⟨264422189005337182208566931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176281459336891454805711287 264422189005337182208566931)
        ·
          refine ⟨396633283508005773312850397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264422189005337182208566931 396633283508005773312850397)
          ·
            refine ⟨148737481315502164992318899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396633283508005773312850397 148737481315502164992318899)
            ·
              refine ⟨223106221973253247488478349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148737481315502164992318899 223106221973253247488478349)
              ·
                refine ⟨83664833239969967808179381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223106221973253247488478349 83664833239969967808179381)
                ·
                  refine ⟨7843578116247184482016817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83664833239969967808179381 7843578116247184482016817)
                  ·
                    refine ⟨5882683587185388361512613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7843578116247184482016817 5882683587185388361512613)
                    ·
                      refine ⟨1103003172597260317783615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5882683587185388361512613 1103003172597260317783615)
                      ·
                        rfl

theorem cell23_2148091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 4].length) (baseStart_2148091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148091 prefixEnd_2148091 := by exact prefixLift 2148091
  have htrace : WordTrace (prefixWord ++ tailWord_2148091) baseStart_2148091 baseEnd_2148091 := by
    simpa [prefixWord, tailWord_2148091, baseEnd_2148091] using wordTrace_append hprefix tailTrace_2148091
  have hstable : (prefixWord ++ tailWord_2148091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148091).length < 2 ^ (prefixWord ++ tailWord_2148091).sum := by decide
  have hdescent : baseEnd_2148091 < baseStart_2148091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148126 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2148126 : Nat := 118140960795 + 2148126 * 2 ^ 59
def prefixEnd_2148126 : Nat := 4983230072969 + 3 ^ 40 * 2148126 * 2
def baseEnd_2148126 : Nat := 367673714806722560281985

theorem tailTrace_2148126 : CollatzResearch.WordTrace tailWord_2148126 prefixEnd_2148126 367673714806722560281985 := by
  unfold tailWord_2148126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9793573976964230944730029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52232394543809231705226821 9793573976964230944730029)
  ·
    refine ⟨3672590241361586604273761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9793573976964230944730029 3672590241361586604273761)
    ·
      refine ⟨2754442681021189953205321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3672590241361586604273761 2754442681021189953205321)
      ·
        refine ⟨2065832010765892464903991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2754442681021189953205321 2065832010765892464903991)
        ·
          refine ⟨3098748016148838697355987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065832010765892464903991 3098748016148838697355987)
          ·
            refine ⟨4648122024223258046033981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3098748016148838697355987 4648122024223258046033981)
            ·
              refine ⟨1743045759083721767262743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4648122024223258046033981 1743045759083721767262743)
              ·
                refine ⟨2614568638625582650894115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1743045759083721767262743 2614568638625582650894115)
                ·
                  refine ⟨3921852957938373976341173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614568638625582650894115 3921852957938373976341173)
                  ·
                    refine ⟨367673714806722560281985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3921852957938373976341173 367673714806722560281985)
                    ·
                      rfl

theorem cell23_2148126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2148126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148126 prefixEnd_2148126 := by exact prefixLift 2148126
  have htrace : WordTrace (prefixWord ++ tailWord_2148126) baseStart_2148126 baseEnd_2148126 := by
    simpa [prefixWord, tailWord_2148126, baseEnd_2148126] using wordTrace_append hprefix tailTrace_2148126
  have hstable : (prefixWord ++ tailWord_2148126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148126).length < 2 ^ (prefixWord ++ tailWord_2148126).sum := by decide
  have hdescent : baseEnd_2148126 < baseStart_2148126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148146 : List Nat := [3, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2]
def baseStart_2148146 : Nat := 118140960795 + 2148146 * 2 ^ 59
def prefixEnd_2148146 : Nat := 4983230072969 + 3 ^ 40 * 2148146 * 2
def baseEnd_2148146 : Nat := 1103031414033257602595863

theorem tailTrace_2148146 : CollatzResearch.WordTrace tailWord_2148146 prefixEnd_2148146 1103031414033257602595863 := by
  unfold tailWord_2148146
  simp only [CollatzResearch.WordTrace]
  refine ⟨19587330318910347743392073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52232880850427593982378861 19587330318910347743392073)
  ·
    refine ⟨14690497739182760807544055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19587330318910347743392073 14690497739182760807544055)
    ·
      refine ⟨22035746608774141211316083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14690497739182760807544055 22035746608774141211316083)
      ·
        refine ⟨33053619913161211816974125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22035746608774141211316083 33053619913161211816974125)
        ·
          refine ⟨12395107467435454431365297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33053619913161211816974125 12395107467435454431365297)
          ·
            refine ⟨9296330600576590823523973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12395107467435454431365297 9296330600576590823523973)
            ·
              refine ⟨1743061987608110779410745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9296330600576590823523973 1743061987608110779410745)
              ·
                refine ⟨1307296490706083084558059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1743061987608110779410745 1307296490706083084558059)
                ·
                  refine ⟨1960944736059124626837089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307296490706083084558059 1960944736059124626837089)
                  ·
                    refine ⟨1470708552044343470127817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1960944736059124626837089 1470708552044343470127817)
                    ·
                      refine ⟨1103031414033257602595863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470708552044343470127817 1103031414033257602595863)
                      ·
                        rfl

theorem cell23_2148146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_2148146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148146 prefixEnd_2148146 := by exact prefixLift 2148146
  have htrace : WordTrace (prefixWord ++ tailWord_2148146) baseStart_2148146 baseEnd_2148146 := by
    simpa [prefixWord, tailWord_2148146, baseEnd_2148146] using wordTrace_append hprefix tailTrace_2148146
  have hstable : (prefixWord ++ tailWord_2148146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148146).length < 2 ^ (prefixWord ++ tailWord_2148146).sum := by decide
  have hdescent : baseEnd_2148146 < baseStart_2148146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148185 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 1, 4, 2]
def baseStart_2148185 : Nat := 118140960795 + 2148185 * 2 ^ 59
def prefixEnd_2148185 : Nat := 4983230072969 + 3 ^ 40 * 2148185 * 2
def baseEnd_2148185 : Nat := 1103051439778782950008183

theorem tailTrace_2148185 : CollatzResearch.WordTrace tailWord_2148185 prefixEnd_2148185 1103051439778782950008183 := by
  unfold tailWord_2148185
  simp only [CollatzResearch.WordTrace]
  refine ⟨78350743722500100634238009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52233829148333400422825339 78350743722500100634238009)
  ·
    refine ⟨58763057791875075475678507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78350743722500100634238009 58763057791875075475678507)
    ·
      refine ⟨88144586687812613213517761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58763057791875075475678507 88144586687812613213517761)
      ·
        refine ⟨66108440015859459910138321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88144586687812613213517761 66108440015859459910138321)
        ·
          refine ⟨49581330011894594932603741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66108440015859459910138321 49581330011894594932603741)
          ·
            refine ⟨18592998754460473099726403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49581330011894594932603741 18592998754460473099726403)
            ·
              refine ⟨27889498131690709649589605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18592998754460473099726403 27889498131690709649589605)
              ·
                refine ⟨5229280899692008059298051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27889498131690709649589605 5229280899692008059298051)
                ·
                  refine ⟨7843921349538012088947077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5229280899692008059298051 7843921349538012088947077)
                  ·
                    refine ⟨1470735253038377266677577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7843921349538012088947077 1470735253038377266677577)
                    ·
                      refine ⟨1103051439778782950008183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470735253038377266677577 1103051439778782950008183)
                      ·
                        rfl

theorem cell23_2148185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_2148185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148185 prefixEnd_2148185 := by exact prefixLift 2148185
  have htrace : WordTrace (prefixWord ++ tailWord_2148185) baseStart_2148185 baseEnd_2148185 := by
    simpa [prefixWord, tailWord_2148185, baseEnd_2148185] using wordTrace_append hprefix tailTrace_2148185
  have hstable : (prefixWord ++ tailWord_2148185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148185).length < 2 ^ (prefixWord ++ tailWord_2148185).sum := by decide
  have hdescent : baseEnd_2148185 < baseStart_2148185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148196 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 2, 1, 3]
def baseStart_2148196 : Nat := 118140960795 + 2148196 * 2 ^ 59
def prefixEnd_2148196 : Nat := 4983230072969 + 3 ^ 40 * 2148196 * 2
def baseEnd_2148196 : Nat := 1103057088065982406970633

theorem tailTrace_2148196 : CollatzResearch.WordTrace tailWord_2148196 prefixEnd_2148196 1103057088065982406970633 := by
  unfold tailWord_2148196
  simp only [CollatzResearch.WordTrace]
  refine ⟨39175572462730124756444221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52234096616973499675258961 39175572462730124756444221)
  ·
    refine ⟨14690839673523796783666583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39175572462730124756444221 14690839673523796783666583)
    ·
      refine ⟨22036259510285695175499875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14690839673523796783666583 22036259510285695175499875)
      ·
        refine ⟨33054389265428542763249813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22036259510285695175499875 33054389265428542763249813)
        ·
          refine ⟨1549424496816962942027335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33054389265428542763249813 1549424496816962942027335)
          ·
            refine ⟨2324136745225444413041003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549424496816962942027335 2324136745225444413041003)
            ·
              refine ⟨3486205117838166619561505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2324136745225444413041003 3486205117838166619561505)
              ·
                refine ⟨2614653838378624964671129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3486205117838166619561505 2614653838378624964671129)
                ·
                  refine ⟨1960990378783968723503347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2614653838378624964671129 1960990378783968723503347)
                  ·
                    refine ⟨2941485568175953085255021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1960990378783968723503347 2941485568175953085255021)
                    ·
                      refine ⟨1103057088065982406970633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2941485568175953085255021 1103057088065982406970633)
                      ·
                        rfl

theorem cell23_2148196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_2148196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148196 prefixEnd_2148196 := by exact prefixLift 2148196
  have htrace : WordTrace (prefixWord ++ tailWord_2148196) baseStart_2148196 baseEnd_2148196 := by
    simpa [prefixWord, tailWord_2148196, baseEnd_2148196] using wordTrace_append hprefix tailTrace_2148196
  have hstable : (prefixWord ++ tailWord_2148196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148196).length < 2 ^ (prefixWord ++ tailWord_2148196).sum := by decide
  have hdescent : baseEnd_2148196 < baseStart_2148196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148270 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2148270 : Nat := 118140960795 + 2148270 * 2 ^ 59
def prefixEnd_2148270 : Nat := 4983230072969 + 3 ^ 40 * 2148270 * 2
def baseEnd_2148270 : Nat := 1103095085634415117445293

theorem tailTrace_2148270 : CollatzResearch.WordTrace tailWord_2148270 prefixEnd_2148270 1103095085634415117445293 := by
  unfold tailWord_2148270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794230490899020018885283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52235895951461440100721509 9794230490899020018885283)
  ·
    refine ⟨14691345736348530028327925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9794230490899020018885283 14691345736348530028327925)
    ·
      refine ⟨1377313662782674690155743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14691345736348530028327925 1377313662782674690155743)
      ·
        refine ⟨2065970494174012035233615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377313662782674690155743 2065970494174012035233615)
        ·
          refine ⟨3098955741261018052850423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065970494174012035233615 3098955741261018052850423)
          ·
            refine ⟨4648433611891527079275635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3098955741261018052850423 4648433611891527079275635)
            ·
              refine ⟨6972650417837290618913453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648433611891527079275635 6972650417837290618913453)
              ·
                refine ⟨2614743906688983982092545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6972650417837290618913453 2614743906688983982092545)
                ·
                  refine ⟨1961057930016737986569409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2614743906688983982092545 1961057930016737986569409)
                  ·
                    refine ⟨1470793447512553489927057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1961057930016737986569409 1470793447512553489927057)
                    ·
                      refine ⟨1103095085634415117445293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470793447512553489927057 1103095085634415117445293)
                      ·
                        rfl

theorem cell23_2148270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2148270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148270 prefixEnd_2148270 := by exact prefixLift 2148270
  have htrace : WordTrace (prefixWord ++ tailWord_2148270) baseStart_2148270 baseEnd_2148270 := by
    simpa [prefixWord, tailWord_2148270, baseEnd_2148270] using wordTrace_append hprefix tailTrace_2148270
  have hstable : (prefixWord ++ tailWord_2148270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148270).length < 2 ^ (prefixWord ++ tailWord_2148270).sum := by decide
  have hdescent : baseEnd_2148270 < baseStart_2148270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148275 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 1, 6, 2]
def baseStart_2148275 : Nat := 118140960795 + 2148275 * 2 ^ 59
def prefixEnd_2148275 : Nat := 4983230072969 + 3 ^ 40 * 2148275 * 2
def baseEnd_2148275 : Nat := 1103097653037687597882769

theorem tailTrace_2148275 : CollatzResearch.WordTrace tailWord_2148275 prefixEnd_2148275 1103097653037687597882769 := by
  unfold tailWord_2148275
  simp only [CollatzResearch.WordTrace]
  refine ⟨78354026292174046005014279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52236017528116030670009519 78354026292174046005014279)
  ·
    refine ⟨117531039438261069007521419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78354026292174046005014279 117531039438261069007521419)
    ·
      refine ⟨176296559157391603511282129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117531039438261069007521419 176296559157391603511282129)
      ·
        refine ⟨132222419368043702633461597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176296559157391603511282129 132222419368043702633461597)
        ·
          refine ⟨49583407263016388487548099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132222419368043702633461597 49583407263016388487548099)
          ·
            refine ⟨74375110894524582731322149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49583407263016388487548099 74375110894524582731322149)
            ·
              refine ⟨13945333292723359262122903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74375110894524582731322149 13945333292723359262122903)
              ·
                refine ⟨20917999939085038893184355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13945333292723359262122903 20917999939085038893184355)
                ·
                  refine ⟨31376999908627558339776533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20917999939085038893184355 31376999908627558339776533)
                  ·
                    refine ⟨1470796870716916797177025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31376999908627558339776533 1470796870716916797177025)
                    ·
                      refine ⟨1103097653037687597882769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470796870716916797177025 1103097653037687597882769)
                      ·
                        rfl

theorem cell23_2148275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 6, 2].length) (baseStart_2148275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148275 prefixEnd_2148275 := by exact prefixLift 2148275
  have htrace : WordTrace (prefixWord ++ tailWord_2148275) baseStart_2148275 baseEnd_2148275 := by
    simpa [prefixWord, tailWord_2148275, baseEnd_2148275] using wordTrace_append hprefix tailTrace_2148275
  have hstable : (prefixWord ++ tailWord_2148275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148275).length < 2 ^ (prefixWord ++ tailWord_2148275).sum := by decide
  have hdescent : baseEnd_2148275 < baseStart_2148275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148298 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 10]
def baseStart_2148298 : Nat := 118140960795 + 2148298 * 2 ^ 59
def prefixEnd_2148298 : Nat := 4983230072969 + 3 ^ 40 * 2148298 * 2
def baseEnd_2148298 : Nat := 122567718121415667543907

theorem tailTrace_2148298 : CollatzResearch.WordTrace tailWord_2148298 prefixEnd_2148298 122567718121415667543907 := by
  unfold tailWord_2148298
  simp only [CollatzResearch.WordTrace]
  refine ⟨19588716292772680233275387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52236576780727147288734365 19588716292772680233275387)
  ·
    refine ⟨29383074439159020349913081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19588716292772680233275387 29383074439159020349913081)
    ·
      refine ⟨22037305829369265262434811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29383074439159020349913081 22037305829369265262434811)
      ·
        refine ⟨33055958744053897893652217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22037305829369265262434811 33055958744053897893652217)
        ·
          refine ⟨24791969058040423420239163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33055958744053897893652217 24791969058040423420239163)
          ·
            refine ⟨37187953587060635130358745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24791969058040423420239163 37187953587060635130358745)
            ·
              refine ⟨27890965190295476347769059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37187953587060635130358745 27890965190295476347769059)
              ·
                refine ⟨41836447785443214521653589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27890965190295476347769059 41836447785443214521653589)
                ·
                  refine ⟨122567718121415667543907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 41836447785443214521653589 122567718121415667543907)
                  ·
                    rfl

theorem cell23_2148298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_2148298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148298 prefixEnd_2148298 := by exact prefixLift 2148298
  have htrace : WordTrace (prefixWord ++ tailWord_2148298) baseStart_2148298 baseEnd_2148298 := by
    simpa [prefixWord, tailWord_2148298, baseEnd_2148298] using wordTrace_append hprefix tailTrace_2148298
  have hstable : (prefixWord ++ tailWord_2148298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148298).length < 2 ^ (prefixWord ++ tailWord_2148298).sum := by decide
  have hdescent : baseEnd_2148298 < baseStart_2148298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148319 : List Nat := [1, 1, 2, 3, 4, 2, 1, 4, 1, 4]
def baseStart_2148319 : Nat := 118140960795 + 2148319 * 2 ^ 59
def prefixEnd_2148319 : Nat := 4983230072969 + 3 ^ 40 * 2148319 * 2
def baseEnd_2148319 : Nat := 367706748728828475244189

theorem tailTrace_2148319 : CollatzResearch.WordTrace tailWord_2148319 prefixEnd_2148319 367706748728828475244189 := by
  unfold tailWord_2148319
  simp only [CollatzResearch.WordTrace]
  refine ⟨78355631104014641519616011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52237087402676427679744007 78355631104014641519616011)
  ·
    refine ⟨117533446656021962279424017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78355631104014641519616011 117533446656021962279424017)
    ·
      refine ⟨88150084992016471709568013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117533446656021962279424017 88150084992016471709568013)
      ·
        refine ⟨33056281872006176891088005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88150084992016471709568013 33056281872006176891088005)
        ·
          refine ⟨6198052851001158167079001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33056281872006176891088005 6198052851001158167079001)
          ·
            refine ⟨4648539638250868625309251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6198052851001158167079001 4648539638250868625309251)
            ·
              refine ⟨6972809457376302937963877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648539638250868625309251 6972809457376302937963877)
              ·
                refine ⟨1307401773258056800868227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6972809457376302937963877 1307401773258056800868227)
                ·
                  refine ⟨1961102659887085201302341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307401773258056800868227 1961102659887085201302341)
                  ·
                    refine ⟨367706748728828475244189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1961102659887085201302341 367706748728828475244189)
                    ·
                      rfl

theorem cell23_2148319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 1, 4].length) (baseStart_2148319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148319 prefixEnd_2148319 := by exact prefixLift 2148319
  have htrace : WordTrace (prefixWord ++ tailWord_2148319) baseStart_2148319 baseEnd_2148319 := by
    simpa [prefixWord, tailWord_2148319, baseEnd_2148319] using wordTrace_append hprefix tailTrace_2148319
  have hstable : (prefixWord ++ tailWord_2148319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148319).length < 2 ^ (prefixWord ++ tailWord_2148319).sum := by decide
  have hdescent : baseEnd_2148319 < baseStart_2148319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148345 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 3, 5]
def baseStart_2148345 : Nat := 118140960795 + 2148345 * 2 ^ 59
def prefixEnd_2148345 : Nat := 4983230072969 + 3 ^ 40 * 2148345 * 2
def baseEnd_2148345 : Nat := 367711198894500774669149

theorem tailTrace_2148345 : CollatzResearch.WordTrace tailWord_2148345 prefixEnd_2148345 367711198894500774669149 := by
  unfold tailWord_2148345
  simp only [CollatzResearch.WordTrace]
  refine ⟨78356579401920447960062489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52237719601280298640041659 78356579401920447960062489)
  ·
    refine ⟨58767434551440335970046867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78356579401920447960062489 58767434551440335970046867)
    ·
      refine ⟨88151151827160503955070301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58767434551440335970046867 88151151827160503955070301)
      ·
        refine ⟨33056681935185188983151363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88151151827160503955070301 33056681935185188983151363)
        ·
          refine ⟨49585022902777783474727045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33056681935185188983151363 49585022902777783474727045)
          ·
            refine ⟨9297191794270834401511321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49585022902777783474727045 9297191794270834401511321)
            ·
              refine ⟨6972893845703125801133491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9297191794270834401511321 6972893845703125801133491)
              ·
                refine ⟨10459340768554688701700237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6972893845703125801133491 10459340768554688701700237)
                ·
                  refine ⟨3922252788208008263137589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10459340768554688701700237 3922252788208008263137589)
                  ·
                    refine ⟨367711198894500774669149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3922252788208008263137589 367711198894500774669149)
                    ·
                      rfl

theorem cell23_2148345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_2148345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148345 prefixEnd_2148345 := by exact prefixLift 2148345
  have htrace : WordTrace (prefixWord ++ tailWord_2148345) baseStart_2148345 baseEnd_2148345 := by
    simpa [prefixWord, tailWord_2148345, baseEnd_2148345] using wordTrace_append hprefix tailTrace_2148345
  have hstable : (prefixWord ++ tailWord_2148345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148345).length < 2 ^ (prefixWord ++ tailWord_2148345).sum := by decide
  have hdescent : baseEnd_2148345 < baseStart_2148345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148352 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 2, 3, 2]
def baseStart_2148352 : Nat := 118140960795 + 2148352 * 2 ^ 59
def prefixEnd_2148352 : Nat := 4983230072969 + 3 ^ 40 * 2148352 * 2
def baseEnd_2148352 : Nat := 1103137191048083796619915

theorem tailTrace_2148352 : CollatzResearch.WordTrace tailWord_2148352 prefixEnd_2148352 1103137191048083796619915 := by
  unfold tailWord_2148352
  simp only [CollatzResearch.WordTrace]
  refine ⟨39178417356447544077783655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52237889808596725437044873 39178417356447544077783655)
  ·
    refine ⟨58767626034671316116675483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39178417356447544077783655 58767626034671316116675483)
    ·
      refine ⟨88151439052006974175013225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58767626034671316116675483 88151439052006974175013225)
      ·
        refine ⟨66113579289005230631259919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88151439052006974175013225 66113579289005230631259919)
        ·
          refine ⟨99170368933507845946889879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66113579289005230631259919 99170368933507845946889879)
          ·
            refine ⟨148755553400261768920334819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99170368933507845946889879 148755553400261768920334819)
            ·
              refine ⟨223133330100392653380502229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148755553400261768920334819 223133330100392653380502229)
              ·
                refine ⟨5229687424227952813605521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 223133330100392653380502229 5229687424227952813605521)
                ·
                  refine ⟨3922265568170964610204141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5229687424227952813605521 3922265568170964610204141)
                  ·
                    refine ⟨1470849588064111728826553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3922265568170964610204141 1470849588064111728826553)
                    ·
                      refine ⟨1103137191048083796619915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470849588064111728826553 1103137191048083796619915)
                      ·
                        rfl

theorem cell23_2148352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_2148352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148352 prefixEnd_2148352 := by exact prefixLift 2148352
  have htrace : WordTrace (prefixWord ++ tailWord_2148352) baseStart_2148352 baseEnd_2148352 := by
    simpa [prefixWord, tailWord_2148352, baseEnd_2148352] using wordTrace_append hprefix tailTrace_2148352
  have hstable : (prefixWord ++ tailWord_2148352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148352).length < 2 ^ (prefixWord ++ tailWord_2148352).sum := by decide
  have hdescent : baseEnd_2148352 < baseStart_2148352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148395 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 4]
def baseStart_2148395 : Nat := 118140960795 + 2148395 * 2 ^ 59
def prefixEnd_2148395 : Nat := 4983230072969 + 3 ^ 40 * 2148395 * 2
def baseEnd_2148395 : Nat := 1103159270716227128382217

theorem tailTrace_2148395 : CollatzResearch.WordTrace tailWord_2148395 prefixEnd_2148395 1103159270716227128382217 := by
  unfold tailWord_2148395
  simp only [CollatzResearch.WordTrace]
  refine ⟨78358403051739306499382639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52238935367826204332921759 78358403051739306499382639)
  ·
    refine ⟨117537604577608959749073959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78358403051739306499382639 117537604577608959749073959)
    ·
      refine ⟨176306406866413439623610939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117537604577608959749073959 176306406866413439623610939)
      ·
        refine ⟨264459610299620159435416409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176306406866413439623610939 264459610299620159435416409)
        ·
          refine ⟨198344707724715119576562307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264459610299620159435416409 198344707724715119576562307)
          ·
            refine ⟨297517061587072679364843461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198344707724715119576562307 297517061587072679364843461)
            ·
              refine ⟨55784449047576127380908149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 297517061587072679364843461 55784449047576127380908149)
              ·
                refine ⟨5229792098210261941960139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55784449047576127380908149 5229792098210261941960139)
                ·
                  refine ⟨7844688147315392912940209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5229792098210261941960139 7844688147315392912940209)
                  ·
                    refine ⟨5883516110486544684705157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7844688147315392912940209 5883516110486544684705157)
                    ·
                      refine ⟨1103159270716227128382217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5883516110486544684705157 1103159270716227128382217)
                      ·
                        rfl

theorem cell23_2148395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 4].length) (baseStart_2148395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148395 prefixEnd_2148395 := by exact prefixLift 2148395
  have htrace : WordTrace (prefixWord ++ tailWord_2148395) baseStart_2148395 baseEnd_2148395 := by
    simpa [prefixWord, tailWord_2148395, baseEnd_2148395] using wordTrace_append hprefix tailTrace_2148395
  have hstable : (prefixWord ++ tailWord_2148395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148395).length < 2 ^ (prefixWord ++ tailWord_2148395).sum := by decide
  have hdescent : baseEnd_2148395 < baseStart_2148395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148512 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 7]
def baseStart_2148512 : Nat := 118140960795 + 2148512 * 2 ^ 59
def prefixEnd_2148512 : Nat := 4983230072969 + 3 ^ 40 * 2148512 * 2
def baseEnd_2148512 : Nat := 122579927550311463402131

theorem tailTrace_2148512 : CollatzResearch.WordTrace tailWord_2148512 prefixEnd_2148512 122579927550311463402131 := by
  unfold tailWord_2148512
  simp only [CollatzResearch.WordTrace]
  refine ⟨39181335196157717740695895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52241780261543623654261193 39181335196157717740695895)
  ·
    refine ⟨58772002794236576611043843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39181335196157717740695895 58772002794236576611043843)
    ·
      refine ⟨88158004191354864916565765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58772002794236576611043843 88158004191354864916565765)
      ·
        refine ⟨16529625785879037171856081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88158004191354864916565765 16529625785879037171856081)
        ·
          refine ⟨12397219339409277878892061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16529625785879037171856081 12397219339409277878892061)
          ·
            refine ⟨4648957252278479204584523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12397219339409277878892061 4648957252278479204584523)
            ·
              refine ⟨6973435878417718806876785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648957252278479204584523 6973435878417718806876785)
              ·
                refine ⟨5230076908813289105157589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6973435878417718806876785 5230076908813289105157589)
                ·
                  refine ⟨122579927550311463402131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5230076908813289105157589 122579927550311463402131)
                  ·
                    rfl

theorem cell23_2148512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 7].length) (baseStart_2148512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148512 prefixEnd_2148512 := by exact prefixLift 2148512
  have htrace : WordTrace (prefixWord ++ tailWord_2148512) baseStart_2148512 baseEnd_2148512 := by
    simpa [prefixWord, tailWord_2148512, baseEnd_2148512] using wordTrace_append hprefix tailTrace_2148512
  have hstable : (prefixWord ++ tailWord_2148512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148512).length < 2 ^ (prefixWord ++ tailWord_2148512).sum := by decide
  have hdescent : baseEnd_2148512 < baseStart_2148512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148540 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 2, 2, 2]
def baseStart_2148540 : Nat := 118140960795 + 2148540 * 2 ^ 59
def prefixEnd_2148540 : Nat := 4983230072969 + 3 ^ 40 * 2148540 * 2
def baseEnd_2148540 : Nat := 1103233725411129061069051

theorem tailTrace_2148540 : CollatzResearch.WordTrace tailWord_2148540 prefixEnd_2148540 1103233725411129061069051 := by
  unfold tailWord_2148540
  simp only [CollatzResearch.WordTrace]
  refine ⟨39181845818106998131705537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52242461090809330842274049 39181845818106998131705537)
  ·
    refine ⟨29386384363580248598779153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39181845818106998131705537 29386384363580248598779153)
    ·
      refine ⟨22039788272685186449084365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29386384363580248598779153 22039788272685186449084365)
      ·
        refine ⟨8264920602256944918406637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22039788272685186449084365 8264920602256944918406637)
        ·
          refine ⟨3099345225846354344402489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8264920602256944918406637 3099345225846354344402489)
          ·
            refine ⟨2324508919384765758301867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3099345225846354344402489 2324508919384765758301867)
            ·
              refine ⟨3486763379077148637452801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2324508919384765758301867 3486763379077148637452801)
              ·
                refine ⟨2615072534307861478089601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3486763379077148637452801 2615072534307861478089601)
                ·
                  refine ⟨1961304400730896108567201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2615072534307861478089601 1961304400730896108567201)
                  ·
                    refine ⟨1470978300548172081425401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1961304400730896108567201 1470978300548172081425401)
                    ·
                      refine ⟨1103233725411129061069051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1470978300548172081425401 1103233725411129061069051)
                      ·
                        rfl

theorem cell23_2148540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_2148540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148540 prefixEnd_2148540 := by exact prefixLift 2148540
  have htrace : WordTrace (prefixWord ++ tailWord_2148540) baseStart_2148540 baseEnd_2148540 := by
    simpa [prefixWord, tailWord_2148540, baseEnd_2148540] using wordTrace_append hprefix tailTrace_2148540
  have hstable : (prefixWord ++ tailWord_2148540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148540).length < 2 ^ (prefixWord ++ tailWord_2148540).sum := by decide
  have hdescent : baseEnd_2148540 < baseStart_2148540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148546 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2148546 : Nat := 118140960795 + 2148546 * 2 ^ 59
def prefixEnd_2148546 : Nat := 4983230072969 + 3 ^ 40 * 2148546 * 2
def baseEnd_2148546 : Nat := 122581867366117337510447

theorem tailTrace_2148546 : CollatzResearch.WordTrace tailWord_2148546 prefixEnd_2148546 122581867366117337510447 := by
  unfold tailWord_2148546
  simp only [CollatzResearch.WordTrace]
  refine ⟨19590977618548064822032373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52242606982794839525419661 19590977618548064822032373)
  ·
    refine ⟨1836654151738881077065535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19590977618548064822032373 1836654151738881077065535)
    ·
      refine ⟨2754981227608321615598303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1836654151738881077065535 2754981227608321615598303)
      ·
        refine ⟨4132471841412482423397455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2754981227608321615598303 4132471841412482423397455)
        ·
          refine ⟨6198707762118723635096183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4132471841412482423397455 6198707762118723635096183)
          ·
            refine ⟨9298061643178085452644275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6198707762118723635096183 9298061643178085452644275)
            ·
              refine ⟨13947092464767128178966413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9298061643178085452644275 13947092464767128178966413)
              ·
                refine ⟨5230159674287673067112405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13947092464767128178966413 5230159674287673067112405)
                ·
                  refine ⟨122581867366117337510447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5230159674287673067112405 122581867366117337510447)
                  ·
                    rfl

theorem cell23_2148546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2148546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148546 prefixEnd_2148546 := by exact prefixLift 2148546
  have htrace : WordTrace (prefixWord ++ tailWord_2148546) baseStart_2148546 baseEnd_2148546 := by
    simpa [prefixWord, tailWord_2148546, baseEnd_2148546] using wordTrace_append hprefix tailTrace_2148546
  have hstable : (prefixWord ++ tailWord_2148546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148546).length < 2 ^ (prefixWord ++ tailWord_2148546).sum := by decide
  have hdescent : baseEnd_2148546 < baseStart_2148546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148602 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 8]
def baseStart_2148602 : Nat := 118140960795 + 2148602 * 2 ^ 59
def prefixEnd_2148602 : Nat := 4983230072969 + 3 ^ 40 * 2148602 * 2
def baseEnd_2148602 : Nat := 122585062356856424277085

theorem tailTrace_2148602 : CollatzResearch.WordTrace tailWord_2148602 prefixEnd_2148602 122585062356856424277085 := by
  unfold tailWord_2148602
  simp only [CollatzResearch.WordTrace]
  refine ⟨19591488240497345213042015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52243968641326253901445373 19591488240497345213042015)
  ·
    refine ⟨29387232360746017819563023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19591488240497345213042015 29387232360746017819563023)
    ·
      refine ⟨44080848541119026729344535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29387232360746017819563023 44080848541119026729344535)
      ·
        refine ⟨66121272811678540094016803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44080848541119026729344535 66121272811678540094016803)
        ·
          refine ⟨99181909217517810141025205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66121272811678540094016803 99181909217517810141025205)
          ·
            refine ⟨9298303989142294700721113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99181909217517810141025205 9298303989142294700721113)
            ·
              refine ⟨6973727991856721025540835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9298303989142294700721113 6973727991856721025540835)
              ·
                refine ⟨10460591987785081538311253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6973727991856721025540835 10460591987785081538311253)
                ·
                  refine ⟨122585062356856424277085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10460591987785081538311253 122585062356856424277085)
                  ·
                    rfl

theorem cell23_2148602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_2148602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148602 prefixEnd_2148602 := by exact prefixLift 2148602
  have htrace : WordTrace (prefixWord ++ tailWord_2148602) baseStart_2148602 baseEnd_2148602 := by
    simpa [prefixWord, tailWord_2148602, baseEnd_2148602] using wordTrace_append hprefix tailTrace_2148602
  have hstable : (prefixWord ++ tailWord_2148602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148602).length < 2 ^ (prefixWord ++ tailWord_2148602).sum := by decide
  have hdescent : baseEnd_2148602 < baseStart_2148602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148653 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 6]
def baseStart_2148653 : Nat := 118140960795 + 2148653 * 2 ^ 59
def prefixEnd_2148653 : Nat := 4983230072969 + 3 ^ 40 * 2148653 * 2
def baseEnd_2148653 : Nat := 122587972080565235439559

theorem tailTrace_2148653 : CollatzResearch.WordTrace tailWord_2148653 prefixEnd_2148653 122587972080565235439559 := by
  unfold tailWord_2148653
  simp only [CollatzResearch.WordTrace]
  refine ⟨78367813084804616562274613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52245208723203077708183075 78367813084804616562274613)
  ·
    refine ⟨7346982476700432802713245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78367813084804616562274613 7346982476700432802713245)
    ·
      refine ⟨2755118428762662301017467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7346982476700432802713245 2755118428762662301017467)
      ·
        refine ⟨4132677643143993451526201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2755118428762662301017467 4132677643143993451526201)
        ·
          refine ⟨3099508232357995088644651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4132677643143993451526201 3099508232357995088644651)
          ·
            refine ⟨4649262348536992632966977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099508232357995088644651 4649262348536992632966977)
            ·
              refine ⟨3486946761402744474725233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4649262348536992632966977 3486946761402744474725233)
              ·
                refine ⟨2615210071052058356043925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3486946761402744474725233 2615210071052058356043925)
                ·
                  refine ⟨122587972080565235439559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2615210071052058356043925 122587972080565235439559)
                  ·
                    rfl

theorem cell23_2148653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_2148653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148653 prefixEnd_2148653 := by exact prefixLift 2148653
  have htrace : WordTrace (prefixWord ++ tailWord_2148653) baseStart_2148653 baseEnd_2148653 := by
    simpa [prefixWord, tailWord_2148653, baseEnd_2148653] using wordTrace_append hprefix tailTrace_2148653
  have hstable : (prefixWord ++ tailWord_2148653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148653).length < 2 ^ (prefixWord ++ tailWord_2148653).sum := by decide
  have hdescent : baseEnd_2148653 < baseStart_2148653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148657 : List Nat := [1, 2, 2, 3, 5, 1, 2, 2, 1, 4]
def baseStart_2148657 : Nat := 118140960795 + 2148657 * 2 ^ 59
def prefixEnd_2148657 : Nat := 4983230072969 + 3 ^ 40 * 2148657 * 2
def baseEnd_2148657 : Nat := 367764600882568367768671

theorem tailTrace_2148657 : CollatzResearch.WordTrace tailWord_2148657 prefixEnd_2148657 367764600882568367768671 := by
  unfold tailWord_2148657
  simp only [CollatzResearch.WordTrace]
  refine ⟨78367958976790125245420225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52245305984526750163613483 78367958976790125245420225)
  ·
    refine ⟨58775969232592593934065169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78367958976790125245420225 58775969232592593934065169)
    ·
      refine ⟨44081976924444445450548877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58775969232592593934065169 44081976924444445450548877)
      ·
        refine ⟨16530741346666667043955829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44081976924444445450548877 16530741346666667043955829)
        ·
          refine ⟨1549757001250000035370859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16530741346666667043955829 1549757001250000035370859)
          ·
            refine ⟨2324635501875000053056289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549757001250000035370859 2324635501875000053056289)
            ·
              refine ⟨1743476626406250039792217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2324635501875000053056289 1743476626406250039792217)
              ·
                refine ⟨1307607469804687529844163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1743476626406250039792217 1307607469804687529844163)
                ·
                  refine ⟨1961411204707031294766245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307607469804687529844163 1961411204707031294766245)
                  ·
                    refine ⟨367764600882568367768671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1961411204707031294766245 367764600882568367768671)
                    ·
                      rfl

theorem cell23_2148657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_2148657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148657 prefixEnd_2148657 := by exact prefixLift 2148657
  have htrace : WordTrace (prefixWord ++ tailWord_2148657) baseStart_2148657 baseEnd_2148657 := by
    simpa [prefixWord, tailWord_2148657, baseEnd_2148657] using wordTrace_append hprefix tailTrace_2148657
  have hstable : (prefixWord ++ tailWord_2148657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148657).length < 2 ^ (prefixWord ++ tailWord_2148657).sum := by decide
  have hdescent : baseEnd_2148657 < baseStart_2148657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148679 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 1, 6]
def baseStart_2148679 : Nat := 118140960795 + 2148679 * 2 ^ 59
def prefixEnd_2148679 : Nat := 4983230072969 + 3 ^ 40 * 2148679 * 2
def baseEnd_2148679 : Nat := 367768366407368005743637

theorem tailTrace_2148679 : CollatzResearch.WordTrace tailWord_2148679 prefixEnd_2148679 367768366407368005743637 := by
  unfold tailWord_2148679
  simp only [CollatzResearch.WordTrace]
  refine ⟨78368761382710423002721091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52245840921806948668480727 78368761382710423002721091)
  ·
    refine ⟨117553142074065634504081637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78368761382710423002721091 117553142074065634504081637)
    ·
      refine ⟨22041214138887306469515307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117553142074065634504081637 22041214138887306469515307)
      ·
        refine ⟨33061821208330959704272961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22041214138887306469515307 33061821208330959704272961)
        ·
          refine ⟨24796365906248219778204721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33061821208330959704272961 24796365906248219778204721)
          ·
            refine ⟨18597274429686164833653541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24796365906248219778204721 18597274429686164833653541)
            ·
              refine ⟨3486988955566155906310039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18597274429686164833653541 3486988955566155906310039)
              ·
                refine ⟨5230483433349233859465059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3486988955566155906310039 5230483433349233859465059)
                ·
                  refine ⟨7845725150023850789197589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5230483433349233859465059 7845725150023850789197589)
                  ·
                    refine ⟨367768366407368005743637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7845725150023850789197589 367768366407368005743637)
                    ·
                      rfl

theorem cell23_2148679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_2148679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148679 prefixEnd_2148679 := by exact prefixLift 2148679
  have htrace : WordTrace (prefixWord ++ tailWord_2148679) baseStart_2148679 baseEnd_2148679 := by
    simpa [prefixWord, tailWord_2148679, baseEnd_2148679] using wordTrace_append hprefix tailTrace_2148679
  have hstable : (prefixWord ++ tailWord_2148679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148679).length < 2 ^ (prefixWord ++ tailWord_2148679).sum := by decide
  have hdescent : baseEnd_2148679 < baseStart_2148679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148720 : List Nat := [2, 1, 1, 1, 4, 3, 2, 4, 1, 2, 2]
def baseStart_2148720 : Nat := 118140960795 + 2148720 * 2 ^ 59
def prefixEnd_2148720 : Nat := 4983230072969 + 3 ^ 40 * 2148720 * 2
def baseEnd_2148720 : Nat := 1103326151928938356818223

theorem tailTrace_2148720 : CollatzResearch.WordTrace tailWord_2148720 prefixEnd_2148720 1103326151928938356818223 := by
  unfold tailWord_2148720
  simp only [CollatzResearch.WordTrace]
  refine ⟨39185128387780943502481807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52246837850374591336642409 39185128387780943502481807)
  ·
    refine ⟨58777692581671415253722711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39185128387780943502481807 58777692581671415253722711)
    ·
      refine ⟨88166538872507122880584067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58777692581671415253722711 88166538872507122880584067)
      ·
        refine ⟨132249808308760684320876101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88166538872507122880584067 132249808308760684320876101)
        ·
          refine ⟨24796839057892628310164269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132249808308760684320876101 24796839057892628310164269)
          ·
            refine ⟨9298814646709735616311601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24796839057892628310164269 9298814646709735616311601)
            ·
              refine ⟨6974110985032301712233701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9298814646709735616311601 6974110985032301712233701)
              ·
                refine ⟨1307645809693556571043819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6974110985032301712233701 1307645809693556571043819)
                ·
                  refine ⟨1961468714540334856565729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307645809693556571043819 1961468714540334856565729)
                  ·
                    refine ⟨1471101535905251142424297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1961468714540334856565729 1471101535905251142424297)
                    ·
                      refine ⟨1103326151928938356818223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471101535905251142424297 1103326151928938356818223)
                      ·
                        rfl

theorem cell23_2148720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 1, 2, 2].length) (baseStart_2148720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148720 prefixEnd_2148720 := by exact prefixLift 2148720
  have htrace : WordTrace (prefixWord ++ tailWord_2148720) baseStart_2148720 baseEnd_2148720 := by
    simpa [prefixWord, tailWord_2148720, baseEnd_2148720] using wordTrace_append hprefix tailTrace_2148720
  have hstable : (prefixWord ++ tailWord_2148720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148720).length < 2 ^ (prefixWord ++ tailWord_2148720).sum := by decide
  have hdescent : baseEnd_2148720 < baseStart_2148720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148796 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2148796 : Nat := 118140960795 + 2148796 * 2 ^ 59
def prefixEnd_2148796 : Nat := 4983230072969 + 3 ^ 40 * 2148796 * 2
def baseEnd_2148796 : Nat := 1103365176458680059467873

theorem tailTrace_2148796 : CollatzResearch.WordTrace tailWord_2148796 prefixEnd_2148796 1103365176458680059467873 := by
  unfold tailWord_2148796
  simp only [CollatzResearch.WordTrace]
  refine ⟨39186514361643275992365121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52248685815524367989820161 39186514361643275992365121)
  ·
    refine ⟨29389885771232456994273841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39186514361643275992365121 29389885771232456994273841)
    ·
      refine ⟨22042414328424342745705381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29389885771232456994273841 22042414328424342745705381)
      ·
        refine ⟨4132952686579564264819759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22042414328424342745705381 4132952686579564264819759)
        ·
          refine ⟨6199429029869346397229639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4132952686579564264819759 6199429029869346397229639)
          ·
            refine ⟨9299143544804019595844459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6199429029869346397229639 9299143544804019595844459)
            ·
              refine ⟨13948715317206029393766689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9299143544804019595844459 13948715317206029393766689)
              ·
                refine ⟨10461536487904522045325017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13948715317206029393766689 10461536487904522045325017)
                ·
                  refine ⟨7846152365928391533993763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10461536487904522045325017 7846152365928391533993763)
                  ·
                    refine ⟨11769228548892587300990645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7846152365928391533993763 11769228548892587300990645)
                    ·
                      refine ⟨1103365176458680059467873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11769228548892587300990645 1103365176458680059467873)
                      ·
                        rfl

theorem cell23_2148796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2148796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148796 prefixEnd_2148796 := by exact prefixLift 2148796
  have htrace : WordTrace (prefixWord ++ tailWord_2148796) baseStart_2148796 baseEnd_2148796 := by
    simpa [prefixWord, tailWord_2148796, baseEnd_2148796] using wordTrace_append hprefix tailTrace_2148796
  have hstable : (prefixWord ++ tailWord_2148796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148796).length < 2 ^ (prefixWord ++ tailWord_2148796).sum := by decide
  have hdescent : baseEnd_2148796 < baseStart_2148796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148826 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3]
def baseStart_2148826 : Nat := 118140960795 + 2148826 * 2 ^ 59
def prefixEnd_2148826 : Nat := 4983230072969 + 3 ^ 40 * 2148826 * 2
def baseEnd_2148826 : Nat := 1103380580878314942092735

theorem tailTrace_2148826 : CollatzResearch.WordTrace tailWord_2148826 prefixEnd_2148826 1103380580878314942092735 := by
  unfold tailWord_2148826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19593530728294466777080583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52249415275451911405548221 19593530728294466777080583)
  ·
    refine ⟨29390296092441700165620875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19593530728294466777080583 29390296092441700165620875)
    ·
      refine ⟨44085444138662550248431313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29390296092441700165620875 44085444138662550248431313)
      ·
        refine ⟨33064083103996912686323485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44085444138662550248431313 33064083103996912686323485)
        ·
          refine ⟨12399031163998842257371307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33064083103996912686323485 12399031163998842257371307)
          ·
            refine ⟨18598546745998263386056961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12399031163998842257371307 18598546745998263386056961)
            ·
              refine ⟨13948910059498697539542721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18598546745998263386056961 13948910059498697539542721)
              ·
                refine ⟨10461682544624023154657041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13948910059498697539542721 10461682544624023154657041)
                ·
                  refine ⟨7846261908468017365992781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10461682544624023154657041 7846261908468017365992781)
                  ·
                    refine ⟨2942348215675506512247293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7846261908468017365992781 2942348215675506512247293)
                    ·
                      refine ⟨1103380580878314942092735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2942348215675506512247293 1103380580878314942092735)
                      ·
                        rfl

theorem cell23_2148826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_2148826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148826 prefixEnd_2148826 := by exact prefixLift 2148826
  have htrace : WordTrace (prefixWord ++ tailWord_2148826) baseStart_2148826 baseEnd_2148826 := by
    simpa [prefixWord, tailWord_2148826, baseEnd_2148826] using wordTrace_append hprefix tailTrace_2148826
  have hstable : (prefixWord ++ tailWord_2148826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148826).length < 2 ^ (prefixWord ++ tailWord_2148826).sum := by decide
  have hdescent : baseEnd_2148826 < baseStart_2148826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148879 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_2148879 : Nat := 118140960795 + 2148879 * 2 ^ 59
def prefixEnd_2148879 : Nat := 4983230072969 + 3 ^ 40 * 2148879 * 2
def baseEnd_2148879 : Nat := 1103407795353003234729991

theorem tailTrace_2148879 : CollatzResearch.WordTrace tailWord_2148879 prefixEnd_2148879 1103407795353003234729991 := by
  unfold tailWord_2148879
  simp only [CollatzResearch.WordTrace]
  refine ⟨78376055981985857160001691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52250703987990571440001127 78376055981985857160001691)
  ·
    refine ⟨117564083972978785740002537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78376055981985857160001691 117564083972978785740002537)
    ·
      refine ⟨88173062979734089305001903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117564083972978785740002537 88173062979734089305001903)
      ·
        refine ⟨132259594469601133957502855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88173062979734089305001903 132259594469601133957502855)
        ·
          refine ⟨198389391704401700936254283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132259594469601133957502855 198389391704401700936254283)
          ·
            refine ⟨297584087556602551404381425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198389391704401700936254283 297584087556602551404381425)
            ·
              refine ⟨223188065667451913553286069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297584087556602551404381425 223188065667451913553286069)
              ·
                refine ⟨20923881156323616895620569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223188065667451913553286069 20923881156323616895620569)
                ·
                  refine ⟨15692910867242712671715427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20923881156323616895620569 15692910867242712671715427)
                  ·
                    refine ⟨23539366300864069007573141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15692910867242712671715427 23539366300864069007573141)
                    ·
                      refine ⟨1103407795353003234729991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23539366300864069007573141 1103407795353003234729991)
                      ·
                        rfl

theorem cell23_2148879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_2148879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148879 prefixEnd_2148879 := by exact prefixLift 2148879
  have htrace : WordTrace (prefixWord ++ tailWord_2148879) baseStart_2148879 baseEnd_2148879 := by
    simpa [prefixWord, tailWord_2148879, baseEnd_2148879] using wordTrace_append hprefix tailTrace_2148879
  have hstable : (prefixWord ++ tailWord_2148879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148879).length < 2 ^ (prefixWord ++ tailWord_2148879).sum := by decide
  have hdescent : baseEnd_2148879 < baseStart_2148879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148889 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 8]
def baseStart_2148889 : Nat := 118140960795 + 2148889 * 2 ^ 59
def prefixEnd_2148889 : Nat := 4983230072969 + 3 ^ 40 * 2148889 * 2
def baseEnd_2148889 : Nat := 122601436684394243956105

theorem tailTrace_2148889 : CollatzResearch.WordTrace tailWord_2148889 prefixEnd_2148889 122601436684394243956105 := by
  unfold tailWord_2148889
  simp only [CollatzResearch.WordTrace]
  refine ⟨78376420711949628867865721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52250947141299752578577147 78376420711949628867865721)
  ·
    refine ⟨58782315533962221650899291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78376420711949628867865721 58782315533962221650899291)
    ·
      refine ⟨88173473300943332476348937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58782315533962221650899291 88173473300943332476348937)
      ·
        refine ⟨66130104975707499357261703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88173473300943332476348937 66130104975707499357261703)
        ·
          refine ⟨99195157463561249035892555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66130104975707499357261703 99195157463561249035892555)
          ·
            refine ⟨148792736195341873553838833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99195157463561249035892555 148792736195341873553838833)
            ·
              refine ⟨111594552146506405165379125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148792736195341873553838833 111594552146506405165379125)
              ·
                refine ⟨10461989263734975484254293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111594552146506405165379125 10461989263734975484254293)
                ·
                  refine ⟨122601436684394243956105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10461989263734975484254293 122601436684394243956105)
                  ·
                    rfl

theorem cell23_2148889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 8].length) (baseStart_2148889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148889 prefixEnd_2148889 := by exact prefixLift 2148889
  have htrace : WordTrace (prefixWord ++ tailWord_2148889) baseStart_2148889 baseEnd_2148889 := by
    simpa [prefixWord, tailWord_2148889, baseEnd_2148889] using wordTrace_append hprefix tailTrace_2148889
  have hstable : (prefixWord ++ tailWord_2148889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148889).length < 2 ^ (prefixWord ++ tailWord_2148889).sum := by decide
  have hdescent : baseEnd_2148889 < baseStart_2148889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148893 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2148893 : Nat := 118140960795 + 2148893 * 2 ^ 59
def prefixEnd_2148893 : Nat := 4983230072969 + 3 ^ 40 * 2148893 * 2
def baseEnd_2148893 : Nat := 367804994694055393318309

theorem tailTrace_2148893 : CollatzResearch.WordTrace tailWord_2148893 prefixEnd_2148893 367804994694055393318309 := by
  unfold tailWord_2148893
  simp only [CollatzResearch.WordTrace]
  refine ⟨78376566603935137551011333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52251044402623425034007555 78376566603935137551011333)
  ·
    refine ⟨14695606238237838290814625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78376566603935137551011333 14695606238237838290814625)
    ·
      refine ⟨11021704678678378718110969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14695606238237838290814625 11021704678678378718110969)
      ·
        refine ⟨8266278509008784038583227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11021704678678378718110969 8266278509008784038583227)
        ·
          refine ⟨12399417763513176057874841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8266278509008784038583227 12399417763513176057874841)
          ·
            refine ⟨9299563322634882043406131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12399417763513176057874841 9299563322634882043406131)
            ·
              refine ⟨13949344983952323065109197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9299563322634882043406131 13949344983952323065109197)
              ·
                refine ⟨5231004368982121149415949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13949344983952323065109197 5231004368982121149415949)
                ·
                  refine ⟨1961626638368295431030981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5231004368982121149415949 1961626638368295431030981)
                  ·
                    refine ⟨367804994694055393318309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1961626638368295431030981 367804994694055393318309)
                    ·
                      rfl

theorem cell23_2148893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2148893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148893 prefixEnd_2148893 := by exact prefixLift 2148893
  have htrace : WordTrace (prefixWord ++ tailWord_2148893) baseStart_2148893 baseEnd_2148893 := by
    simpa [prefixWord, tailWord_2148893, baseEnd_2148893] using wordTrace_append hprefix tailTrace_2148893
  have hstable : (prefixWord ++ tailWord_2148893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148893).length < 2 ^ (prefixWord ++ tailWord_2148893).sum := by decide
  have hdescent : baseEnd_2148893 < baseStart_2148893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148943 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 4, 3, 2]
def baseStart_2148943 : Nat := 118140960795 + 2148943 * 2 ^ 59
def prefixEnd_2148943 : Nat := 4983230072969 + 3 ^ 40 * 2148943 * 2
def baseEnd_2148943 : Nat := 1103440658114890984329697

theorem tailTrace_2148943 : CollatzResearch.WordTrace tailWord_2148943 prefixEnd_2148943 1103440658114890984329697 := by
  unfold tailWord_2148943
  simp only [CollatzResearch.WordTrace]
  refine ⟨78378390253753996090331483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52252260169169330726887655 78378390253753996090331483)
  ·
    refine ⟨117567585380630994135497225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78378390253753996090331483 117567585380630994135497225)
    ·
      refine ⟨88175689035473245601622919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117567585380630994135497225 88175689035473245601622919)
      ·
        refine ⟨132263533553209868402434379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88175689035473245601622919 132263533553209868402434379)
        ·
          refine ⟨198395300329814802603651569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132263533553209868402434379 198395300329814802603651569)
          ·
            refine ⟨148796475247361101952738677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198395300329814802603651569 148796475247361101952738677)
            ·
              refine ⟨13949669554440103308069251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148796475247361101952738677 13949669554440103308069251)
              ·
                refine ⟨20924504331660154962103877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13949669554440103308069251 20924504331660154962103877)
                ·
                  refine ⟨3923344562186279055394477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20924504331660154962103877 3923344562186279055394477)
                  ·
                    refine ⟨1471254210819854645772929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3923344562186279055394477 1471254210819854645772929)
                    ·
                      refine ⟨1103440658114890984329697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471254210819854645772929 1103440658114890984329697)
                      ·
                        rfl

theorem cell23_2148943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 3, 2].length) (baseStart_2148943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148943 prefixEnd_2148943 := by exact prefixLift 2148943
  have htrace : WordTrace (prefixWord ++ tailWord_2148943) baseStart_2148943 baseEnd_2148943 := by
    simpa [prefixWord, tailWord_2148943, baseEnd_2148943] using wordTrace_append hprefix tailTrace_2148943
  have hstable : (prefixWord ++ tailWord_2148943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148943).length < 2 ^ (prefixWord ++ tailWord_2148943).sum := by decide
  have hdescent : baseEnd_2148943 < baseStart_2148943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148996 : List Nat := [2, 3, 2, 1, 3, 12]
def baseStart_2148996 : Nat := 118140960795 + 2148996 * 2 ^ 59
def prefixEnd_2148996 : Nat := 4983230072969 + 3 ^ 40 * 2148996 * 2
def baseEnd_2148996 : Nat := 4541020051808968217971

theorem tailTrace_2148996 : CollatzResearch.WordTrace tailWord_2148996 prefixEnd_2148996 4541020051808968217971 := by
  unfold tailWord_2148996
  simp only [CollatzResearch.WordTrace]
  refine ⟨39190161661280993071005421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52253548881707990761340561 39190161661280993071005421)
  ·
    refine ⟨14696310622980372401627033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39190161661280993071005421 14696310622980372401627033)
    ·
      refine ⟨11022232967235279301220275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14696310622980372401627033 11022232967235279301220275)
      ·
        refine ⟨16533349450852918951830413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11022232967235279301220275 16533349450852918951830413)
        ·
          refine ⟨6200006044069844606936405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16533349450852918951830413 6200006044069844606936405)
          ·
            refine ⟨4541020051808968217971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6200006044069844606936405 4541020051808968217971)
            ·
              rfl

theorem cell23_2148996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 12].length) (baseStart_2148996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2148996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2148996 prefixEnd_2148996 := by exact prefixLift 2148996
  have htrace : WordTrace (prefixWord ++ tailWord_2148996) baseStart_2148996 baseEnd_2148996 := by
    simpa [prefixWord, tailWord_2148996, baseEnd_2148996] using wordTrace_append hprefix tailTrace_2148996
  have hstable : (prefixWord ++ tailWord_2148996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148996).length < 2 ^ (prefixWord ++ tailWord_2148996).sum := by decide
  have hdescent : baseEnd_2148996 < baseStart_2148996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149007 : List Nat := [1, 1, 2, 1, 1, 1, 1, 10, 1, 2, 2]
def baseStart_2149007 : Nat := 118140960795 + 2149007 * 2 ^ 59
def prefixEnd_2149007 : Nat := 4983230072969 + 3 ^ 40 * 2149007 * 2
def baseEnd_2149007 : Nat := 1103473520876778733929403

theorem tailTrace_2149007 : CollatzResearch.WordTrace tailWord_2149007 prefixEnd_2149007 1103473520876778733929403 := by
  unfold tailWord_2149007
  simp only [CollatzResearch.WordTrace]
  refine ⟨78380724525522135020661275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52253816350348090013774183 78380724525522135020661275)
  ·
    refine ⟨117571086788283202530991913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78380724525522135020661275 117571086788283202530991913)
    ·
      refine ⟨88178315091212401898243935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117571086788283202530991913 88178315091212401898243935)
      ·
        refine ⟨132267472636818602847365903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88178315091212401898243935 132267472636818602847365903)
        ·
          refine ⟨198401208955227904271048855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132267472636818602847365903 198401208955227904271048855)
          ·
            refine ⟨297601813432841856406573283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198401208955227904271048855 297601813432841856406573283)
            ·
              refine ⟨446402720149262784609859925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297601813432841856406573283 446402720149262784609859925)
              ·
                refine ⟨1307820469187293314286699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 446402720149262784609859925 1307820469187293314286699)
                ·
                  refine ⟨1961730703780939971430049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307820469187293314286699 1961730703780939971430049)
                  ·
                    refine ⟨1471298027835704978572537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1961730703780939971430049 1471298027835704978572537)
                    ·
                      refine ⟨1103473520876778733929403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471298027835704978572537 1103473520876778733929403)
                      ·
                        rfl

theorem cell23_2149007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 1, 2, 2].length) (baseStart_2149007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149007 prefixEnd_2149007 := by exact prefixLift 2149007
  have htrace : WordTrace (prefixWord ++ tailWord_2149007) baseStart_2149007 baseEnd_2149007 := by
    simpa [prefixWord, tailWord_2149007, baseEnd_2149007] using wordTrace_append hprefix tailTrace_2149007
  have hstable : (prefixWord ++ tailWord_2149007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149007).length < 2 ^ (prefixWord ++ tailWord_2149007).sum := by decide
  have hdescent : baseEnd_2149007 < baseStart_2149007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149010 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2149010 : Nat := 118140960795 + 2149010 * 2 ^ 59
def prefixEnd_2149010 : Nat := 4983230072969 + 3 ^ 40 * 2149010 * 2
def baseEnd_2149010 : Nat := 1103475061318742222191889

theorem tailTrace_2149010 : CollatzResearch.WordTrace tailWord_2149010 prefixEnd_2149010 1103475061318742222191889 := by
  unfold tailWord_2149010
  simp only [CollatzResearch.WordTrace]
  refine ⟨19595208486127816633255121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52253889296340844355346989 19595208486127816633255121)
  ·
    refine ⟨14696406364595862474941341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19595208486127816633255121 14696406364595862474941341)
    ·
      refine ⟨5511152386723448428103003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14696406364595862474941341 5511152386723448428103003)
      ·
        refine ⟨8266728580085172642154505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5511152386723448428103003 8266728580085172642154505)
        ·
          refine ⟨6200046435063879481615879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8266728580085172642154505 6200046435063879481615879)
          ·
            refine ⟨9300069652595819222423819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6200046435063879481615879 9300069652595819222423819)
            ·
              refine ⟨13950104478893728833635729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9300069652595819222423819 13950104478893728833635729)
              ·
                refine ⟨10462578359170296625226797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13950104478893728833635729 10462578359170296625226797)
                ·
                  refine ⟨3923466884688861234460049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10462578359170296625226797 3923466884688861234460049)
                  ·
                    refine ⟨2942600163516645925845037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3923466884688861234460049 2942600163516645925845037)
                    ·
                      refine ⟨1103475061318742222191889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2942600163516645925845037 1103475061318742222191889)
                      ·
                        rfl

theorem cell23_2149010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2149010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149010 prefixEnd_2149010 := by exact prefixLift 2149010
  have htrace : WordTrace (prefixWord ++ tailWord_2149010) baseStart_2149010 baseEnd_2149010 := by
    simpa [prefixWord, tailWord_2149010, baseEnd_2149010] using wordTrace_append hprefix tailTrace_2149010
  have hstable : (prefixWord ++ tailWord_2149010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149010).length < 2 ^ (prefixWord ++ tailWord_2149010).sum := by decide
  have hdescent : baseEnd_2149010 < baseStart_2149010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149020 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2149020 : Nat := 118140960795 + 2149020 * 2 ^ 59
def prefixEnd_2149020 : Nat := 4983230072969 + 3 ^ 40 * 2149020 * 2
def baseEnd_2149020 : Nat := 1103480196125287183066843

theorem tailTrace_2149020 : CollatzResearch.WordTrace tailWord_2149020 prefixEnd_2149020 1103480196125287183066843 := by
  unfold tailWord_2149020
  simp only [CollatzResearch.WordTrace]
  refine ⟨39190599337237519120442257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52254132449650025493923009 39190599337237519120442257)
  ·
    refine ⟨29392949502928139340331693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39190599337237519120442257 29392949502928139340331693)
    ·
      refine ⟨11022356063598052252624385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29392949502928139340331693 11022356063598052252624385)
      ·
        refine ⟨8266767047698539189468289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11022356063598052252624385 8266767047698539189468289)
        ·
          refine ⟨6200075285773904392101217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8266767047698539189468289 6200075285773904392101217)
          ·
            refine ⟨4650056464330428294075913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6200075285773904392101217 4650056464330428294075913)
            ·
              refine ⟨3487542348247821220556935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4650056464330428294075913 3487542348247821220556935)
              ·
                refine ⟨5231313522371731830835403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487542348247821220556935 5231313522371731830835403)
                ·
                  refine ⟨7846970283557597746253105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5231313522371731830835403 7846970283557597746253105)
                  ·
                    refine ⟨5885227712668198309689829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7846970283557597746253105 5885227712668198309689829)
                    ·
                      refine ⟨1103480196125287183066843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5885227712668198309689829 1103480196125287183066843)
                      ·
                        rfl

theorem cell23_2149020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2149020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149020 prefixEnd_2149020 := by exact prefixLift 2149020
  have htrace : WordTrace (prefixWord ++ tailWord_2149020) baseStart_2149020 baseEnd_2149020 := by
    simpa [prefixWord, tailWord_2149020, baseEnd_2149020] using wordTrace_append hprefix tailTrace_2149020
  have hstable : (prefixWord ++ tailWord_2149020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149020).length < 2 ^ (prefixWord ++ tailWord_2149020).sum := by decide
  have hdescent : baseEnd_2149020 < baseStart_2149020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149041 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2149041 : Nat := 118140960795 + 2149041 * 2 ^ 59
def prefixEnd_2149041 : Nat := 4983230072969 + 3 ^ 40 * 2149041 * 2
def baseEnd_2149041 : Nat := 1103490979219031600904247

theorem tailTrace_2149041 : CollatzResearch.WordTrace tailWord_2149041 prefixEnd_2149041 1103490979219031600904247 := by
  unfold tailWord_2149041
  simp only [CollatzResearch.WordTrace]
  refine ⟨78381964607398958827398977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52254643071599305884932651 78381964607398958827398977)
  ·
    refine ⟨58786473455549219120549233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78381964607398958827398977 58786473455549219120549233)
    ·
      refine ⟨44089855091661914340411925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58786473455549219120549233 44089855091661914340411925)
      ·
        refine ⟨2066711957421652234706809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44089855091661914340411925 2066711957421652234706809)
        ·
          refine ⟨1550033968066239176030107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2066711957421652234706809 1550033968066239176030107)
          ·
            refine ⟨2325050952099358764045161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550033968066239176030107 2325050952099358764045161)
            ·
              refine ⟨1743788214074519073033871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2325050952099358764045161 1743788214074519073033871)
              ·
                refine ⟨2615682321111778609550807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1743788214074519073033871 2615682321111778609550807)
                ·
                  refine ⟨3923523481667667914326211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615682321111778609550807 3923523481667667914326211)
                  ·
                    refine ⟨5885285222501501871489317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3923523481667667914326211 5885285222501501871489317)
                    ·
                      refine ⟨1103490979219031600904247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5885285222501501871489317 1103490979219031600904247)
                      ·
                        rfl

theorem cell23_2149041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2149041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149041 prefixEnd_2149041 := by exact prefixLift 2149041
  have htrace : WordTrace (prefixWord ++ tailWord_2149041) baseStart_2149041 baseEnd_2149041 := by
    simpa [prefixWord, tailWord_2149041, baseEnd_2149041] using wordTrace_append hprefix tailTrace_2149041
  have hstable : (prefixWord ++ tailWord_2149041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149041).length < 2 ^ (prefixWord ++ tailWord_2149041).sum := by decide
  have hdescent : baseEnd_2149041 < baseStart_2149041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149074 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_2149074 : Nat := 118140960795 + 2149074 * 2 ^ 59
def prefixEnd_2149074 : Nat := 4983230072969 + 3 ^ 40 * 2149074 * 2
def baseEnd_2149074 : Nat := 1103507924080629971791595

theorem tailTrace_2149074 : CollatzResearch.WordTrace tailWord_2149074 prefixEnd_2149074 1103507924080629971791595 := by
  unfold tailWord_2149074
  simp only [CollatzResearch.WordTrace]
  refine ⟨19595792054069851365837569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52255445477519603642233517 19595792054069851365837569)
  ·
    refine ⟨14696844040552388524378177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19595792054069851365837569 14696844040552388524378177)
    ·
      refine ⟨11022633030414291393283633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14696844040552388524378177 11022633030414291393283633)
      ·
        refine ⟨8266974772810718544962725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11022633030414291393283633 8266974772810718544962725)
        ·
          refine ⟨1550057769902009727180511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8266974772810718544962725 1550057769902009727180511)
          ·
            refine ⟨2325086654853014590770767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550057769902009727180511 2325086654853014590770767)
            ·
              refine ⟨3487629982279521886156151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325086654853014590770767 3487629982279521886156151)
              ·
                refine ⟨5231444973419282829234227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487629982279521886156151 5231444973419282829234227)
                ·
                  refine ⟨7847167460128924243851341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5231444973419282829234227 7847167460128924243851341)
                  ·
                    refine ⟨2942687797548346591444253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7847167460128924243851341 2942687797548346591444253)
                    ·
                      refine ⟨1103507924080629971791595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2942687797548346591444253 1103507924080629971791595)
                      ·
                        rfl

theorem cell23_2149074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_2149074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149074 prefixEnd_2149074 := by exact prefixLift 2149074
  have htrace : WordTrace (prefixWord ++ tailWord_2149074) baseStart_2149074 baseEnd_2149074 := by
    simpa [prefixWord, tailWord_2149074, baseEnd_2149074] using wordTrace_append hprefix tailTrace_2149074
  have hstable : (prefixWord ++ tailWord_2149074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149074).length < 2 ^ (prefixWord ++ tailWord_2149074).sum := by decide
  have hdescent : baseEnd_2149074 < baseStart_2149074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149084 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_2149084 : Nat := 118140960795 + 2149084 * 2 ^ 59
def prefixEnd_2149084 : Nat := 4983230072969 + 3 ^ 40 * 2149084 * 2
def baseEnd_2149084 : Nat := 1103513058887174932666549

theorem tailTrace_2149084 : CollatzResearch.WordTrace tailWord_2149084 prefixEnd_2149084 1103513058887174932666549 := by
  unfold tailWord_2149084
  simp only [CollatzResearch.WordTrace]
  refine ⟨39191766473121588585607153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52255688630828784780809537 39191766473121588585607153)
  ·
    refine ⟨29393824854841191439205365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39191766473121588585607153 29393824854841191439205365)
    ·
      refine ⟨2755671080141361697425503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29393824854841191439205365 2755671080141361697425503)
      ·
        refine ⟨4133506620212042546138255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2755671080141361697425503 4133506620212042546138255)
        ·
          refine ⟨6200259930318063819207383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4133506620212042546138255 6200259930318063819207383)
          ·
            refine ⟨9300389895477095728811075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6200259930318063819207383 9300389895477095728811075)
            ·
              refine ⟨13950584843215643593216613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9300389895477095728811075 13950584843215643593216613)
              ·
                refine ⟨2615734658102933173728115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13950584843215643593216613 2615734658102933173728115)
                ·
                  refine ⟨3923601987154399760592173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615734658102933173728115 3923601987154399760592173)
                  ·
                    refine ⟨1471350745182899910222065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3923601987154399760592173 1471350745182899910222065)
                    ·
                      refine ⟨1103513058887174932666549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471350745182899910222065 1103513058887174932666549)
                      ·
                        rfl

theorem cell23_2149084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_2149084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149084 prefixEnd_2149084 := by exact prefixLift 2149084
  have htrace : WordTrace (prefixWord ++ tailWord_2149084) baseStart_2149084 baseEnd_2149084 := by
    simpa [prefixWord, tailWord_2149084, baseEnd_2149084] using wordTrace_append hprefix tailTrace_2149084
  have hstable : (prefixWord ++ tailWord_2149084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149084).length < 2 ^ (prefixWord ++ tailWord_2149084).sum := by decide
  have hdescent : baseEnd_2149084 < baseStart_2149084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149113 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 4, 3, 3]
def baseStart_2149113 : Nat := 118140960795 + 2149113 * 2 ^ 59
def prefixEnd_2149113 : Nat := 4983230072969 + 3 ^ 40 * 2149113 * 2
def baseEnd_2149113 : Nat := 1103527949826155319203915

theorem tailTrace_2149113 : CollatzResearch.WordTrace tailWord_2149113 prefixEnd_2149113 1103527949826155319203915 := by
  unfold tailWord_2149113
  simp only [CollatzResearch.WordTrace]
  refine ⟨78384590663138115124019993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52256393775425410082679995 78384590663138115124019993)
  ·
    refine ⟨58788442997353586343014995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78384590663138115124019993 58788442997353586343014995)
    ·
      refine ⟨88182664496030379514522493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58788442997353586343014995 88182664496030379514522493)
      ·
        refine ⟨33068499186011392317945935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88182664496030379514522493 33068499186011392317945935)
        ·
          refine ⟨49602748779017088476918903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33068499186011392317945935 49602748779017088476918903)
          ·
            refine ⟨74404123168525632715378355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49602748779017088476918903 74404123168525632715378355)
            ·
              refine ⟨111606184752788449073067533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74404123168525632715378355 111606184752788449073067533)
              ·
                refine ⟨41852319282295668402400325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111606184752788449073067533 41852319282295668402400325)
                ·
                  refine ⟨7847309865430437825450061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41852319282295668402400325 7847309865430437825450061)
                  ·
                    refine ⟨2942741199536414184543773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7847309865430437825450061 2942741199536414184543773)
                    ·
                      refine ⟨1103527949826155319203915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2942741199536414184543773 1103527949826155319203915)
                      ·
                        rfl

theorem cell23_2149113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_2149113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149113 prefixEnd_2149113 := by exact prefixLift 2149113
  have htrace : WordTrace (prefixWord ++ tailWord_2149113) baseStart_2149113 baseEnd_2149113 := by
    simpa [prefixWord, tailWord_2149113, baseEnd_2149113] using wordTrace_append hprefix tailTrace_2149113
  have hstable : (prefixWord ++ tailWord_2149113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149113).length < 2 ^ (prefixWord ++ tailWord_2149113).sum := by decide
  have hdescent : baseEnd_2149113 < baseStart_2149113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149170 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2149170 : Nat := 118140960795 + 2149170 * 2 ^ 59
def prefixEnd_2149170 : Nat := 4983230072969 + 3 ^ 40 * 2149170 * 2
def baseEnd_2149170 : Nat := 1103557218223461596191153

theorem tailTrace_2149170 : CollatzResearch.WordTrace tailWord_2149170 prefixEnd_2149170 1103557218223461596191153 := by
  unfold tailWord_2149170
  simp only [CollatzResearch.WordTrace]
  refine ⟨19596667405982903464711241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52257779749287742572563309 19596667405982903464711241)
  ·
    refine ⟨14697500554487177598533431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19596667405982903464711241 14697500554487177598533431)
    ·
      refine ⟨22046250831730766397800147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14697500554487177598533431 22046250831730766397800147)
      ·
        refine ⟨33069376247596149596700221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22046250831730766397800147 33069376247596149596700221)
        ·
          refine ⟨12401016092848556098762583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33069376247596149596700221 12401016092848556098762583)
          ·
            refine ⟨18601524139272834148143875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12401016092848556098762583 18601524139272834148143875)
            ·
              refine ⟨27902286208909251222215813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18601524139272834148143875 27902286208909251222215813)
              ·
                refine ⟨5231678664170484604165465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27902286208909251222215813 5231678664170484604165465)
                ·
                  refine ⟨3923758998127863453124099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5231678664170484604165465 3923758998127863453124099)
                  ·
                    refine ⟨5885638497191795179686149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3923758998127863453124099 5885638497191795179686149)
                    ·
                      refine ⟨1103557218223461596191153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5885638497191795179686149 1103557218223461596191153)
                      ·
                        rfl

theorem cell23_2149170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2149170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149170 prefixEnd_2149170 := by exact prefixLift 2149170
  have htrace : WordTrace (prefixWord ++ tailWord_2149170) baseStart_2149170 baseEnd_2149170 := by
    simpa [prefixWord, tailWord_2149170, baseEnd_2149170] using wordTrace_append hprefix tailTrace_2149170
  have hstable : (prefixWord ++ tailWord_2149170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149170).length < 2 ^ (prefixWord ++ tailWord_2149170).sum := by decide
  have hdescent : baseEnd_2149170 < baseStart_2149170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149180 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_2149180 : Nat := 118140960795 + 2149180 * 2 ^ 59
def prefixEnd_2149180 : Nat := 4983230072969 + 3 ^ 40 * 2149180 * 2
def baseEnd_2149180 : Nat := 367854117676668852355369

theorem tailTrace_2149180 : CollatzResearch.WordTrace tailWord_2149180 prefixEnd_2149180 367854117676668852355369 := by
  unfold tailWord_2149180
  simp only [CollatzResearch.WordTrace]
  refine ⟨39193517176947692783354497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52258022902596923711139329 39193517176947692783354497)
  ·
    refine ⟨29395137882710769587515873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39193517176947692783354497 29395137882710769587515873)
    ·
      refine ⟨22046353412033077190636905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29395137882710769587515873 22046353412033077190636905)
      ·
        refine ⟨16534765059024807892977679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22046353412033077190636905 16534765059024807892977679)
        ·
          refine ⟨24802147588537211839466519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16534765059024807892977679 24802147588537211839466519)
          ·
            refine ⟨37203221382805817759199779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24802147588537211839466519 37203221382805817759199779)
            ·
              refine ⟨55804832074208726638799669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37203221382805817759199779 55804832074208726638799669)
              ·
                refine ⟨5231703006957068122387469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55804832074208726638799669 5231703006957068122387469)
                ·
                  refine ⟨1961888627608900545895301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5231703006957068122387469 1961888627608900545895301)
                  ·
                    refine ⟨367854117676668852355369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1961888627608900545895301 367854117676668852355369)
                    ·
                      rfl

theorem cell23_2149180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_2149180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149180 prefixEnd_2149180 := by exact prefixLift 2149180
  have htrace : WordTrace (prefixWord ++ tailWord_2149180) baseStart_2149180 baseEnd_2149180 := by
    simpa [prefixWord, tailWord_2149180, baseEnd_2149180] using wordTrace_append hprefix tailTrace_2149180
  have hstable : (prefixWord ++ tailWord_2149180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149180).length < 2 ^ (prefixWord ++ tailWord_2149180).sum := by decide
  have hdescent : baseEnd_2149180 < baseStart_2149180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149204 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_2149204 : Nat := 118140960795 + 2149204 * 2 ^ 59
def prefixEnd_2149204 : Nat := 4983230072969 + 3 ^ 40 * 2149204 * 2
def baseEnd_2149204 : Nat := 1103574676565714463165997

theorem tailTrace_2149204 : CollatzResearch.WordTrace tailWord_2149204 prefixEnd_2149204 1103574676565714463165997 := by
  unfold tailWord_2149204
  simp only [CollatzResearch.WordTrace]
  refine ⟨39193954852904218832791333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52258606470538958443721777 39193954852904218832791333)
  ·
    refine ⟨7348866534919541031148375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39193954852904218832791333 7348866534919541031148375)
    ·
      refine ⟨11023299802379311546722563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7348866534919541031148375 11023299802379311546722563)
      ·
        refine ⟨16534949703568967320083845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11023299802379311546722563 16534949703568967320083845)
        ·
          refine ⟨3100303069419181372515721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16534949703568967320083845 3100303069419181372515721)
          ·
            refine ⟨2325227302064386029386791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3100303069419181372515721 2325227302064386029386791)
            ·
              refine ⟨3487840953096579044080187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325227302064386029386791 3487840953096579044080187)
              ·
                refine ⟨5231761429644868566120281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487840953096579044080187 5231761429644868566120281)
                ·
                  refine ⟨3923821072233651424590211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5231761429644868566120281 3923821072233651424590211)
                  ·
                    refine ⟨5885731608350477136885317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3923821072233651424590211 5885731608350477136885317)
                    ·
                      refine ⟨1103574676565714463165997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5885731608350477136885317 1103574676565714463165997)
                      ·
                        rfl

theorem cell23_2149204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_2149204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149204 prefixEnd_2149204 := by exact prefixLift 2149204
  have htrace : WordTrace (prefixWord ++ tailWord_2149204) baseStart_2149204 baseEnd_2149204 := by
    simpa [prefixWord, tailWord_2149204, baseEnd_2149204] using wordTrace_append hprefix tailTrace_2149204
  have hstable : (prefixWord ++ tailWord_2149204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149204).length < 2 ^ (prefixWord ++ tailWord_2149204).sum := by decide
  have hdescent : baseEnd_2149204 < baseStart_2149204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149207 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 3]
def baseStart_2149207 : Nat := 118140960795 + 2149207 * 2 ^ 59
def prefixEnd_2149207 : Nat := 4983230072969 + 3 ^ 40 * 2149207 * 2
def baseEnd_2149207 : Nat := 1103576217007677951428483

theorem tailTrace_2149207 : CollatzResearch.WordTrace tailWord_2149207 prefixEnd_2149207 1103576217007677951428483 := by
  unfold tailWord_2149207
  simp only [CollatzResearch.WordTrace]
  refine ⟨78388019124797569177941875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52258679416531712785294583 78388019124797569177941875)
  ·
    refine ⟨117582028687196353766912813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78388019124797569177941875 117582028687196353766912813)
    ·
      refine ⟨44093260757698632662592305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117582028687196353766912813 44093260757698632662592305)
      ·
        refine ⟨33069945568273974496944229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44093260757698632662592305 33069945568273974496944229)
        ·
          refine ⟨6200614794051370218177043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33069945568273974496944229 6200614794051370218177043)
          ·
            refine ⟨9300922191077055327265565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6200614794051370218177043 9300922191077055327265565)
            ·
              refine ⟨3487845821653895747724587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9300922191077055327265565 3487845821653895747724587)
              ·
                refine ⟨5231768732480843621586881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487845821653895747724587 5231768732480843621586881)
                ·
                  refine ⟨3923826549360632716190161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5231768732480843621586881 3923826549360632716190161)
                  ·
                    refine ⟨2942869912020474537142621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3923826549360632716190161 2942869912020474537142621)
                    ·
                      refine ⟨1103576217007677951428483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2942869912020474537142621 1103576217007677951428483)
                      ·
                        rfl

theorem cell23_2149207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_2149207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149207 prefixEnd_2149207 := by exact prefixLift 2149207
  have htrace : WordTrace (prefixWord ++ tailWord_2149207) baseStart_2149207 baseEnd_2149207 := by
    simpa [prefixWord, tailWord_2149207, baseEnd_2149207] using wordTrace_append hprefix tailTrace_2149207
  have hstable : (prefixWord ++ tailWord_2149207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149207).length < 2 ^ (prefixWord ++ tailWord_2149207).sum := by decide
  have hdescent : baseEnd_2149207 < baseStart_2149207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149257 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 1, 5]
def baseStart_2149257 : Nat := 118140960795 + 2149257 * 2 ^ 59
def prefixEnd_2149257 : Nat := 4983230072969 + 3 ^ 40 * 2149257 * 2
def baseEnd_2149257 : Nat := 367867297013467585267751

theorem tailTrace_2149257 : CollatzResearch.WordTrace tailWord_2149257 prefixEnd_2149257 367867297013467585267751 := by
  unfold tailWord_2149257
  simp only [CollatzResearch.WordTrace]
  refine ⟨78389842774616427717262025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52259895183077618478174683 78389842774616427717262025)
  ·
    refine ⟨58792382080962320787946519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78389842774616427717262025 58792382080962320787946519)
    ·
      refine ⟨88188573121443481181919779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58792382080962320787946519 88188573121443481181919779)
      ·
        refine ⟨132282859682165221772879669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88188573121443481181919779 132282859682165221772879669)
        ·
          refine ⟨12401518095202989541207469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132282859682165221772879669 12401518095202989541207469)
          ·
            refine ⟨4650569285701121077952801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12401518095202989541207469 4650569285701121077952801)
            ·
              refine ⟨3487926964275840808464601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4650569285701121077952801 3487926964275840808464601)
              ·
                refine ⟨2615945223206880606348451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3487926964275840808464601 2615945223206880606348451)
                ·
                  refine ⟨3923917834810320909522677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615945223206880606348451 3923917834810320909522677)
                  ·
                    refine ⟨367867297013467585267751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3923917834810320909522677 367867297013467585267751)
                    ·
                      rfl

theorem cell23_2149257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 5].length) (baseStart_2149257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149257 prefixEnd_2149257 := by exact prefixLift 2149257
  have htrace : WordTrace (prefixWord ++ tailWord_2149257) baseStart_2149257 baseEnd_2149257 := by
    simpa [prefixWord, tailWord_2149257, baseEnd_2149257] using wordTrace_append hprefix tailTrace_2149257
  have hstable : (prefixWord ++ tailWord_2149257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149257).length < 2 ^ (prefixWord ++ tailWord_2149257).sum := by decide
  have hdescent : baseEnd_2149257 < baseStart_2149257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149260 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_2149260 : Nat := 118140960795 + 2149260 * 2 ^ 59
def prefixEnd_2149260 : Nat := 4983230072969 + 3 ^ 40 * 2149260 * 2
def baseEnd_2149260 : Nat := 1103603431482366244065739

theorem tailTrace_2149260 : CollatzResearch.WordTrace tailWord_2149260 prefixEnd_2149260 1103603431482366244065739 := by
  unfold tailWord_2149260
  simp only [CollatzResearch.WordTrace]
  refine ⟨39194976096802779614810617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52259968129070372819747489 39194976096802779614810617)
  ·
    refine ⟨29396232072602084711107963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39194976096802779614810617 29396232072602084711107963)
    ·
      refine ⟨44094348108903127066661945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29396232072602084711107963 44094348108903127066661945)
      ·
        refine ⟨33070761081677345299996459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44094348108903127066661945 33070761081677345299996459)
        ·
          refine ⟨49606141622516017949994689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33070761081677345299996459 49606141622516017949994689)
          ·
            refine ⟨37204606216887013462496017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49606141622516017949994689 37204606216887013462496017)
            ·
              refine ⟨27903454662665260096872013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37204606216887013462496017 27903454662665260096872013)
              ·
                refine ⟨10463795498499472536327005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27903454662665260096872013 10463795498499472536327005)
                ·
                  refine ⟨3923923311937302201122627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10463795498499472536327005 3923923311937302201122627)
                  ·
                    refine ⟨5885884967905953301683941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3923923311937302201122627 5885884967905953301683941)
                    ·
                      refine ⟨1103603431482366244065739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5885884967905953301683941 1103603431482366244065739)
                      ·
                        rfl

theorem cell23_2149260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_2149260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149260 prefixEnd_2149260 := by exact prefixLift 2149260
  have htrace : WordTrace (prefixWord ++ tailWord_2149260) baseStart_2149260 baseEnd_2149260 := by
    simpa [prefixWord, tailWord_2149260, baseEnd_2149260] using wordTrace_append hprefix tailTrace_2149260
  have hstable : (prefixWord ++ tailWord_2149260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149260).length < 2 ^ (prefixWord ++ tailWord_2149260).sum := by decide
  have hdescent : baseEnd_2149260 < baseStart_2149260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149277 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_2149277 : Nat := 118140960795 + 2149277 * 2 ^ 59
def prefixEnd_2149277 : Nat := 4983230072969 + 3 ^ 40 * 2149277 * 2
def baseEnd_2149277 : Nat := 1103612160653492677553161

theorem tailTrace_2149277 : CollatzResearch.WordTrace tailWord_2149277 prefixEnd_2149277 1103612160653492677553161 := by
  unfold tailWord_2149277
  simp only [CollatzResearch.WordTrace]
  refine ⟨78390572234543971132990085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52260381489695980755326723 78390572234543971132990085)
  ·
    refine ⟨14698232293976994587435641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78390572234543971132990085 14698232293976994587435641)
    ·
      refine ⟨11023674220482745940576731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14698232293976994587435641 11023674220482745940576731)
      ·
        refine ⟨16535511330724118910865097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11023674220482745940576731 16535511330724118910865097)
        ·
          refine ⟨12401633498043089183148823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16535511330724118910865097 12401633498043089183148823)
          ·
            refine ⟨18602450247064633774723235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12401633498043089183148823 18602450247064633774723235)
            ·
              refine ⟨27903675370596950662084853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18602450247064633774723235 27903675370596950662084853)
              ·
                refine ⟨2615969565993464124570455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27903675370596950662084853 2615969565993464124570455)
                ·
                  refine ⟨3923954348990196186855683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2615969565993464124570455 3923954348990196186855683)
                  ·
                    refine ⟨5885931523485294280283525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3923954348990196186855683 5885931523485294280283525)
                    ·
                      refine ⟨1103612160653492677553161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5885931523485294280283525 1103612160653492677553161)
                      ·
                        rfl

theorem cell23_2149277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_2149277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149277 prefixEnd_2149277 := by exact prefixLift 2149277
  have htrace : WordTrace (prefixWord ++ tailWord_2149277) baseStart_2149277 baseEnd_2149277 := by
    simpa [prefixWord, tailWord_2149277, baseEnd_2149277] using wordTrace_append hprefix tailTrace_2149277
  have hstable : (prefixWord ++ tailWord_2149277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149277).length < 2 ^ (prefixWord ++ tailWord_2149277).sum := by decide
  have hdescent : baseEnd_2149277 < baseStart_2149277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149280 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2149280 : Nat := 118140960795 + 2149280 * 2 ^ 59
def prefixEnd_2149280 : Nat := 4983230072969 + 3 ^ 40 * 2149280 * 2
def baseEnd_2149280 : Nat := 1103613701095456165815647

theorem tailTrace_2149280 : CollatzResearch.WordTrace tailWord_2149280 prefixEnd_2149280 1103613701095456165815647 := by
  unfold tailWord_2149280
  simp only [CollatzResearch.WordTrace]
  refine ⟨39195340826766551322674647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52260454435688735096899529 39195340826766551322674647)
  ·
    refine ⟨58793011240149826984011971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39195340826766551322674647 58793011240149826984011971)
    ·
      refine ⟨88189516860224740476017957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58793011240149826984011971 88189516860224740476017957)
      ·
        refine ⟨16535534411292138839253367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88189516860224740476017957 16535534411292138839253367)
        ·
          refine ⟨24803301616938208258880051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16535534411292138839253367 24803301616938208258880051)
          ·
            refine ⟨37204952425407312388320077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24803301616938208258880051 37204952425407312388320077)
            ·
              refine ⟨13951857159527742145620029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37204952425407312388320077 13951857159527742145620029)
              ·
                refine ⟨5231946434822903304607511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13951857159527742145620029 5231946434822903304607511)
                ·
                  refine ⟨7847919652234354956911267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5231946434822903304607511 7847919652234354956911267)
                  ·
                    refine ⟨11771879478351532435366901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7847919652234354956911267 11771879478351532435366901)
                    ·
                      refine ⟨1103613701095456165815647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11771879478351532435366901 1103613701095456165815647)
                      ·
                        rfl

theorem cell23_2149280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2149280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149280 prefixEnd_2149280 := by exact prefixLift 2149280
  have htrace : WordTrace (prefixWord ++ tailWord_2149280) baseStart_2149280 baseEnd_2149280 := by
    simpa [prefixWord, tailWord_2149280, baseEnd_2149280] using wordTrace_append hprefix tailTrace_2149280
  have hstable : (prefixWord ++ tailWord_2149280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149280).length < 2 ^ (prefixWord ++ tailWord_2149280).sum := by decide
  have hdescent : baseEnd_2149280 < baseStart_2149280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149283 : List Nat := [1, 1, 1, 4, 1, 2, 13]
def baseStart_2149283 : Nat := 118140960795 + 2149283 * 2 ^ 59
def prefixEnd_2149283 : Nat := 4983230072969 + 3 ^ 40 * 2149283 * 2
def baseEnd_2149283 : Nat := 13624879525153329062693

theorem tailTrace_2149283 : CollatzResearch.WordTrace tailWord_2149283 prefixEnd_2149283 13624879525153329062693 := by
  unfold tailWord_2149283
  simp only [CollatzResearch.WordTrace]
  refine ⟨78390791072522234157708503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52260527381681489438472335 78390791072522234157708503)
  ·
    refine ⟨117586186608783351236562755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78390791072522234157708503 117586186608783351236562755)
    ·
      refine ⟨176379279913175026854844133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117586186608783351236562755 176379279913175026854844133)
      ·
        refine ⟨33071114983720317535283275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176379279913175026854844133 33071114983720317535283275)
        ·
          refine ⟨49606672475580476302924913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33071114983720317535283275 49606672475580476302924913)
          ·
            refine ⟨37205004356685357227193685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49606672475580476302924913 37205004356685357227193685)
            ·
              refine ⟨13624879525153329062693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 37205004356685357227193685 13624879525153329062693)
              ·
                rfl

theorem cell23_2149283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 13].length) (baseStart_2149283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149283 prefixEnd_2149283 := by exact prefixLift 2149283
  have htrace : WordTrace (prefixWord ++ tailWord_2149283) baseStart_2149283 baseEnd_2149283 := by
    simpa [prefixWord, tailWord_2149283, baseEnd_2149283] using wordTrace_append hprefix tailTrace_2149283
  have hstable : (prefixWord ++ tailWord_2149283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149283).length < 2 ^ (prefixWord ++ tailWord_2149283).sum := by decide
  have hdescent : baseEnd_2149283 < baseStart_2149283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149304 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 2, 4]
def baseStart_2149304 : Nat := 118140960795 + 2149304 * 2 ^ 59
def prefixEnd_2149304 : Nat := 4983230072969 + 3 ^ 40 * 2149304 * 2
def baseEnd_2149304 : Nat := 367875341543721357305179

theorem tailTrace_2149304 : CollatzResearch.WordTrace tailWord_2149304 prefixEnd_2149304 367875341543721357305179 := by
  unfold tailWord_2149304
  simp only [CollatzResearch.WordTrace]
  refine ⟨39195778502723077372111483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52261038003630769829481977 39195778502723077372111483)
  ·
    refine ⟨58793667754084616058167225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39195778502723077372111483 58793667754084616058167225)
    ·
      refine ⟨44095250815563462043625419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58793667754084616058167225 44095250815563462043625419)
      ·
        refine ⟨66142876223345193065438129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44095250815563462043625419 66142876223345193065438129)
        ·
          refine ⟨49607157167508894799078597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66142876223345193065438129 49607157167508894799078597)
          ·
            refine ⟨9301341968907917774827237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49607157167508894799078597 9301341968907917774827237)
            ·
              refine ⟨1744001619170234582780107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9301341968907917774827237 1744001619170234582780107)
              ·
                refine ⟨2616002428755351874170161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744001619170234582780107 2616002428755351874170161)
                ·
                  refine ⟨1962001821566513905627621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2616002428755351874170161 1962001821566513905627621)
                  ·
                    refine ⟨367875341543721357305179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962001821566513905627621 367875341543721357305179)
                    ·
                      rfl

theorem cell23_2149304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_2149304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149304 prefixEnd_2149304 := by exact prefixLift 2149304
  have htrace : WordTrace (prefixWord ++ tailWord_2149304) baseStart_2149304 baseEnd_2149304 := by
    simpa [prefixWord, tailWord_2149304, baseEnd_2149304] using wordTrace_append hprefix tailTrace_2149304
  have hstable : (prefixWord ++ tailWord_2149304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149304).length < 2 ^ (prefixWord ++ tailWord_2149304).sum := by decide
  have hdescent : baseEnd_2149304 < baseStart_2149304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149325 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2149325 : Nat := 118140960795 + 2149325 * 2 ^ 59
def prefixEnd_2149325 : Nat := 4983230072969 + 3 ^ 40 * 2149325 * 2
def baseEnd_2149325 : Nat := 367878935908302829917647

theorem tailTrace_2149325 : CollatzResearch.WordTrace tailWord_2149325 prefixEnd_2149325 367878935908302829917647 := by
  unfold tailWord_2149325
  simp only [CollatzResearch.WordTrace]
  refine ⟨78392322938370075330737429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52261548625580050220491619 78392322938370075330737429)
  ·
    refine ⟨3674640137736097281128317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78392322938370075330737429 3674640137736097281128317)
    ·
      refine ⟨1377990051651036480423119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3674640137736097281128317 1377990051651036480423119)
      ·
        refine ⟨2066985077476554720634679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377990051651036480423119 2066985077476554720634679)
        ·
          refine ⟨3100477616214832080952019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2066985077476554720634679 3100477616214832080952019)
          ·
            refine ⟨4650716424322248121428029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3100477616214832080952019 4650716424322248121428029)
            ·
              refine ⟨1744018659120843045535511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4650716424322248121428029 1744018659120843045535511)
              ·
                refine ⟨2616027988681264568303267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744018659120843045535511 2616027988681264568303267)
                ·
                  refine ⟨3924041983021896852454901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616027988681264568303267 3924041983021896852454901)
                  ·
                    refine ⟨367878935908302829917647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3924041983021896852454901 367878935908302829917647)
                    ·
                      rfl

theorem cell23_2149325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2149325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149325 prefixEnd_2149325 := by exact prefixLift 2149325
  have htrace : WordTrace (prefixWord ++ tailWord_2149325) baseStart_2149325 baseEnd_2149325 := by
    simpa [prefixWord, tailWord_2149325, baseEnd_2149325] using wordTrace_append hprefix tailTrace_2149325
  have hstable : (prefixWord ++ tailWord_2149325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149325).length < 2 ^ (prefixWord ++ tailWord_2149325).sum := by decide
  have hdescent : baseEnd_2149325 < baseStart_2149325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149327 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 3]
def baseStart_2149327 : Nat := 118140960795 + 2149327 * 2 ^ 59
def prefixEnd_2149327 : Nat := 4983230072969 + 3 ^ 40 * 2149327 * 2
def baseEnd_2149327 : Nat := 1103637834686217481927931

theorem tailTrace_2149327 : CollatzResearch.WordTrace tailWord_2149327 prefixEnd_2149327 1103637834686217481927931 := by
  unfold tailWord_2149327
  simp only [CollatzResearch.WordTrace]
  refine ⟨78392395884362829672310235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52261597256241886448206823 78392395884362829672310235)
  ·
    refine ⟨117588593826544244508465353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78392395884362829672310235 117588593826544244508465353)
    ·
      refine ⟨88191445369908183381349015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117588593826544244508465353 88191445369908183381349015)
      ·
        refine ⟨132287168054862275072023523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88191445369908183381349015 132287168054862275072023523)
        ·
          refine ⟨198430752082293412608035285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132287168054862275072023523 198430752082293412608035285)
          ·
            refine ⟨4650720751928751858000827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 198430752082293412608035285 4650720751928751858000827)
            ·
              refine ⟨6976081127893127787001241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4650720751928751858000827 6976081127893127787001241)
              ·
                refine ⟨5232060845919845840250931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6976081127893127787001241 5232060845919845840250931)
                ·
                  refine ⟨7848091268879768760376397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5232060845919845840250931 7848091268879768760376397)
                  ·
                    refine ⟨2943034225829913285141149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7848091268879768760376397 2943034225829913285141149)
                    ·
                      refine ⟨1103637834686217481927931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2943034225829913285141149 1103637834686217481927931)
                      ·
                        rfl

theorem cell23_2149327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 3].length) (baseStart_2149327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149327 prefixEnd_2149327 := by exact prefixLift 2149327
  have htrace : WordTrace (prefixWord ++ tailWord_2149327) baseStart_2149327 baseEnd_2149327 := by
    simpa [prefixWord, tailWord_2149327, baseEnd_2149327] using wordTrace_append hprefix tailTrace_2149327
  have hstable : (prefixWord ++ tailWord_2149327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149327).length < 2 ^ (prefixWord ++ tailWord_2149327).sum := by decide
  have hdescent : baseEnd_2149327 < baseStart_2149327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149354 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_2149354 : Nat := 118140960795 + 2149354 * 2 ^ 59
def prefixEnd_2149354 : Nat := 4983230072969 + 3 ^ 40 * 2149354 * 2
def baseEnd_2149354 : Nat := 1103651698663888876290307

theorem tailTrace_2149354 : CollatzResearch.WordTrace tailWord_2149354 prefixEnd_2149354 1103651698663888876290307 := by
  unfold tailWord_2149354
  simp only [CollatzResearch.WordTrace]
  refine ⟨19598345163816253320885779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52262253770176675522362077 19598345163816253320885779)
  ·
    refine ⟨29397517745724379981328669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19598345163816253320885779 29397517745724379981328669)
    ·
      refine ⟨11024069154646642492998251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29397517745724379981328669 11024069154646642492998251)
      ·
        refine ⟨16536103731969963739497377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11024069154646642492998251 16536103731969963739497377)
        ·
          refine ⟨12402077798977472804623033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16536103731969963739497377 12402077798977472804623033)
          ·
            refine ⟨9301558349233104603467275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12402077798977472804623033 9301558349233104603467275)
            ·
              refine ⟨13952337523849656905200913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9301558349233104603467275 13952337523849656905200913)
              ·
                refine ⟨10464253142887242678900685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13952337523849656905200913 10464253142887242678900685)
                ·
                  refine ⟨3924094928582716004587757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10464253142887242678900685 3924094928582716004587757)
                  ·
                    refine ⟨1471535598218518501720409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3924094928582716004587757 1471535598218518501720409)
                    ·
                      refine ⟨1103651698663888876290307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471535598218518501720409 1103651698663888876290307)
                      ·
                        rfl

theorem cell23_2149354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_2149354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149354 prefixEnd_2149354 := by exact prefixLift 2149354
  have htrace : WordTrace (prefixWord ++ tailWord_2149354) baseStart_2149354 baseEnd_2149354 := by
    simpa [prefixWord, tailWord_2149354, baseEnd_2149354] using wordTrace_append hprefix tailTrace_2149354
  have hstable : (prefixWord ++ tailWord_2149354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149354).length < 2 ^ (prefixWord ++ tailWord_2149354).sum := by decide
  have hdescent : baseEnd_2149354 < baseStart_2149354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149370 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_2149370 : Nat := 118140960795 + 2149370 * 2 ^ 59
def prefixEnd_2149370 : Nat := 4983230072969 + 3 ^ 40 * 2149370 * 2
def baseEnd_2149370 : Nat := 1103659914354360813690233

theorem tailTrace_2149370 : CollatzResearch.WordTrace tailWord_2149370 prefixEnd_2149370 1103659914354360813690233 := by
  unfold tailWord_2149370
  simp only [CollatzResearch.WordTrace]
  refine ⟨19598491055801762004031391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52262642815471365344083709 19598491055801762004031391)
  ·
    refine ⟨29397736583702643006047087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19598491055801762004031391 29397736583702643006047087)
    ·
      refine ⟨44096604875553964509070631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29397736583702643006047087 44096604875553964509070631)
      ·
        refine ⟨66144907313330946763605947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44096604875553964509070631 66144907313330946763605947)
        ·
          refine ⟨99217360969996420145408921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66144907313330946763605947 99217360969996420145408921)
          ·
            refine ⟨74413020727497315109056691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99217360969996420145408921 74413020727497315109056691)
            ·
              refine ⟨111619531091245972663585037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74413020727497315109056691 111619531091245972663585037)
              ·
                refine ⟨41857324159217239748844389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111619531091245972663585037 41857324159217239748844389)
                ·
                  refine ⟨7848248279853232452908323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41857324159217239748844389 7848248279853232452908323)
                  ·
                    refine ⟨11772372419779848679362485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7848248279853232452908323 11772372419779848679362485)
                    ·
                      refine ⟨1103659914354360813690233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11772372419779848679362485 1103659914354360813690233)
                      ·
                        rfl

theorem cell23_2149370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_2149370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149370 prefixEnd_2149370 := by exact prefixLift 2149370
  have htrace : WordTrace (prefixWord ++ tailWord_2149370) baseStart_2149370 baseEnd_2149370 := by
    simpa [prefixWord, tailWord_2149370, baseEnd_2149370] using wordTrace_append hprefix tailTrace_2149370
  have hstable : (prefixWord ++ tailWord_2149370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149370).length < 2 ^ (prefixWord ++ tailWord_2149370).sum := by decide
  have hdescent : baseEnd_2149370 < baseStart_2149370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149384 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 1, 4, 2]
def baseStart_2149384 : Nat := 118140960795 + 2149384 * 2 ^ 59
def prefixEnd_2149384 : Nat := 4983230072969 + 3 ^ 40 * 2149384 * 2
def baseEnd_2149384 : Nat := 1103667103083523758915169

theorem tailTrace_2149384 : CollatzResearch.WordTrace tailWord_2149384 prefixEnd_2149384 1103667103083523758915169 := by
  unfold tailWord_2149384
  simp only [CollatzResearch.WordTrace]
  refine ⟨39197237422578164203567603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52262983230104218938090137 39197237422578164203567603)
  ·
    refine ⟨58795856133867246305351405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39197237422578164203567603 58795856133867246305351405)
    ·
      refine ⟨22048446050200217364506777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58795856133867246305351405 22048446050200217364506777)
      ·
        refine ⟨16536334537650163023380083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22048446050200217364506777 16536334537650163023380083)
        ·
          refine ⟨24804501806475244535070125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16536334537650163023380083 24804501806475244535070125)
          ·
            refine ⟨9301688177428216700651297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24804501806475244535070125 9301688177428216700651297)
            ·
              refine ⟨6976266133071162525488473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9301688177428216700651297 6976266133071162525488473)
              ·
                refine ⟨5232199599803371894116355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6976266133071162525488473 5232199599803371894116355)
                ·
                  refine ⟨7848299399705057841174533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5232199599803371894116355 7848299399705057841174533)
                  ·
                    refine ⟨1471556137444698345220225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7848299399705057841174533 1471556137444698345220225)
                    ·
                      refine ⟨1103667103083523758915169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471556137444698345220225 1103667103083523758915169)
                      ·
                        rfl

theorem cell23_2149384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_2149384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149384 prefixEnd_2149384 := by exact prefixLift 2149384
  have htrace : WordTrace (prefixWord ++ tailWord_2149384) baseStart_2149384 baseEnd_2149384 := by
    simpa [prefixWord, tailWord_2149384, baseEnd_2149384] using wordTrace_append hprefix tailTrace_2149384
  have hstable : (prefixWord ++ tailWord_2149384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149384).length < 2 ^ (prefixWord ++ tailWord_2149384).sum := by decide
  have hdescent : baseEnd_2149384 < baseStart_2149384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149388 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 1, 3, 2]
def baseStart_2149388 : Nat := 118140960795 + 2149388 * 2 ^ 59
def prefixEnd_2149388 : Nat := 4983230072969 + 3 ^ 40 * 2149388 * 2
def baseEnd_2149388 : Nat := 1103669157006141743265151

theorem tailTrace_2149388 : CollatzResearch.WordTrace tailWord_2149388 prefixEnd_2149388 1103669157006141743265151 := by
  unfold tailWord_2149388
  simp only [CollatzResearch.WordTrace]
  refine ⟨39197310368570918545140409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52263080491427891393520545 39197310368570918545140409)
  ·
    refine ⟨29397982776428188908855307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39197310368570918545140409 29397982776428188908855307)
    ·
      refine ⟨44096974164642283363282961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29397982776428188908855307 44096974164642283363282961)
      ·
        refine ⟨33072730623481712522462221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44096974164642283363282961 33072730623481712522462221)
        ·
          refine ⟨12402273983805642195923333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33072730623481712522462221 12402273983805642195923333)
          ·
            refine ⟨2325426371963557911735625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12402273983805642195923333 2325426371963557911735625)
            ·
              refine ⟨1744069778972668433801719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2325426371963557911735625 1744069778972668433801719)
              ·
                refine ⟨2616104668459002650702579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744069778972668433801719 2616104668459002650702579)
                ·
                  refine ⟨3924157002688503976053869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616104668459002650702579 3924157002688503976053869)
                  ·
                    refine ⟨1471558876008188991020201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3924157002688503976053869 1471558876008188991020201)
                    ·
                      refine ⟨1103669157006141743265151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471558876008188991020201 1103669157006141743265151)
                      ·
                        rfl

theorem cell23_2149388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_2149388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149388 prefixEnd_2149388 := by exact prefixLift 2149388
  have htrace : WordTrace (prefixWord ++ tailWord_2149388) baseStart_2149388 baseEnd_2149388 := by
    simpa [prefixWord, tailWord_2149388, baseEnd_2149388] using wordTrace_append hprefix tailTrace_2149388
  have hstable : (prefixWord ++ tailWord_2149388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149388).length < 2 ^ (prefixWord ++ tailWord_2149388).sum := by decide
  have hdescent : baseEnd_2149388 < baseStart_2149388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149397 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_2149397 : Nat := 118140960795 + 2149397 * 2 ^ 59
def prefixEnd_2149397 : Nat := 4983230072969 + 3 ^ 40 * 2149397 * 2
def baseEnd_2149397 : Nat := 1103673778332032208052609

theorem tailTrace_2149397 : CollatzResearch.WordTrace tailWord_2149397 prefixEnd_2149397 1103673778332032208052609 := by
  unfold tailWord_2149397
  simp only [CollatzResearch.WordTrace]
  refine ⟨78394948994109231627358445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52263299329406154418238963 78394948994109231627358445)
  ·
    refine ⟨29398105872790961860259417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78394948994109231627358445 29398105872790961860259417)
    ·
      refine ⟨22048579404593221395194563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29398105872790961860259417 22048579404593221395194563)
      ·
        refine ⟨33072869106889832092791845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22048579404593221395194563 33072869106889832092791845)
        ·
          refine ⟨6201162957541843517398471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33072869106889832092791845 6201162957541843517398471)
          ·
            refine ⟨9301744436312765276097707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6201162957541843517398471 9301744436312765276097707)
            ·
              refine ⟨13952616654469147914146561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9301744436312765276097707 13952616654469147914146561)
              ·
                refine ⟨10464462490851860935609921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13952616654469147914146561 10464462490851860935609921)
                ·
                  refine ⟨7848346868138895701707441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10464462490851860935609921 7848346868138895701707441)
                  ·
                    refine ⟨5886260151104171776280581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7848346868138895701707441 5886260151104171776280581)
                    ·
                      refine ⟨1103673778332032208052609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5886260151104171776280581 1103673778332032208052609)
                      ·
                        rfl

theorem cell23_2149397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_2149397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149397 prefixEnd_2149397 := by exact prefixLift 2149397
  have htrace : WordTrace (prefixWord ++ tailWord_2149397) baseStart_2149397 baseEnd_2149397 := by
    simpa [prefixWord, tailWord_2149397, baseEnd_2149397] using wordTrace_append hprefix tailTrace_2149397
  have hstable : (prefixWord ++ tailWord_2149397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149397).length < 2 ^ (prefixWord ++ tailWord_2149397).sum := by decide
  have hdescent : baseEnd_2149397 < baseStart_2149397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149401 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 2, 2, 2]
def baseStart_2149401 : Nat := 118140960795 + 2149401 * 2 ^ 59
def prefixEnd_2149401 : Nat := 4983230072969 + 3 ^ 40 * 2149401 * 2
def baseEnd_2149401 : Nat := 1103675832254650192402591

theorem tailTrace_2149401 : CollatzResearch.WordTrace tailWord_2149401 prefixEnd_2149401 1103675832254650192402591 := by
  unfold tailWord_2149401
  simp only [CollatzResearch.WordTrace]
  refine ⟨78395094886094740310504057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52263396590729826873669371 78395094886094740310504057)
  ·
    refine ⟨58796321164571055232878043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78395094886094740310504057 58796321164571055232878043)
    ·
      refine ⟨88194481746856582849317065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58796321164571055232878043 88194481746856582849317065)
      ·
        refine ⟨66145861310142437136987799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88194481746856582849317065 66145861310142437136987799)
        ·
          refine ⟨99218791965213655705481699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66145861310142437136987799 99218791965213655705481699)
          ·
            refine ⟨148828187947820483558222549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99218791965213655705481699 148828187947820483558222549)
            ·
              refine ⟨3488160655027042583395841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 148828187947820483558222549 3488160655027042583395841)
              ·
                refine ⟨2616120491270281937546881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3488160655027042583395841 2616120491270281937546881)
                ·
                  refine ⟨1962090368452711453160161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2616120491270281937546881 1962090368452711453160161)
                  ·
                    refine ⟨1471567776339533589870121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1962090368452711453160161 1471567776339533589870121)
                    ·
                      refine ⟨1103675832254650192402591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471567776339533589870121 1103675832254650192402591)
                      ·
                        rfl

theorem cell23_2149401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_2149401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149401 prefixEnd_2149401 := by exact prefixLift 2149401
  have htrace : WordTrace (prefixWord ++ tailWord_2149401) baseStart_2149401 baseEnd_2149401 := by
    simpa [prefixWord, tailWord_2149401, baseEnd_2149401] using wordTrace_append hprefix tailTrace_2149401
  have hstable : (prefixWord ++ tailWord_2149401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149401).length < 2 ^ (prefixWord ++ tailWord_2149401).sum := by decide
  have hdescent : baseEnd_2149401 < baseStart_2149401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149407 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 7]
def baseStart_2149407 : Nat := 118140960795 + 2149407 * 2 ^ 59
def prefixEnd_2149407 : Nat := 4983230072969 + 3 ^ 40 * 2149407 * 2
def baseEnd_2149407 : Nat := 122630990348730796547507

theorem tailTrace_2149407 : CollatzResearch.WordTrace tailWord_2149407 prefixEnd_2149407 122630990348730796547507 := by
  unfold tailWord_2149407
  simp only [CollatzResearch.WordTrace]
  refine ⟨78395313724073003335222475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52263542482715335556814983 78395313724073003335222475)
  ·
    refine ⟨117592970586109505002833713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78395313724073003335222475 117592970586109505002833713)
    ·
      refine ⟨88194727939582128752125285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117592970586109505002833713 88194727939582128752125285)
      ·
        refine ⟨16536511488671649141023491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88194727939582128752125285 16536511488671649141023491)
        ·
          refine ⟨24804767233007473711535237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16536511488671649141023491 24804767233007473711535237)
          ·
            refine ⟨4650893856188901320912857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24804767233007473711535237 4650893856188901320912857)
            ·
              refine ⟨3488170392141675990684643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4650893856188901320912857 3488170392141675990684643)
              ·
                refine ⟨5232255588212513986026965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488170392141675990684643 5232255588212513986026965)
                ·
                  refine ⟨122630990348730796547507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5232255588212513986026965 122630990348730796547507)
                  ·
                    rfl

theorem cell23_2149407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 7].length) (baseStart_2149407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149407 prefixEnd_2149407 := by exact prefixLift 2149407
  have htrace : WordTrace (prefixWord ++ tailWord_2149407) baseStart_2149407 baseEnd_2149407 := by
    simpa [prefixWord, tailWord_2149407, baseEnd_2149407] using wordTrace_append hprefix tailTrace_2149407
  have hstable : (prefixWord ++ tailWord_2149407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149407).length < 2 ^ (prefixWord ++ tailWord_2149407).sum := by decide
  have hdescent : baseEnd_2149407 < baseStart_2149407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149418 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_2149418 : Nat := 118140960795 + 2149418 * 2 ^ 59
def prefixEnd_2149418 : Nat := 4983230072969 + 3 ^ 40 * 2149418 * 2
def baseEnd_2149418 : Nat := 1103684561425776625890013

theorem tailTrace_2149418 : CollatzResearch.WordTrace tailWord_2149418 prefixEnd_2149418 1103684561425776625890013 := by
  unfold tailWord_2149418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19598928731758288053468227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52263809951355434809248605 19598928731758288053468227)
  ·
    refine ⟨29398393097637432080202341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19598928731758288053468227 29398393097637432080202341)
    ·
      refine ⟨5512198705807018515037939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29398393097637432080202341 5512198705807018515037939)
      ·
        refine ⟨8268298058710527772556909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5512198705807018515037939 8268298058710527772556909)
        ·
          refine ⟨3100611772016447914708841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8268298058710527772556909 3100611772016447914708841)
          ·
            refine ⟨2325458829012335936031631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3100611772016447914708841 2325458829012335936031631)
            ·
              refine ⟨3488188243518503904047447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325458829012335936031631 3488188243518503904047447)
              ·
                refine ⟨5232282365277755856071171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488188243518503904047447 5232282365277755856071171)
                ·
                  refine ⟨7848423547916633784106757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5232282365277755856071171 7848423547916633784106757)
                  ·
                    refine ⟨1471579415234368834520017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7848423547916633784106757 1471579415234368834520017)
                    ·
                      refine ⟨1103684561425776625890013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471579415234368834520017 1103684561425776625890013)
                      ·
                        rfl

theorem cell23_2149418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_2149418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149418 prefixEnd_2149418 := by exact prefixLift 2149418
  have htrace : WordTrace (prefixWord ++ tailWord_2149418) baseStart_2149418 baseEnd_2149418 := by
    simpa [prefixWord, tailWord_2149418, baseEnd_2149418] using wordTrace_append hprefix tailTrace_2149418
  have hstable : (prefixWord ++ tailWord_2149418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149418).length < 2 ^ (prefixWord ++ tailWord_2149418).sum := by decide
  have hdescent : baseEnd_2149418 < baseStart_2149418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149420 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_2149420 : Nat := 118140960795 + 2149420 * 2 ^ 59
def prefixEnd_2149420 : Nat := 4983230072969 + 3 ^ 40 * 2149420 * 2
def baseEnd_2149420 : Nat := 367895196129028539355001

theorem tailTrace_2149420 : CollatzResearch.WordTrace tailWord_2149420 prefixEnd_2149420 367895196129028539355001 := by
  unfold tailWord_2149420
  simp only [CollatzResearch.WordTrace]
  refine ⟨39197893936512953277722857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52263858582017271036963809 39197893936512953277722857)
  ·
    refine ⟨29398420452384714958292143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39197893936512953277722857 29398420452384714958292143)
    ·
      refine ⟨44097630678577072437438215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29398420452384714958292143 44097630678577072437438215)
      ·
        refine ⟨66146446017865608656157323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44097630678577072437438215 66146446017865608656157323)
        ·
          refine ⟨99219669026798412984235985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66146446017865608656157323 99219669026798412984235985)
          ·
            refine ⟨74414751770098809738176989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99219669026798412984235985 74414751770098809738176989)
            ·
              refine ⟨27905531913787053651816371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74414751770098809738176989 27905531913787053651816371)
              ·
                refine ⟨41858297870680580477724557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27905531913787053651816371 41858297870680580477724557)
                ·
                  refine ⟨15696861701505217679146709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41858297870680580477724557 15696861701505217679146709)
                  ·
                    refine ⟨367895196129028539355001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15696861701505217679146709 367895196129028539355001)
                    ·
                      rfl

theorem cell23_2149420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_2149420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149420 prefixEnd_2149420 := by exact prefixLift 2149420
  have htrace : WordTrace (prefixWord ++ tailWord_2149420) baseStart_2149420 baseEnd_2149420 := by
    simpa [prefixWord, tailWord_2149420, baseEnd_2149420] using wordTrace_append hprefix tailTrace_2149420
  have hstable : (prefixWord ++ tailWord_2149420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149420).length < 2 ^ (prefixWord ++ tailWord_2149420).sum := by decide
  have hdescent : baseEnd_2149420 < baseStart_2149420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149437 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_2149437 : Nat := 118140960795 + 2149437 * 2 ^ 59
def prefixEnd_2149437 : Nat := 4983230072969 + 3 ^ 40 * 2149437 * 2
def baseEnd_2149437 : Nat := 367898105852737350517475

theorem tailTrace_2149437 : CollatzResearch.WordTrace tailWord_2149437 prefixEnd_2149437 367898105852737350517475 := by
  unfold tailWord_2149437
  simp only [CollatzResearch.WordTrace]
  refine ⟨78396407913964318458814565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52264271942642878972543043 78396407913964318458814565)
  ·
    refine ⟨14699326483868309711027731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78396407913964318458814565 14699326483868309711027731)
    ·
      refine ⟨22048989725802464566541597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14699326483868309711027731 22048989725802464566541597)
      ·
        refine ⟨8268371147175924212453099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22048989725802464566541597 8268371147175924212453099)
        ·
          refine ⟨12402556720763886318679649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8268371147175924212453099 12402556720763886318679649)
          ·
            refine ⟨9301917540572914739009737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12402556720763886318679649 9301917540572914739009737)
            ·
              refine ⟨6976438155429686054257303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9301917540572914739009737 6976438155429686054257303)
              ·
                refine ⟨10464657233144529081385955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6976438155429686054257303 10464657233144529081385955)
                ·
                  refine ⟨15696985849716793622078933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10464657233144529081385955 15696985849716793622078933)
                  ·
                    refine ⟨367898105852737350517475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15696985849716793622078933 367898105852737350517475)
                    ·
                      rfl

theorem cell23_2149437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_2149437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149437 prefixEnd_2149437 := by exact prefixLift 2149437
  have htrace : WordTrace (prefixWord ++ tailWord_2149437) baseStart_2149437 baseEnd_2149437 := by
    simpa [prefixWord, tailWord_2149437, baseEnd_2149437] using wordTrace_append hprefix tailTrace_2149437
  have hstable : (prefixWord ++ tailWord_2149437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149437).length < 2 ^ (prefixWord ++ tailWord_2149437).sum := by decide
  have hdescent : baseEnd_2149437 < baseStart_2149437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149457 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_2149457 : Nat := 118140960795 + 2149457 * 2 ^ 59
def prefixEnd_2149457 : Nat := 4983230072969 + 3 ^ 40 * 2149457 * 2
def baseEnd_2149457 : Nat := 1103704587171301973302333

theorem tailTrace_2149457 : CollatzResearch.WordTrace tailWord_2149457 prefixEnd_2149457 1103704587171301973302333 := by
  unfold tailWord_2149457
  simp only [CollatzResearch.WordTrace]
  refine ⟨78397137373891861874542625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52264758249261241249695083 78397137373891861874542625)
  ·
    refine ⟨58797853030418896405906969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78397137373891861874542625 58797853030418896405906969)
    ·
      refine ⟨44098389772814172304430227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58797853030418896405906969 44098389772814172304430227)
      ·
        refine ⟨66147584659221258456645341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44098389772814172304430227 66147584659221258456645341)
        ·
          refine ⟨24805344247207971921242003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66147584659221258456645341 24805344247207971921242003)
          ·
            refine ⟨37208016370811957881863005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24805344247207971921242003 37208016370811957881863005)
            ·
              refine ⟨13953006139054484205698627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37208016370811957881863005 13953006139054484205698627)
              ·
                refine ⟨20929509208581726308547941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13953006139054484205698627 20929509208581726308547941)
                ·
                  refine ⟨3924282976609073682852739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20929509208581726308547941 3924282976609073682852739)
                  ·
                    refine ⟨5886424464913610524279109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3924282976609073682852739 5886424464913610524279109)
                    ·
                      refine ⟨1103704587171301973302333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5886424464913610524279109 1103704587171301973302333)
                      ·
                        rfl

theorem cell23_2149457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_2149457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149457 prefixEnd_2149457 := by exact prefixLift 2149457
  have htrace : WordTrace (prefixWord ++ tailWord_2149457) baseStart_2149457 baseEnd_2149457 := by
    simpa [prefixWord, tailWord_2149457, baseEnd_2149457] using wordTrace_append hprefix tailTrace_2149457
  have hstable : (prefixWord ++ tailWord_2149457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149457).length < 2 ^ (prefixWord ++ tailWord_2149457).sum := by decide
  have hdescent : baseEnd_2149457 < baseStart_2149457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149469 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_2149469 : Nat := 118140960795 + 2149469 * 2 ^ 59
def prefixEnd_2149469 : Nat := 4983230072969 + 3 ^ 40 * 2149469 * 2
def baseEnd_2149469 : Nat := 1103710748939155926352279

theorem tailTrace_2149469 : CollatzResearch.WordTrace tailWord_2149469 prefixEnd_2149469 1103710748939155926352279 := by
  unfold tailWord_2149469
  simp only [CollatzResearch.WordTrace]
  refine ⟨78397575049848387923979461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52265050033232258615986307 78397575049848387923979461)
  ·
    refine ⟨14699545321846572735746149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78397575049848387923979461 14699545321846572735746149)
    ·
      refine ⟨2756164747846232387952403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14699545321846572735746149 2756164747846232387952403)
      ·
        refine ⟨4134247121769348581928605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2756164747846232387952403 4134247121769348581928605)
        ·
          refine ⟨1550342670663505718223227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4134247121769348581928605 1550342670663505718223227)
          ·
            refine ⟨2325514005995258577334841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550342670663505718223227 2325514005995258577334841)
            ·
              refine ⟨1744135504496443933001131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2325514005995258577334841 1744135504496443933001131)
              ·
                refine ⟨2616203256744665899501697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744135504496443933001131 2616203256744665899501697)
                ·
                  refine ⟨1962152442558499424626273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2616203256744665899501697 1962152442558499424626273)
                  ·
                    refine ⟨1471614331918874568469705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1962152442558499424626273 1471614331918874568469705)
                    ·
                      refine ⟨1103710748939155926352279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471614331918874568469705 1103710748939155926352279)
                      ·
                        rfl

theorem cell23_2149469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_2149469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149469 prefixEnd_2149469 := by exact prefixLift 2149469
  have htrace : WordTrace (prefixWord ++ tailWord_2149469) baseStart_2149469 baseEnd_2149469 := by
    simpa [prefixWord, tailWord_2149469, baseEnd_2149469] using wordTrace_append hprefix tailTrace_2149469
  have hstable : (prefixWord ++ tailWord_2149469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149469).length < 2 ^ (prefixWord ++ tailWord_2149469).sum := by decide
  have hdescent : baseEnd_2149469 < baseStart_2149469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149501 : List Nat := [1, 4, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_2149501 : Nat := 118140960795 + 2149501 * 2 ^ 59
def prefixEnd_2149501 : Nat := 4983230072969 + 3 ^ 40 * 2149501 * 2
def baseEnd_2149501 : Nat := 367909060106699933717377

theorem tailTrace_2149501 : CollatzResearch.WordTrace tailWord_2149501 prefixEnd_2149501 367909060106699933717377 := by
  unfold tailWord_2149501
  simp only [CollatzResearch.WordTrace]
  refine ⟨78398742185732457389144357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52265828123821638259429571 78398742185732457389144357)
  ·
    refine ⟨14699764159824835760464567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78398742185732457389144357 14699764159824835760464567)
    ·
      refine ⟨22049646239737253640696851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14699764159824835760464567 22049646239737253640696851)
      ·
        refine ⟨33074469359605880461045277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22049646239737253640696851 33074469359605880461045277)
        ·
          refine ⟨12402926009852205172891979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33074469359605880461045277 12402926009852205172891979)
          ·
            refine ⟨18604389014778307759337969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12402926009852205172891979 18604389014778307759337969)
            ·
              refine ⟨13953291761083730819503477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18604389014778307759337969 13953291761083730819503477)
              ·
                refine ⟨1308121102601599764328451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13953291761083730819503477 1308121102601599764328451)
                ·
                  refine ⟨1962181653902399646492677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308121102601599764328451 1962181653902399646492677)
                  ·
                    refine ⟨367909060106699933717377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962181653902399646492677 367909060106699933717377)
                    ·
                      rfl

theorem cell23_2149501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_2149501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149501 prefixEnd_2149501 := by exact prefixLift 2149501
  have htrace : WordTrace (prefixWord ++ tailWord_2149501) baseStart_2149501 baseEnd_2149501 := by
    simpa [prefixWord, tailWord_2149501, baseEnd_2149501] using wordTrace_append hprefix tailTrace_2149501
  have hstable : (prefixWord ++ tailWord_2149501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149501).length < 2 ^ (prefixWord ++ tailWord_2149501).sum := by decide
  have hdescent : baseEnd_2149501 < baseStart_2149501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149514 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 6]
def baseStart_2149514 : Nat := 118140960795 + 2149514 * 2 ^ 59
def prefixEnd_2149514 : Nat := 4983230072969 + 3 ^ 40 * 2149514 * 2
def baseEnd_2149514 : Nat := 122637095063178694476619

theorem tailTrace_2149514 : CollatzResearch.WordTrace tailWord_2149514 prefixEnd_2149514 122637095063178694476619 := by
  unfold tailWord_2149514
  simp only [CollatzResearch.WordTrace]
  refine ⟨19599804083671340152341899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52266144223123573739578397 19599804083671340152341899)
  ·
    refine ⟨29399706125507010228512849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19599804083671340152341899 29399706125507010228512849)
    ·
      refine ⟨22049779594130257671384637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29399706125507010228512849 22049779594130257671384637)
      ·
        refine ⟨8268667347798846626769239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22049779594130257671384637 8268667347798846626769239)
        ·
          refine ⟨12403001021698269940153859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8268667347798846626769239 12403001021698269940153859)
          ·
            refine ⟨18604501532547404910230789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12403001021698269940153859 18604501532547404910230789)
            ·
              refine ⟨3488344037352638420668273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18604501532547404910230789 3488344037352638420668273)
              ·
                refine ⟨2616258028014478815501205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3488344037352638420668273 2616258028014478815501205)
                ·
                  refine ⟨122637095063178694476619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2616258028014478815501205 122637095063178694476619)
                  ·
                    rfl

theorem cell23_2149514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_2149514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149514 prefixEnd_2149514 := by exact prefixLift 2149514
  have htrace : WordTrace (prefixWord ++ tailWord_2149514) baseStart_2149514 baseEnd_2149514 := by
    simpa [prefixWord, tailWord_2149514, baseEnd_2149514] using wordTrace_append hprefix tailTrace_2149514
  have hstable : (prefixWord ++ tailWord_2149514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149514).length < 2 ^ (prefixWord ++ tailWord_2149514).sum := by decide
  have hdescent : baseEnd_2149514 < baseStart_2149514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149518 : List Nat := [4, 1, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_2149518 : Nat := 118140960795 + 2149518 * 2 ^ 59
def prefixEnd_2149518 : Nat := 4983230072969 + 3 ^ 40 * 2149518 * 2
def baseEnd_2149518 : Nat := 367911969830408744879851

theorem tailTrace_2149518 : CollatzResearch.WordTrace tailWord_2149518 prefixEnd_2149518 367911969830408744879851 := by
  unfold tailWord_2149518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9799920278333858661564151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52266241484447246195008805 9799920278333858661564151)
  ·
    refine ⟨14699880417500787992346227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9799920278333858661564151 14699880417500787992346227)
    ·
      refine ⟨22049820626251181988519341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14699880417500787992346227 22049820626251181988519341)
      ·
        refine ⟨8268682734844193245694753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22049820626251181988519341 8268682734844193245694753)
        ·
          refine ⟨6201512051133144934271065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8268682734844193245694753 6201512051133144934271065)
          ·
            refine ⟨4651134038349858700703299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6201512051133144934271065 4651134038349858700703299)
            ·
              refine ⟨6976701057524788051054949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4651134038349858700703299 6976701057524788051054949)
              ·
                refine ⟨1308131448285897759572803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6976701057524788051054949 1308131448285897759572803)
                ·
                  refine ⟨1962197172428846639359205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308131448285897759572803 1962197172428846639359205)
                  ·
                    refine ⟨367911969830408744879851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962197172428846639359205 367911969830408744879851)
                    ·
                      rfl

theorem cell23_2149518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_2149518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149518 prefixEnd_2149518 := by exact prefixLift 2149518
  have htrace : WordTrace (prefixWord ++ tailWord_2149518) baseStart_2149518 baseEnd_2149518 := by
    simpa [prefixWord, tailWord_2149518, baseEnd_2149518] using wordTrace_append hprefix tailTrace_2149518
  have hstable : (prefixWord ++ tailWord_2149518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149518).length < 2 ^ (prefixWord ++ tailWord_2149518).sum := by decide
  have hdescent : baseEnd_2149518 < baseStart_2149518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149537 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2149537 : Nat := 118140960795 + 2149537 * 2 ^ 59
def prefixEnd_2149537 : Nat := 4983230072969 + 3 ^ 40 * 2149537 * 2
def baseEnd_2149537 : Nat := 1103745665623661660301965

theorem tailTrace_2149537 : CollatzResearch.WordTrace tailWord_2149537 prefixEnd_2149537 1103745665623661660301965 := by
  unfold tailWord_2149537
  simp only [CollatzResearch.WordTrace]
  refine ⟨78400055213602035537454865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52266703475734690358303243 78400055213602035537454865)
  ·
    refine ⟨58800041410201526653091149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78400055213602035537454865 58800041410201526653091149)
    ·
      refine ⟨22050015528825572494909181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58800041410201526653091149 22050015528825572494909181)
      ·
        refine ⟨8268755823309589685590943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22050015528825572494909181 8268755823309589685590943)
        ·
          refine ⟨12403133734964384528386415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8268755823309589685590943 12403133734964384528386415)
          ·
            refine ⟨18604700602446576792579623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12403133734964384528386415 18604700602446576792579623)
            ·
              refine ⟨27907050903669865188869435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18604700602446576792579623 27907050903669865188869435)
              ·
                refine ⟨41860576355504797783304153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27907050903669865188869435 41860576355504797783304153)
                ·
                  refine ⟨31395432266628598337478115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41860576355504797783304153 31395432266628598337478115)
                  ·
                    refine ⟨47093148399942897506217173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31395432266628598337478115 47093148399942897506217173)
                    ·
                      refine ⟨1103745665623661660301965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47093148399942897506217173 1103745665623661660301965)
                      ·
                        rfl

theorem cell23_2149537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2149537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149537 prefixEnd_2149537 := by exact prefixLift 2149537
  have htrace : WordTrace (prefixWord ++ tailWord_2149537) baseStart_2149537 baseEnd_2149537 := by
    simpa [prefixWord, tailWord_2149537, baseEnd_2149537] using wordTrace_append hprefix tailTrace_2149537
  have hstable : (prefixWord ++ tailWord_2149537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149537).length < 2 ^ (prefixWord ++ tailWord_2149537).sum := by decide
  have hdescent : baseEnd_2149537 < baseStart_2149537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149541 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 3, 1, 3]
def baseStart_2149541 : Nat := 118140960795 + 2149541 * 2 ^ 59
def prefixEnd_2149541 : Nat := 4983230072969 + 3 ^ 40 * 2149541 * 2
def baseEnd_2149541 : Nat := 1103747719546279644651947

theorem tailTrace_2149541 : CollatzResearch.WordTrace tailWord_2149541 prefixEnd_2149541 1103747719546279644651947 := by
  unfold tailWord_2149541
  simp only [CollatzResearch.WordTrace]
  refine ⟨78400201105587544220600477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52266800737058362813733651 78400201105587544220600477)
  ·
    refine ⟨29400075414595329082725179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78400201105587544220600477 29400075414595329082725179)
    ·
      refine ⟨44100113121892993624087769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29400075414595329082725179 44100113121892993624087769)
      ·
        refine ⟨33075084841419745218065827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44100113121892993624087769 33075084841419745218065827)
        ·
          refine ⟨49612627262129617827098741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33075084841419745218065827 49612627262129617827098741)
          ·
            refine ⟨4651183805824651671290507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49612627262129617827098741 4651183805824651671290507)
            ·
              refine ⟨6976775708736977506935761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4651183805824651671290507 6976775708736977506935761)
              ·
                refine ⟨5232581781552733130201821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6976775708736977506935761 5232581781552733130201821)
                ·
                  refine ⟨1962218168082274923825683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5232581781552733130201821 1962218168082274923825683)
                  ·
                    refine ⟨2943327252123412385738525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1962218168082274923825683 2943327252123412385738525)
                    ·
                      refine ⟨1103747719546279644651947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2943327252123412385738525 1103747719546279644651947)
                      ·
                        rfl

theorem cell23_2149541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_2149541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149541 prefixEnd_2149541 := by exact prefixLift 2149541
  have htrace : WordTrace (prefixWord ++ tailWord_2149541) baseStart_2149541 baseEnd_2149541 := by
    simpa [prefixWord, tailWord_2149541, baseEnd_2149541] using wordTrace_append hprefix tailTrace_2149541
  have hstable : (prefixWord ++ tailWord_2149541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149541).length < 2 ^ (prefixWord ++ tailWord_2149541).sum := by decide
  have hdescent : baseEnd_2149541 < baseStart_2149541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149551 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 2, 3, 2]
def baseStart_2149551 : Nat := 118140960795 + 2149551 * 2 ^ 59
def prefixEnd_2149551 : Nat := 4983230072969 + 3 ^ 40 * 2149551 * 2
def baseEnd_2149551 : Nat := 1103752854352824605526901

theorem tailTrace_2149551 : CollatzResearch.WordTrace tailWord_2149551 prefixEnd_2149551 1103752854352824605526901 := by
  unfold tailWord_2149551
  simp only [CollatzResearch.WordTrace]
  refine ⟨78400565835551315928464507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52267043890367543952309671 78400565835551315928464507)
  ·
    refine ⟨117600848753326973892696761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78400565835551315928464507 117600848753326973892696761)
    ·
      refine ⟨88200636564995230419522571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117600848753326973892696761 88200636564995230419522571)
      ·
        refine ⟨132300954847492845629283857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88200636564995230419522571 132300954847492845629283857)
        ·
          refine ⟨99225716135619634221962893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132300954847492845629283857 99225716135619634221962893)
          ·
            refine ⟨37209643550857362833236085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99225716135619634221962893 37209643550857362833236085)
            ·
              refine ⟨3488404082892877765615883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37209643550857362833236085 3488404082892877765615883)
              ·
                refine ⟨5232606124339316648423825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488404082892877765615883 5232606124339316648423825)
                ·
                  refine ⟨3924454593254487486317869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5232606124339316648423825 3924454593254487486317869)
                  ·
                    refine ⟨1471670472470432807369201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3924454593254487486317869 1471670472470432807369201)
                    ·
                      refine ⟨1103752854352824605526901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471670472470432807369201 1103752854352824605526901)
                      ·
                        rfl

theorem cell23_2149551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 3, 2].length) (baseStart_2149551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149551 prefixEnd_2149551 := by exact prefixLift 2149551
  have htrace : WordTrace (prefixWord ++ tailWord_2149551) baseStart_2149551 baseEnd_2149551 := by
    simpa [prefixWord, tailWord_2149551, baseEnd_2149551] using wordTrace_append hprefix tailTrace_2149551
  have hstable : (prefixWord ++ tailWord_2149551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149551).length < 2 ^ (prefixWord ++ tailWord_2149551).sum := by decide
  have hdescent : baseEnd_2149551 < baseStart_2149551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149561 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 1, 5]
def baseStart_2149561 : Nat := 118140960795 + 2149561 * 2 ^ 59
def prefixEnd_2149561 : Nat := 4983230072969 + 3 ^ 40 * 2149561 * 2
def baseEnd_2149561 : Nat := 367919329719789855467285

theorem tailTrace_2149561 : CollatzResearch.WordTrace tailWord_2149561 prefixEnd_2149561 367919329719789855467285 := by
  unfold tailWord_2149561
  simp only [CollatzResearch.WordTrace]
  refine ⟨78400930565515087636328537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52267287043676725090885691 78400930565515087636328537)
  ·
    refine ⟨58800697924136315727246403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78400930565515087636328537 58800697924136315727246403)
    ·
      refine ⟨88201046886204473590869605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58800697924136315727246403 88201046886204473590869605)
      ·
        refine ⟨16537696291163338798288051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88201046886204473590869605 16537696291163338798288051)
        ·
          refine ⟨24806544436745008197432077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16537696291163338798288051 24806544436745008197432077)
          ·
            refine ⟨9302454163779378074037029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24806544436745008197432077 9302454163779378074037029)
            ·
              refine ⟨1744210155708633388881943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9302454163779378074037029 1744210155708633388881943)
              ·
                refine ⟨2616315233562950083322915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744210155708633388881943 2616315233562950083322915)
                ·
                  refine ⟨3924472850344425124984373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616315233562950083322915 3924472850344425124984373)
                  ·
                    refine ⟨367919329719789855467285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3924472850344425124984373 367919329719789855467285)
                    ·
                      rfl

theorem cell23_2149561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 5].length) (baseStart_2149561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149561 prefixEnd_2149561 := by exact prefixLift 2149561
  have htrace : WordTrace (prefixWord ++ tailWord_2149561) baseStart_2149561 baseEnd_2149561 := by
    simpa [prefixWord, tailWord_2149561, baseEnd_2149561] using wordTrace_append hprefix tailTrace_2149561
  have hstable : (prefixWord ++ tailWord_2149561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149561).length < 2 ^ (prefixWord ++ tailWord_2149561).sum := by decide
  have hdescent : baseEnd_2149561 < baseStart_2149561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149601 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_2149601 : Nat := 118140960795 + 2149601 * 2 ^ 59
def prefixEnd_2149601 : Nat := 4983230072969 + 3 ^ 40 * 2149601 * 2
def baseEnd_2149601 : Nat := 1103778528385549409901671

theorem tailTrace_2149601 : CollatzResearch.WordTrace tailWord_2149601 prefixEnd_2149601 1103778528385549409901671 := by
  unfold tailWord_2149601
  simp only [CollatzResearch.WordTrace]
  refine ⟨78402389485370174467784657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52268259656913449645189771 78402389485370174467784657)
  ·
    refine ⟨58801792114027630850838493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78402389485370174467784657 58801792114027630850838493)
    ·
      refine ⟨22050672042760361569064435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58801792114027630850838493 22050672042760361569064435)
      ·
        refine ⟨33076008064140542353596653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22050672042760361569064435 33076008064140542353596653)
        ·
          refine ⟨12403503024052703382598745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33076008064140542353596653 12403503024052703382598745)
          ·
            refine ⟨9302627268039527536949059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12403503024052703382598745 9302627268039527536949059)
            ·
              refine ⟨13953940902059291305423589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9302627268039527536949059 13953940902059291305423589)
              ·
                refine ⟨2616363919136117119766923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13953940902059291305423589 2616363919136117119766923)
                ·
                  refine ⟨3924545878704175679650385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2616363919136117119766923 3924545878704175679650385)
                  ·
                    refine ⟨2943409409028131759737789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3924545878704175679650385 2943409409028131759737789)
                    ·
                      refine ⟨1103778528385549409901671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2943409409028131759737789 1103778528385549409901671)
                      ·
                        rfl

theorem cell23_2149601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_2149601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149601 prefixEnd_2149601 := by exact prefixLift 2149601
  have htrace : WordTrace (prefixWord ++ tailWord_2149601) baseStart_2149601 baseEnd_2149601 := by
    simpa [prefixWord, tailWord_2149601, baseEnd_2149601] using wordTrace_append hprefix tailTrace_2149601
  have hstable : (prefixWord ++ tailWord_2149601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149601).length < 2 ^ (prefixWord ++ tailWord_2149601).sum := by decide
  have hdescent : baseEnd_2149601 < baseStart_2149601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149604 : List Nat := [2, 3, 1, 1, 1, 2, 6, 7]
def baseStart_2149604 : Nat := 118140960795 + 2149604 * 2 ^ 59
def prefixEnd_2149604 : Nat := 4983230072969 + 3 ^ 40 * 2149604 * 2
def baseEnd_2149604 : Nat := 40880743289907885117191

theorem tailTrace_2149604 : CollatzResearch.WordTrace tailWord_2149604 prefixEnd_2149604 40880743289907885117191 := by
  unfold tailWord_2149604
  simp only [CollatzResearch.WordTrace]
  refine ⟨39201249452179652990071933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52268332602906203986762577 39201249452179652990071933)
  ·
    refine ⟨14700468544567369871276975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39201249452179652990071933 14700468544567369871276975)
    ·
      refine ⟨22050702816851054806915463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14700468544567369871276975 22050702816851054806915463)
      ·
        refine ⟨33076054225276582210373195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22050702816851054806915463 33076054225276582210373195)
        ·
          refine ⟨49614081337914873315559793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33076054225276582210373195 49614081337914873315559793)
          ·
            refine ⟨37210561003436154986669845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49614081337914873315559793 37210561003436154986669845)
            ·
              refine ⟨1744245047036069765000149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37210561003436154986669845 1744245047036069765000149)
              ·
                refine ⟨40880743289907885117191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1744245047036069765000149 40880743289907885117191)
                ·
                  rfl

theorem cell23_2149604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 7].length) (baseStart_2149604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149604 prefixEnd_2149604 := by exact prefixLift 2149604
  have htrace : WordTrace (prefixWord ++ tailWord_2149604) baseStart_2149604 baseEnd_2149604 := by
    simpa [prefixWord, tailWord_2149604, baseEnd_2149604] using wordTrace_append hprefix tailTrace_2149604
  have hstable : (prefixWord ++ tailWord_2149604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149604).length < 2 ^ (prefixWord ++ tailWord_2149604).sum := by decide
  have hdescent : baseEnd_2149604 < baseStart_2149604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149617 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 1, 9]
def baseStart_2149617 : Nat := 118140960795 + 2149617 * 2 ^ 59
def prefixEnd_2149617 : Nat := 4983230072969 + 3 ^ 40 * 2149617 * 2
def baseEnd_2149617 : Nat := 367928914692007115767199

theorem tailTrace_2149617 : CollatzResearch.WordTrace tailWord_2149617 prefixEnd_2149617 367928914692007115767199 := by
  unfold tailWord_2149617
  simp only [CollatzResearch.WordTrace]
  refine ⟨78402973053312209200367105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52268648702208139466911403 78402973053312209200367105)
  ·
    refine ⟨58802229789984156900275329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78402973053312209200367105 58802229789984156900275329)
    ·
      refine ⟨44101672342488117675206497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58802229789984156900275329 44101672342488117675206497)
      ·
        refine ⟨33076254256866088256404873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44101672342488117675206497 33076254256866088256404873)
        ·
          refine ⟨24807190692649566192303655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33076254256866088256404873 24807190692649566192303655)
          ·
            refine ⟨37210786038974349288455483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24807190692649566192303655 37210786038974349288455483)
            ·
              refine ⟨55816179058461523932683225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37210786038974349288455483 55816179058461523932683225)
              ·
                refine ⟨41862134293846142949512419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55816179058461523932683225 41862134293846142949512419)
                ·
                  refine ⟨62793201440769214424268629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41862134293846142949512419 62793201440769214424268629)
                  ·
                    refine ⟨367928914692007115767199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 62793201440769214424268629 367928914692007115767199)
                    ·
                      rfl

theorem cell23_2149617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_2149617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149617 prefixEnd_2149617 := by exact prefixLift 2149617
  have htrace : WordTrace (prefixWord ++ tailWord_2149617) baseStart_2149617 baseEnd_2149617 := by
    simpa [prefixWord, tailWord_2149617, baseEnd_2149617] using wordTrace_append hprefix tailTrace_2149617
  have hstable : (prefixWord ++ tailWord_2149617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149617).length < 2 ^ (prefixWord ++ tailWord_2149617).sum := by decide
  have hdescent : baseEnd_2149617 < baseStart_2149617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149631 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 4, 1, 3]
def baseStart_2149631 : Nat := 118140960795 + 2149631 * 2 ^ 59
def prefixEnd_2149631 : Nat := 4983230072969 + 3 ^ 40 * 2149631 * 2
def baseEnd_2149631 : Nat := 1103793932805184292526533

theorem tailTrace_2149631 : CollatzResearch.WordTrace tailWord_2149631 prefixEnd_2149631 1103793932805184292526533 := by
  unfold tailWord_2149631
  simp only [CollatzResearch.WordTrace]
  refine ⟨78403483675261489591376747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52268989116840993060917831 78403483675261489591376747)
  ·
    refine ⟨117605225512892234387065121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78403483675261489591376747 117605225512892234387065121)
    ·
      refine ⟨88203919134669175790298841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117605225512892234387065121 88203919134669175790298841)
      ·
        refine ⟨66152939351001881842724131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88203919134669175790298841 66152939351001881842724131)
        ·
          refine ⟨99229409026502822764086197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66152939351001881842724131 99229409026502822764086197)
          ·
            refine ⟨9302757096234639634133081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99229409026502822764086197 9302757096234639634133081)
            ·
              refine ⟨6977067822175979725599811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9302757096234639634133081 6977067822175979725599811)
              ·
                refine ⟨10465601733263969588399717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6977067822175979725599811 10465601733263969588399717)
                ·
                  refine ⟨1962300324986994297824947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10465601733263969588399717 1962300324986994297824947)
                  ·
                    refine ⟨2943450487480491446737421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1962300324986994297824947 2943450487480491446737421)
                    ·
                      refine ⟨1103793932805184292526533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2943450487480491446737421 1103793932805184292526533)
                      ·
                        rfl

theorem cell23_2149631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_2149631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149631 prefixEnd_2149631 := by exact prefixLift 2149631
  have htrace : WordTrace (prefixWord ++ tailWord_2149631) baseStart_2149631 baseEnd_2149631 := by
    simpa [prefixWord, tailWord_2149631, baseEnd_2149631] using wordTrace_append hprefix tailTrace_2149631
  have hstable : (prefixWord ++ tailWord_2149631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149631).length < 2 ^ (prefixWord ++ tailWord_2149631).sum := by decide
  have hdescent : baseEnd_2149631 < baseStart_2149631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149641 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 3, 3, 2]
def baseStart_2149641 : Nat := 118140960795 + 2149641 * 2 ^ 59
def prefixEnd_2149641 : Nat := 4983230072969 + 3 ^ 40 * 2149641 * 2
def baseEnd_2149641 : Nat := 1103799067611729253401487

theorem tailTrace_2149641 : CollatzResearch.WordTrace tailWord_2149641 prefixEnd_2149641 1103799067611729253401487 := by
  unfold tailWord_2149641
  simp only [CollatzResearch.WordTrace]
  refine ⟨78403848405225261299240777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52269232270150174199493851 78403848405225261299240777)
  ·
    refine ⟨58802886303918945974430583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78403848405225261299240777 58802886303918945974430583)
    ·
      refine ⟨88204329455878418961645875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58802886303918945974430583 88204329455878418961645875)
      ·
        refine ⟨132306494183817628442468813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88204329455878418961645875 132306494183817628442468813)
        ·
          refine ⟨49614935318931610665925805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132306494183817628442468813 49614935318931610665925805)
          ·
            refine ⟨18605600744599353999722177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49614935318931610665925805 18605600744599353999722177)
            ·
              refine ⟨13954200558449515499791633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18605600744599353999722177 13954200558449515499791633)
              ·
                refine ⟨10465650418837136624843725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13954200558449515499791633 10465650418837136624843725)
                ·
                  refine ⟨3924618907063926234316397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10465650418837136624843725 3924618907063926234316397)
                  ·
                    refine ⟨1471732090148972337868649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3924618907063926234316397 1471732090148972337868649)
                    ·
                      refine ⟨1103799067611729253401487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471732090148972337868649 1103799067611729253401487)
                      ·
                        rfl

theorem cell23_2149641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 3, 2].length) (baseStart_2149641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149641 prefixEnd_2149641 := by exact prefixLift 2149641
  have htrace : WordTrace (prefixWord ++ tailWord_2149641) baseStart_2149641 baseEnd_2149641 := by
    simpa [prefixWord, tailWord_2149641, baseEnd_2149641] using wordTrace_append hprefix tailTrace_2149641
  have hstable : (prefixWord ++ tailWord_2149641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149641).length < 2 ^ (prefixWord ++ tailWord_2149641).sum := by decide
  have hdescent : baseEnd_2149641 < baseStart_2149641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149657 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_2149657 : Nat := 118140960795 + 2149657 * 2 ^ 59
def prefixEnd_2149657 : Nat := 4983230072969 + 3 ^ 40 * 2149657 * 2
def baseEnd_2149657 : Nat := 1103807283302201190801413

theorem tailTrace_2149657 : CollatzResearch.WordTrace tailWord_2149657 prefixEnd_2149657 1103807283302201190801413 := by
  unfold tailWord_2149657
  simp only [CollatzResearch.WordTrace]
  refine ⟨78404431973167296031823225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52269621315444864021215483 78404431973167296031823225)
  ·
    refine ⟨58803323979875472023867419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78404431973167296031823225 58803323979875472023867419)
    ·
      refine ⟨88204985969813208035801129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58803323979875472023867419 88204985969813208035801129)
      ·
        refine ⟨66153739477359906026850847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88204985969813208035801129 66153739477359906026850847)
        ·
          refine ⟨99230609216039859040276271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66153739477359906026850847 99230609216039859040276271)
          ·
            refine ⟨148845913824059788560414407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99230609216039859040276271 148845913824059788560414407)
            ·
              refine ⟨223268870736089682840621611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148845913824059788560414407 223268870736089682840621611)
              ·
                refine ⟨334903306104134524260932417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223268870736089682840621611 334903306104134524260932417)
                ·
                  refine ⟨251177479578100893195699313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334903306104134524260932417 251177479578100893195699313)
                  ·
                    refine ⟨188383109683575669896774485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 251177479578100893195699313 188383109683575669896774485)
                    ·
                      refine ⟨1103807283302201190801413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 188383109683575669896774485 1103807283302201190801413)
                      ·
                        rfl

theorem cell23_2149657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_2149657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149657 prefixEnd_2149657 := by exact prefixLift 2149657
  have htrace : WordTrace (prefixWord ++ tailWord_2149657) baseStart_2149657 baseEnd_2149657 := by
    simpa [prefixWord, tailWord_2149657, baseEnd_2149657] using wordTrace_append hprefix tailTrace_2149657
  have hstable : (prefixWord ++ tailWord_2149657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149657).length < 2 ^ (prefixWord ++ tailWord_2149657).sum := by decide
  have hdescent : baseEnd_2149657 < baseStart_2149657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149658 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2]
def baseStart_2149658 : Nat := 118140960795 + 2149658 * 2 ^ 59
def prefixEnd_2149658 : Nat := 4983230072969 + 3 ^ 40 * 2149658 * 2
def baseEnd_2149658 : Nat := 1103807796782855686888909

theorem tailTrace_2149658 : CollatzResearch.WordTrace tailWord_2149658 prefixEnd_2149658 1103807796782855686888909 := by
  unfold tailWord_2149658
  simp only [CollatzResearch.WordTrace]
  refine ⟨19601117111540918300652407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52269645630775782135073085 19601117111540918300652407)
  ·
    refine ⟨29401675667311377450978611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19601117111540918300652407 29401675667311377450978611)
    ·
      refine ⟨44102513500967066176467917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29401675667311377450978611 44102513500967066176467917)
      ·
        refine ⟨16538442562862649816175469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44102513500967066176467917 16538442562862649816175469)
        ·
          refine ⟨6201915961073493681065801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16538442562862649816175469 6201915961073493681065801)
          ·
            refine ⟨4651436970805120260799351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6201915961073493681065801 4651436970805120260799351)
            ·
              refine ⟨6977155456207680391199027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4651436970805120260799351 6977155456207680391199027)
              ·
                refine ⟨10465733184311520586798541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6977155456207680391199027 10465733184311520586798541)
                ·
                  refine ⟨3924649944116820220049453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10465733184311520586798541 3924649944116820220049453)
                  ·
                    refine ⟨1471743729043807582518545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3924649944116820220049453 1471743729043807582518545)
                    ·
                      refine ⟨1103807796782855686888909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471743729043807582518545 1103807796782855686888909)
                      ·
                        rfl

theorem cell23_2149658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_2149658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149658 prefixEnd_2149658 := by exact prefixLift 2149658
  have htrace : WordTrace (prefixWord ++ tailWord_2149658) baseStart_2149658 baseEnd_2149658 := by
    simpa [prefixWord, tailWord_2149658, baseEnd_2149658] using wordTrace_append hprefix tailTrace_2149658
  have hstable : (prefixWord ++ tailWord_2149658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149658).length < 2 ^ (prefixWord ++ tailWord_2149658).sum := by decide
  have hdescent : baseEnd_2149658 < baseStart_2149658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149728 : List Nat := [2, 1, 1, 3, 4, 2, 2, 3, 5]
def baseStart_2149728 : Nat := 118140960795 + 2149728 * 2 ^ 59
def prefixEnd_2149728 : Nat := 4983230072969 + 3 ^ 40 * 2149728 * 2
def baseEnd_2149728 : Nat := 122649304492074490334843

theorem tailTrace_2149728 : CollatzResearch.WordTrace tailWord_2149728 prefixEnd_2149728 122649304492074490334843 := by
  unfold tailWord_2149728
  simp only [CollatzResearch.WordTrace]
  refine ⟨39203510777955037578828919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52271347703940050105105225 39203510777955037578828919)
  ·
    refine ⟨58805266166932556368243379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39203510777955037578828919 58805266166932556368243379)
    ·
      refine ⟨88207899250398834552365069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58805266166932556368243379 88207899250398834552365069)
      ·
        refine ⟨33077962218899562957136901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88207899250398834552365069 33077962218899562957136901)
        ·
          refine ⟨6202117916043668054463169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33077962218899562957136901 6202117916043668054463169)
          ·
            refine ⟨4651588437032751040847377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6202117916043668054463169 4651588437032751040847377)
            ·
              refine ⟨3488691327774563280635533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4651588437032751040847377 3488691327774563280635533)
              ·
                refine ⟨1308259247915461230238325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3488691327774563280635533 1308259247915461230238325)
                ·
                  refine ⟨122649304492074490334843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1308259247915461230238325 122649304492074490334843)
                  ·
                    rfl

theorem cell23_2149728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 5].length) (baseStart_2149728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149728 prefixEnd_2149728 := by exact prefixLift 2149728
  have htrace : WordTrace (prefixWord ++ tailWord_2149728) baseStart_2149728 baseEnd_2149728 := by
    simpa [prefixWord, tailWord_2149728, baseEnd_2149728] using wordTrace_append hprefix tailTrace_2149728
  have hstable : (prefixWord ++ tailWord_2149728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149728).length < 2 ^ (prefixWord ++ tailWord_2149728).sum := by decide
  have hdescent : baseEnd_2149728 < baseStart_2149728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149771 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 3, 4]
def baseStart_2149771 : Nat := 118140960795 + 2149771 * 2 ^ 59
def prefixEnd_2149771 : Nat := 4983230072969 + 3 ^ 40 * 2149771 * 2
def baseEnd_2149771 : Nat := 367955273365604581591963

theorem tailTrace_2149771 : CollatzResearch.WordTrace tailWord_2149771 prefixEnd_2149771 367955273365604581591963 := by
  unfold tailWord_2149771
  simp only [CollatzResearch.WordTrace]
  refine ⟨78408589894754293501473167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52272393263169529000982111 78408589894754293501473167)
  ·
    refine ⟨117612884842131440252209751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78408589894754293501473167 117612884842131440252209751)
    ·
      refine ⟨176419327263197160378314627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117612884842131440252209751 176419327263197160378314627)
      ·
        refine ⟨264628990894795740567471941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176419327263197160378314627 264628990894795740567471941)
        ·
          refine ⟨49617935792774201356400989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 264628990894795740567471941 49617935792774201356400989)
          ·
            refine ⟨18606725922290325508650371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49617935792774201356400989 18606725922290325508650371)
            ·
              refine ⟨27910088883435488262975557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18606725922290325508650371 27910088883435488262975557)
              ·
                refine ⟨5233141665644154049307917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27910088883435488262975557 5233141665644154049307917)
                ·
                  refine ⟨1962428124616557768490469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5233141665644154049307917 1962428124616557768490469)
                  ·
                    refine ⟨367955273365604581591963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962428124616557768490469 367955273365604581591963)
                    ·
                      rfl

theorem cell23_2149771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 4].length) (baseStart_2149771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149771 prefixEnd_2149771 := by exact prefixLift 2149771
  have htrace : WordTrace (prefixWord ++ tailWord_2149771) baseStart_2149771 baseEnd_2149771 := by
    simpa [prefixWord, tailWord_2149771, baseEnd_2149771] using wordTrace_append hprefix tailTrace_2149771
  have hstable : (prefixWord ++ tailWord_2149771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149771).length < 2 ^ (prefixWord ++ tailWord_2149771).sum := by decide
  have hdescent : baseEnd_2149771 < baseStart_2149771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149781 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_2149781 : Nat := 118140960795 + 2149781 * 2 ^ 59
def prefixEnd_2149781 : Nat := 4983230072969 + 3 ^ 40 * 2149781 * 2
def baseEnd_2149781 : Nat := 1103870954903358705650843

theorem tailTrace_2149781 : CollatzResearch.WordTrace tailWord_2149781 prefixEnd_2149781 1103870954903358705650843 := by
  unfold tailWord_2149781
  simp only [CollatzResearch.WordTrace]
  refine ⟨78408954624718065209337197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52272636416478710139558131 78408954624718065209337197)
  ·
    refine ⟨29403357984269274453501449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78408954624718065209337197 29403357984269274453501449)
    ·
      refine ⟨22052518488201955840126087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29403357984269274453501449 22052518488201955840126087)
      ·
        refine ⟨33078777732302933760189131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22052518488201955840126087 33078777732302933760189131)
        ·
          refine ⟨49618166598454400640283697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33078777732302933760189131 49618166598454400640283697)
          ·
            refine ⟨37213624948840800480212773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49618166598454400640283697 37213624948840800480212773)
            ·
              refine ⟨6977554677907650090039895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37213624948840800480212773 6977554677907650090039895)
              ·
                refine ⟨10466332016861475135059843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6977554677907650090039895 10466332016861475135059843)
                ·
                  refine ⟨15699498025292212702589765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10466332016861475135059843 15699498025292212702589765)
                  ·
                    refine ⟨2943655879742289881735581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15699498025292212702589765 2943655879742289881735581)
                    ·
                      refine ⟨1103870954903358705650843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2943655879742289881735581 1103870954903358705650843)
                      ·
                        rfl

theorem cell23_2149781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_2149781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149781 prefixEnd_2149781 := by exact prefixLift 2149781
  have htrace : WordTrace (prefixWord ++ tailWord_2149781) baseStart_2149781 baseEnd_2149781 := by
    simpa [prefixWord, tailWord_2149781, baseEnd_2149781] using wordTrace_append hprefix tailTrace_2149781
  have hstable : (prefixWord ++ tailWord_2149781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149781).length < 2 ^ (prefixWord ++ tailWord_2149781).sum := by decide
  have hdescent : baseEnd_2149781 < baseStart_2149781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149804 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_2149804 : Nat := 118140960795 + 2149804 * 2 ^ 59
def prefixEnd_2149804 : Nat := 4983230072969 + 3 ^ 40 * 2149804 * 2
def baseEnd_2149804 : Nat := 1103882764958412115663237

theorem tailTrace_2149804 : CollatzResearch.WordTrace tailWord_2149804 prefixEnd_2149804 1103882764958412115663237 := by
  unfold tailWord_2149804
  simp only [CollatzResearch.WordTrace]
  refine ⟨39204896751817370068712233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52273195669089826758282977 39204896751817370068712233)
  ·
    refine ⟨29403672563863027551534175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39204896751817370068712233 29403672563863027551534175)
    ·
      refine ⟨44105508845794541327301263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29403672563863027551534175 44105508845794541327301263)
      ·
        refine ⟨66158263268691811990951895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44105508845794541327301263 66158263268691811990951895)
        ·
          refine ⟨99237394903037717986427843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66158263268691811990951895 99237394903037717986427843)
          ·
            refine ⟨148856092354556576979641765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99237394903037717986427843 148856092354556576979641765)
            ·
              refine ⟨27910517316479358183682831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148856092354556576979641765 27910517316479358183682831)
              ·
                refine ⟨41865775974719037275524247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27910517316479358183682831 41865775974719037275524247)
                ·
                  refine ⟨62798663962078555913286371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41865775974719037275524247 62798663962078555913286371)
                  ·
                    refine ⟨94197995943117833869929557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62798663962078555913286371 94197995943117833869929557)
                    ·
                      refine ⟨1103882764958412115663237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 94197995943117833869929557 1103882764958412115663237)
                      ·
                        rfl

theorem cell23_2149804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_2149804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149804 prefixEnd_2149804 := by exact prefixLift 2149804
  have htrace : WordTrace (prefixWord ++ tailWord_2149804) baseStart_2149804 baseEnd_2149804 := by
    simpa [prefixWord, tailWord_2149804, baseEnd_2149804] using wordTrace_append hprefix tailTrace_2149804
  have hstable : (prefixWord ++ tailWord_2149804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149804).length < 2 ^ (prefixWord ++ tailWord_2149804).sum := by decide
  have hdescent : baseEnd_2149804 < baseStart_2149804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149805 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2149805 : Nat := 118140960795 + 2149805 * 2 ^ 59
def prefixEnd_2149805 : Nat := 4983230072969 + 3 ^ 40 * 2149805 * 2
def baseEnd_2149805 : Nat := 367961092813022203916911

theorem tailTrace_2149805 : CollatzResearch.WordTrace tailWord_2149805 prefixEnd_2149805 367961092813022203916911 := by
  unfold tailWord_2149805
  simp only [CollatzResearch.WordTrace]
  refine ⟨78409829976631117308210869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52273219984420744872140579 78409829976631117308210869)
  ·
    refine ⟨7350921560309167247644769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78409829976631117308210869 7350921560309167247644769)
    ·
      refine ⟨5513191170231875435733577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7350921560309167247644769 5513191170231875435733577)
      ·
        refine ⟨4134893377673906576800183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5513191170231875435733577 4134893377673906576800183)
        ·
          refine ⟨6202340066510859865200275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4134893377673906576800183 6202340066510859865200275)
          ·
            refine ⟨9303510099766289797800413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6202340066510859865200275 9303510099766289797800413)
            ·
              refine ⟨3488816287412358674175155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9303510099766289797800413 3488816287412358674175155)
              ·
                refine ⟨5233224431118538011262733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488816287412358674175155 5233224431118538011262733)
                ·
                  refine ⟨1962459161669451754223525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5233224431118538011262733 1962459161669451754223525)
                  ·
                    refine ⟨367961092813022203916911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962459161669451754223525 367961092813022203916911)
                    ·
                      rfl

theorem cell23_2149805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2149805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149805 prefixEnd_2149805 := by exact prefixLift 2149805
  have htrace : WordTrace (prefixWord ++ tailWord_2149805) baseStart_2149805 baseEnd_2149805 := by
    simpa [prefixWord, tailWord_2149805, baseEnd_2149805] using wordTrace_append hprefix tailTrace_2149805
  have hstable : (prefixWord ++ tailWord_2149805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149805).length < 2 ^ (prefixWord ++ tailWord_2149805).sum := by decide
  have hdescent : baseEnd_2149805 < baseStart_2149805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149831 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 3, 5]
def baseStart_2149831 : Nat := 118140960795 + 2149831 * 2 ^ 59
def prefixEnd_2149831 : Nat := 4983230072969 + 3 ^ 40 * 2149831 * 2
def baseEnd_2149831 : Nat := 367965542978694503341871

theorem tailTrace_2149831 : CollatzResearch.WordTrace tailWord_2149831 prefixEnd_2149831 367965542978694503341871 := by
  unfold tailWord_2149831
  simp only [CollatzResearch.WordTrace]
  refine ⟨78410778274536923748657347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52273852183024615832438231 78410778274536923748657347)
  ·
    refine ⟨117616167411805385622986021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78410778274536923748657347 117616167411805385622986021)
    ·
      refine ⟨22053031389713509804309879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117616167411805385622986021 22053031389713509804309879)
      ·
        refine ⟨33079547084570264706464819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22053031389713509804309879 33079547084570264706464819)
        ·
          refine ⟨49619320626855397059697229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33079547084570264706464819 49619320626855397059697229)
          ·
            refine ⟨18607245235070773897386461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49619320626855397059697229 18607245235070773897386461)
            ·
              refine ⟨6977716963151540211519923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18607245235070773897386461 6977716963151540211519923)
              ·
                refine ⟨10466575444727310317279885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6977716963151540211519923 10466575444727310317279885)
                ·
                  refine ⟨3924965791772741368979957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10466575444727310317279885 3924965791772741368979957)
                  ·
                    refine ⟨367965542978694503341871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3924965791772741368979957 367965542978694503341871)
                    ·
                      rfl

theorem cell23_2149831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_2149831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149831 prefixEnd_2149831 := by exact prefixLift 2149831
  have htrace : WordTrace (prefixWord ++ tailWord_2149831) baseStart_2149831 baseEnd_2149831 := by
    simpa [prefixWord, tailWord_2149831, baseEnd_2149831] using wordTrace_append hprefix tailTrace_2149831
  have hstable : (prefixWord ++ tailWord_2149831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149831).length < 2 ^ (prefixWord ++ tailWord_2149831).sum := by decide
  have hdescent : baseEnd_2149831 < baseStart_2149831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149838 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2]
def baseStart_2149838 : Nat := 118140960795 + 2149838 * 2 ^ 59
def prefixEnd_2149838 : Nat := 4983230072969 + 3 ^ 40 * 2149838 * 2
def baseEnd_2149838 : Nat := 1103900223300664982638081

theorem tailTrace_2149838 : CollatzResearch.WordTrace tailWord_2149838 prefixEnd_2149838 1103900223300664982638081 := by
  unfold tailWord_2149838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9801379198188945493020271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52274022390341042629441445 9801379198188945493020271)
  ·
    refine ⟨14702068797283418239530407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9801379198188945493020271 14702068797283418239530407)
    ·
      refine ⟨22053103195925127359295611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14702068797283418239530407 22053103195925127359295611)
      ·
        refine ⟨33079654793887691038943417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22053103195925127359295611 33079654793887691038943417)
        ·
          refine ⟨24809741095415768279207563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33079654793887691038943417 24809741095415768279207563)
          ·
            refine ⟨37214611643123652418811345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24809741095415768279207563 37214611643123652418811345)
            ·
              refine ⟨27910958732342739314108509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37214611643123652418811345 27910958732342739314108509)
              ·
                refine ⟨10466609524628527242790691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27910958732342739314108509 10466609524628527242790691)
                ·
                  refine ⟨15699914286942790864186037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10466609524628527242790691 15699914286942790864186037)
                  ·
                    refine ⟨1471866964400886643517441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15699914286942790864186037 1471866964400886643517441)
                    ·
                      refine ⟨1103900223300664982638081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471866964400886643517441 1103900223300664982638081)
                      ·
                        rfl

theorem cell23_2149838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_2149838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149838 prefixEnd_2149838 := by exact prefixLift 2149838
  have htrace : WordTrace (prefixWord ++ tailWord_2149838) baseStart_2149838 baseEnd_2149838 := by
    simpa [prefixWord, tailWord_2149838, baseEnd_2149838] using wordTrace_append hprefix tailTrace_2149838
  have hstable : (prefixWord ++ tailWord_2149838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149838).length < 2 ^ (prefixWord ++ tailWord_2149838).sum := by decide
  have hdescent : baseEnd_2149838 < baseStart_2149838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149871 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 5]
def baseStart_2149871 : Nat := 118140960795 + 2149871 * 2 ^ 59
def prefixEnd_2149871 : Nat := 4983230072969 + 3 ^ 40 * 2149871 * 2
def baseEnd_2149871 : Nat := 1103917168162263353525429

theorem tailTrace_2149871 : CollatzResearch.WordTrace tailWord_2149871 prefixEnd_2149871 1103917168162263353525429 := by
  unfold tailWord_2149871
  simp only [CollatzResearch.WordTrace]
  refine ⟨78412237194392010580113467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52274824796261340386742311 78412237194392010580113467)
  ·
    refine ⟨117618355791588015870170201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78412237194392010580113467 117618355791588015870170201)
    ·
      refine ⟨88213766843691011902627651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117618355791588015870170201 88213766843691011902627651)
      ·
        refine ⟨132320650265536517853941477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88213766843691011902627651 132320650265536517853941477)
        ·
          refine ⟨24810121924788097097614027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132320650265536517853941477 24810121924788097097614027)
          ·
            refine ⟨37215182887182145646421041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24810121924788097097614027 37215182887182145646421041)
            ·
              refine ⟨27911387165386609234815781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37215182887182145646421041 27911387165386609234815781)
              ·
                refine ⟨5233385093509989231527959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27911387165386609234815781 5233385093509989231527959)
                ·
                  refine ⟨7850077640264983847291939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5233385093509989231527959 7850077640264983847291939)
                  ·
                    refine ⟨11775116460397475770937909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7850077640264983847291939 11775116460397475770937909)
                    ·
                      refine ⟨1103917168162263353525429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11775116460397475770937909 1103917168162263353525429)
                      ·
                        rfl

theorem cell23_2149871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_2149871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149871 prefixEnd_2149871 := by exact prefixLift 2149871
  have htrace : WordTrace (prefixWord ++ tailWord_2149871) baseStart_2149871 baseEnd_2149871 := by
    simpa [prefixWord, tailWord_2149871, baseEnd_2149871] using wordTrace_append hprefix tailTrace_2149871
  have hstable : (prefixWord ++ tailWord_2149871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149871).length < 2 ^ (prefixWord ++ tailWord_2149871).sum := by decide
  have hdescent : baseEnd_2149871 < baseStart_2149871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149878 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_2149878 : Nat := 118140960795 + 2149878 * 2 ^ 59
def prefixEnd_2149878 : Nat := 4983230072969 + 3 ^ 40 * 2149878 * 2
def baseEnd_2149878 : Nat := 367973587508948275379299

theorem tailTrace_2149878 : CollatzResearch.WordTrace tailWord_2149878 prefixEnd_2149878 367973587508948275379299 := by
  unfold tailWord_2149878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900780781585415673476143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52274995003577767183745525 4900780781585415673476143)
  ·
    refine ⟨7351171172378123510214215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4900780781585415673476143 7351171172378123510214215)
    ·
      refine ⟨11026756758567185265321323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7351171172378123510214215 11026756758567185265321323)
      ·
        refine ⟨16540135137850777897981985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11026756758567185265321323 16540135137850777897981985)
        ·
          refine ⟨12405101353388083423486489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16540135137850777897981985 12405101353388083423486489)
          ·
            refine ⟨9303826015041062567614867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12405101353388083423486489 9303826015041062567614867)
            ·
              refine ⟨13955739022561593851422301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9303826015041062567614867 13955739022561593851422301)
              ·
                refine ⟨5233402133460597694283363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13955739022561593851422301 5233402133460597694283363)
                ·
                  refine ⟨7850103200190896541425045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5233402133460597694283363 7850103200190896541425045)
                  ·
                    refine ⟨367973587508948275379299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7850103200190896541425045 367973587508948275379299)
                    ·
                      rfl

theorem cell23_2149878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_2149878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149878 prefixEnd_2149878 := by exact prefixLift 2149878
  have htrace : WordTrace (prefixWord ++ tailWord_2149878) baseStart_2149878 baseEnd_2149878 := by
    simpa [prefixWord, tailWord_2149878, baseEnd_2149878] using wordTrace_append hprefix tailTrace_2149878
  have hstable : (prefixWord ++ tailWord_2149878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149878).length < 2 ^ (prefixWord ++ tailWord_2149878).sum := by decide
  have hdescent : baseEnd_2149878 < baseStart_2149878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149885 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 5, 2, 2]
def baseStart_2149885 : Nat := 118140960795 + 2149885 * 2 ^ 59
def prefixEnd_2149885 : Nat := 4983230072969 + 3 ^ 40 * 2149885 * 2
def baseEnd_2149885 : Nat := 1103924356891426298750365

theorem tailTrace_2149885 : CollatzResearch.WordTrace tailWord_2149885 prefixEnd_2149885 1103924356891426298750365 := by
  unfold tailWord_2149885
  simp only [CollatzResearch.WordTrace]
  refine ⟨78412747816341290971123109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52275165210894193980748739 78412747816341290971123109)
  ·
    refine ⟨14702390215563992057085583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78412747816341290971123109 14702390215563992057085583)
    ·
      refine ⟨22053585323345988085628375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14702390215563992057085583 22053585323345988085628375)
      ·
        refine ⟨33080377985018982128442563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22053585323345988085628375 33080377985018982128442563)
        ·
          refine ⟨49620566977528473192663845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33080377985018982128442563 49620566977528473192663845)
          ·
            refine ⟨9303856308286588723624471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49620566977528473192663845 9303856308286588723624471)
            ·
              refine ⟨13955784462429883085436707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9303856308286588723624471 13955784462429883085436707)
              ·
                refine ⟨20933676693644824628155061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13955784462429883085436707 20933676693644824628155061)
                ·
                  refine ⟨1962532190029202308889537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20933676693644824628155061 1962532190029202308889537)
                  ·
                    refine ⟨1471899142521901731667153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1962532190029202308889537 1471899142521901731667153)
                    ·
                      refine ⟨1103924356891426298750365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471899142521901731667153 1103924356891426298750365)
                      ·
                        rfl

theorem cell23_2149885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_2149885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149885 prefixEnd_2149885 := by exact prefixLift 2149885
  have htrace : WordTrace (prefixWord ++ tailWord_2149885) baseStart_2149885 baseEnd_2149885 := by
    simpa [prefixWord, tailWord_2149885, baseEnd_2149885] using wordTrace_append hprefix tailTrace_2149885
  have hstable : (prefixWord ++ tailWord_2149885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149885).length < 2 ^ (prefixWord ++ tailWord_2149885).sum := by decide
  have hdescent : baseEnd_2149885 < baseStart_2149885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149889 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_2149889 : Nat := 118140960795 + 2149889 * 2 ^ 59
def prefixEnd_2149889 : Nat := 4983230072969 + 3 ^ 40 * 2149889 * 2
def baseEnd_2149889 : Nat := 1103926410814044283100347

theorem tailTrace_2149889 : CollatzResearch.WordTrace tailWord_2149889 prefixEnd_2149889 1103926410814044283100347 := by
  unfold tailWord_2149889
  simp only [CollatzResearch.WordTrace]
  refine ⟨78412893708326799654268721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52275262472217866436179147 78412893708326799654268721)
  ·
    refine ⟨58809670281245099740701541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78412893708326799654268721 58809670281245099740701541)
    ·
      refine ⟨11026813177733456201381539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58809670281245099740701541 11026813177733456201381539)
      ·
        refine ⟨16540219766600184302072309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11026813177733456201381539 16540219766600184302072309)
        ·
          refine ⟨1550645603118767278319279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16540219766600184302072309 1550645603118767278319279)
          ·
            refine ⟨2325968404678150917478919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550645603118767278319279 2325968404678150917478919)
            ·
              refine ⟨3488952607017226376218379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325968404678150917478919 3488952607017226376218379)
              ·
                refine ⟨5233428910525839564327569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488952607017226376218379 5233428910525839564327569)
                ·
                  refine ⟨3925071682894379673245677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5233428910525839564327569 3925071682894379673245677)
                  ·
                    refine ⟨1471901881085392377467129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3925071682894379673245677 1471901881085392377467129)
                    ·
                      refine ⟨1103926410814044283100347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1471901881085392377467129 1103926410814044283100347)
                      ·
                        rfl

theorem cell23_2149889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_2149889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149889 prefixEnd_2149889 := by exact prefixLift 2149889
  have htrace : WordTrace (prefixWord ++ tailWord_2149889) baseStart_2149889 baseEnd_2149889 := by
    simpa [prefixWord, tailWord_2149889, baseEnd_2149889] using wordTrace_append hprefix tailTrace_2149889
  have hstable : (prefixWord ++ tailWord_2149889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149889).length < 2 ^ (prefixWord ++ tailWord_2149889).sum := by decide
  have hdescent : baseEnd_2149889 < baseStart_2149889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149898 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2149898 : Nat := 118140960795 + 2149898 * 2 ^ 59
def prefixEnd_2149898 : Nat := 4983230072969 + 3 ^ 40 * 2149898 * 2
def baseEnd_2149898 : Nat := 1103931032139934747887805

theorem tailTrace_2149898 : CollatzResearch.WordTrace tailWord_2149898 prefixEnd_2149898 1103931032139934747887805 := by
  unfold tailWord_2149898
  simp only [CollatzResearch.WordTrace]
  refine ⟨19603305491323548547836587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52275481310196129460897565 19603305491323548547836587)
  ·
    refine ⟨29404958236985322821754881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19603305491323548547836587 29404958236985322821754881)
    ·
      refine ⟨22053718677738992116316161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29404958236985322821754881 22053718677738992116316161)
      ·
        refine ⟨16540289008304244087237121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22053718677738992116316161 16540289008304244087237121)
        ·
          refine ⟨12405216756228183065427841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16540289008304244087237121 12405216756228183065427841)
          ·
            refine ⟨9303912567171137299070881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12405216756228183065427841 9303912567171137299070881)
            ·
              refine ⟨6977934425378352974303161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9303912567171137299070881 6977934425378352974303161)
              ·
                refine ⟨5233450819033764730727371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6977934425378352974303161 5233450819033764730727371)
                ·
                  refine ⟨7850176228550647096091057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5233450819033764730727371 7850176228550647096091057)
                  ·
                    refine ⟨5887632171412985322068293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7850176228550647096091057 5887632171412985322068293)
                    ·
                      refine ⟨1103931032139934747887805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5887632171412985322068293 1103931032139934747887805)
                      ·
                        rfl

theorem cell23_2149898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2149898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149898 prefixEnd_2149898 := by exact prefixLift 2149898
  have htrace : WordTrace (prefixWord ++ tailWord_2149898) baseStart_2149898 baseEnd_2149898 := by
    simpa [prefixWord, tailWord_2149898, baseEnd_2149898] using wordTrace_append hprefix tailTrace_2149898
  have hstable : (prefixWord ++ tailWord_2149898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149898).length < 2 ^ (prefixWord ++ tailWord_2149898).sum := by decide
  have hdescent : baseEnd_2149898 < baseStart_2149898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149912 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 2, 4]
def baseStart_2149912 : Nat := 118140960795 + 2149912 * 2 ^ 59
def prefixEnd_2149912 : Nat := 4983230072969 + 3 ^ 40 * 2149912 * 2
def baseEnd_2149912 : Nat := 367979406956365897704247

theorem tailTrace_2149912 : CollatzResearch.WordTrace tailWord_2149912 prefixEnd_2149912 367979406956365897704247 := by
  unfold tailWord_2149912
  simp only [CollatzResearch.WordTrace]
  refine ⟨39206866293621737291177995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52275821724828983054903993 39206866293621737291177995)
  ·
    refine ⟨58810299440432605936766993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39206866293621737291177995 58810299440432605936766993)
    ·
      refine ⟨44107724580324454452575245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58810299440432605936766993 44107724580324454452575245)
      ·
        refine ⟨16540396717621670419715717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44107724580324454452575245 16540396717621670419715717)
        ·
          refine ⟨3101324384554063203696697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16540396717621670419715717 3101324384554063203696697)
          ·
            refine ⟨2325993288415547402772523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3101324384554063203696697 2325993288415547402772523)
            ·
              refine ⟨3488989932623321104158785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325993288415547402772523 3488989932623321104158785)
              ·
                refine ⟨2616742449467490828119089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3488989932623321104158785 2616742449467490828119089)
                ·
                  refine ⟨1962556837100618121089317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2616742449467490828119089 1962556837100618121089317)
                  ·
                    refine ⟨367979406956365897704247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962556837100618121089317 367979406956365897704247)
                    ·
                      rfl

theorem cell23_2149912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_2149912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149912 prefixEnd_2149912 := by exact prefixLift 2149912
  have htrace : WordTrace (prefixWord ++ tailWord_2149912) baseStart_2149912 baseEnd_2149912 := by
    simpa [prefixWord, tailWord_2149912, baseEnd_2149912] using wordTrace_append hprefix tailTrace_2149912
  have hstable : (prefixWord ++ tailWord_2149912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149912).length < 2 ^ (prefixWord ++ tailWord_2149912).sum := by decide
  have hdescent : baseEnd_2149912 < baseStart_2149912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149942 : List Nat := [5, 1, 2, 1, 3, 2, 2, 7]
def baseStart_2149942 : Nat := 118140960795 + 2149942 * 2 ^ 59
def prefixEnd_2149942 : Nat := 4983230072969 + 3 ^ 40 * 2149942 * 2
def baseEnd_2149942 : Nat := 40887171306990095397689

theorem tailTrace_2149942 : CollatzResearch.WordTrace tailWord_2149942 prefixEnd_2149942 40887171306990095397689 := by
  unfold tailWord_2149942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900926673570924356621755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52276551184756526470632053 4900926673570924356621755)
  ·
    refine ⟨7351390010356386534932633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4900926673570924356621755 7351390010356386534932633)
    ·
      refine ⟨5513542507767289901199475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7351390010356386534932633 5513542507767289901199475)
      ·
        refine ⟨8270313761650934851799213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5513542507767289901199475 8270313761650934851799213)
        ·
          refine ⟨3101367660619100569424705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8270313761650934851799213 3101367660619100569424705)
          ·
            refine ⟨2326025745464325427068529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3101367660619100569424705 2326025745464325427068529)
            ·
              refine ⟨1744519309098244070301397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2326025745464325427068529 1744519309098244070301397)
              ·
                refine ⟨40887171306990095397689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1744519309098244070301397 40887171306990095397689)
                ·
                  rfl

theorem cell23_2149942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_2149942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149942 prefixEnd_2149942 := by exact prefixLift 2149942
  have htrace : WordTrace (prefixWord ++ tailWord_2149942) baseStart_2149942 baseEnd_2149942 := by
    simpa [prefixWord, tailWord_2149942, baseEnd_2149942] using wordTrace_append hprefix tailTrace_2149942
  have hstable : (prefixWord ++ tailWord_2149942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149942).length < 2 ^ (prefixWord ++ tailWord_2149942).sum := by decide
  have hdescent : baseEnd_2149942 < baseStart_2149942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2149971 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 4]
def baseStart_2149971 : Nat := 118140960795 + 2149971 * 2 ^ 59
def prefixEnd_2149971 : Nat := 4983230072969 + 3 ^ 40 * 2149971 * 2
def baseEnd_2149971 : Nat := 1103968516227712962274969

theorem tailTrace_2149971 : CollatzResearch.WordTrace tailWord_2149971 prefixEnd_2149971 1103968516227712962274969 := by
  unfold tailWord_2149971
  simp only [CollatzResearch.WordTrace]
  refine ⟨78415884494029727658753767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52277256329353151772502511 78415884494029727658753767)
  ·
    refine ⟨117623826741044591488130651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78415884494029727658753767 117623826741044591488130651)
    ·
      refine ⟨176435740111566887232195977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117623826741044591488130651 176435740111566887232195977)
      ·
        refine ⟨132326805083675165424146983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176435740111566887232195977 132326805083675165424146983)
        ·
          refine ⟨198490207625512748136220475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132326805083675165424146983 198490207625512748136220475)
          ·
            refine ⟨297735311438269122204330713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198490207625512748136220475 297735311438269122204330713)
            ·
              refine ⟨223301483578701841653248035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297735311438269122204330713 223301483578701841653248035)
              ·
                refine ⟨334952225368052762479872053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223301483578701841653248035 334952225368052762479872053)
                ·
                  refine ⟨31401771128254946482488005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 334952225368052762479872053 31401771128254946482488005)
                  ·
                    refine ⟨5887832086547802465466501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31401771128254946482488005 5887832086547802465466501)
                    ·
                      refine ⟨1103968516227712962274969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5887832086547802465466501 1103968516227712962274969)
                      ·
                        rfl

theorem cell23_2149971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_2149971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2149971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2149971 prefixEnd_2149971 := by exact prefixLift 2149971
  have htrace : WordTrace (prefixWord ++ tailWord_2149971) baseStart_2149971 baseEnd_2149971 := by
    simpa [prefixWord, tailWord_2149971, baseEnd_2149971] using wordTrace_append hprefix tailTrace_2149971
  have hstable : (prefixWord ++ tailWord_2149971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2149971).length < 2 ^ (prefixWord ++ tailWord_2149971).sum := by decide
  have hdescent : baseEnd_2149971 < baseStart_2149971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2149971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150001 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_2150001 : Nat := 118140960795 + 2150001 * 2 ^ 59
def prefixEnd_2150001 : Nat := 4983230072969 + 3 ^ 40 * 2150001 * 2
def baseEnd_2150001 : Nat := 1103983920647347844899831

theorem tailTrace_2150001 : CollatzResearch.WordTrace tailWord_2150001 prefixEnd_2150001 1103983920647347844899831 := by
  unfold tailWord_2150001
  simp only [CollatzResearch.WordTrace]
  refine ⟨78416978683921042782345857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52277985789280695188230571 78416978683921042782345857)
  ·
    refine ⟨58812734012940782086759393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78416978683921042782345857 58812734012940782086759393)
    ·
      refine ⟨44109550509705586565069545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58812734012940782086759393 44109550509705586565069545)
      ·
        refine ⟨33082162882279189923802159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44109550509705586565069545 33082162882279189923802159)
        ·
          refine ⟨49623244323418784885703239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33082162882279189923802159 49623244323418784885703239)
          ·
            refine ⟨74434866485128177328554859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49623244323418784885703239 74434866485128177328554859)
            ·
              refine ⟨111652299727692265992832289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74434866485128177328554859 111652299727692265992832289)
              ·
                refine ⟨83739224795769199494624217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111652299727692265992832289 83739224795769199494624217)
                ·
                  refine ⟨62804418596826899620968163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83739224795769199494624217 62804418596826899620968163)
                  ·
                    refine ⟨94206627895240349431452245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62804418596826899620968163 94206627895240349431452245)
                    ·
                      refine ⟨1103983920647347844899831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 94206627895240349431452245 1103983920647347844899831)
                      ·
                        rfl

theorem cell23_2150001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_2150001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150001 prefixEnd_2150001 := by exact prefixLift 2150001
  have htrace : WordTrace (prefixWord ++ tailWord_2150001) baseStart_2150001 baseEnd_2150001 := by
    simpa [prefixWord, tailWord_2150001, baseEnd_2150001] using wordTrace_append hprefix tailTrace_2150001
  have hstable : (prefixWord ++ tailWord_2150001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150001).length < 2 ^ (prefixWord ++ tailWord_2150001).sum := by decide
  have hdescent : baseEnd_2150001 < baseStart_2150001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150028 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_2150028 : Nat := 118140960795 + 2150028 * 2 ^ 59
def prefixEnd_2150028 : Nat := 4983230072969 + 3 ^ 40 * 2150028 * 2
def baseEnd_2150028 : Nat := 367999261541673079754069

theorem tailTrace_2150028 : CollatzResearch.WordTrace tailWord_2150028 prefixEnd_2150028 367999261541673079754069 := by
  unfold tailWord_2150028
  simp only [CollatzResearch.WordTrace]
  refine ⟨39208981727411613196789369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52278642303215484262385825 39208981727411613196789369)
  ·
    refine ⟨29406736295558709897592027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39208981727411613196789369 29406736295558709897592027)
    ·
      refine ⟨44110104443338064846388041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29406736295558709897592027 44110104443338064846388041)
      ·
        refine ⟨33082578332503548634791031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44110104443338064846388041 33082578332503548634791031)
        ·
          refine ⟨49623867498755322952186547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33082578332503548634791031 49623867498755322952186547)
          ·
            refine ⟨74435801248132984428279821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49623867498755322952186547 74435801248132984428279821)
            ·
              refine ⟨27913425468049869160604933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74435801248132984428279821 27913425468049869160604933)
              ·
                refine ⟨5233767275259350467613425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27913425468049869160604933 5233767275259350467613425)
                ·
                  refine ⟨3925325456444512850710069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5233767275259350467613425 3925325456444512850710069)
                  ·
                    refine ⟨367999261541673079754069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3925325456444512850710069 367999261541673079754069)
                    ·
                      rfl

theorem cell23_2150028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_2150028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150028 prefixEnd_2150028 := by exact prefixLift 2150028
  have htrace : WordTrace (prefixWord ++ tailWord_2150028) baseStart_2150028 baseEnd_2150028 := by
    simpa [prefixWord, tailWord_2150028, baseEnd_2150028] using wordTrace_append hprefix tailTrace_2150028
  have hstable : (prefixWord ++ tailWord_2150028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150028).length < 2 ^ (prefixWord ++ tailWord_2150028).sum := by decide
  have hdescent : baseEnd_2150028 < baseStart_2150028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150031 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_2150031 : Nat := 118140960795 + 2150031 * 2 ^ 59
def prefixEnd_2150031 : Nat := 4983230072969 + 3 ^ 40 * 2150031 * 2
def baseEnd_2150031 : Nat := 1103999325066982727524693

theorem tailTrace_2150031 : CollatzResearch.WordTrace tailWord_2150031 prefixEnd_2150031 1103999325066982727524693 := by
  unfold tailWord_2150031
  simp only [CollatzResearch.WordTrace]
  refine ⟨78418072873812357905937947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52278715249208238603958631 78418072873812357905937947)
  ·
    refine ⟨117627109310718536858906921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78418072873812357905937947 117627109310718536858906921)
    ·
      refine ⟨88220331983038902644180191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117627109310718536858906921 88220331983038902644180191)
      ·
        refine ⟨132330497974558353966270287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88220331983038902644180191 132330497974558353966270287)
        ·
          refine ⟨198495746961837530949405431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132330497974558353966270287 198495746961837530949405431)
          ·
            refine ⟨297743620442756296424108147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198495746961837530949405431 297743620442756296424108147)
            ·
              refine ⟨446615430664134444636162221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297743620442756296424108147 446615430664134444636162221)
              ·
                refine ⟨167480786499050416738560833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446615430664134444636162221 167480786499050416738560833)
                ·
                  refine ⟨125610589874287812553920625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167480786499050416738560833 125610589874287812553920625)
                  ·
                    refine ⟨94207942405715859415440469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 125610589874287812553920625 94207942405715859415440469)
                    ·
                      refine ⟨1103999325066982727524693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 94207942405715859415440469 1103999325066982727524693)
                      ·
                        rfl

theorem cell23_2150031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_2150031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150031 prefixEnd_2150031 := by exact prefixLift 2150031
  have htrace : WordTrace (prefixWord ++ tailWord_2150031) baseStart_2150031 baseEnd_2150031 := by
    simpa [prefixWord, tailWord_2150031, baseEnd_2150031] using wordTrace_append hprefix tailTrace_2150031
  have hstable : (prefixWord ++ tailWord_2150031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150031).length < 2 ^ (prefixWord ++ tailWord_2150031).sum := by decide
  have hdescent : baseEnd_2150031 < baseStart_2150031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150062 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2150062 : Nat := 118140960795 + 2150062 * 2 ^ 59
def prefixEnd_2150062 : Nat := 4983230072969 + 3 ^ 40 * 2150062 * 2
def baseEnd_2150062 : Nat := 368005080989090702079017

theorem tailTrace_2150062 : CollatzResearch.WordTrace tailWord_2150062 prefixEnd_2150062 368005080989090702079017 := by
  unfold tailWord_2150062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9802400442087506275039555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52279469024466700133544293 9802400442087506275039555)
  ·
    refine ⟨14703600663131259412559333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9802400442087506275039555 14703600663131259412559333)
    ·
      refine ⟨2756925124337111139854875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14703600663131259412559333 2756925124337111139854875)
      ·
        refine ⟨4135387686505666709782313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2756925124337111139854875 4135387686505666709782313)
        ·
          refine ⟨3101540764879250032336735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4135387686505666709782313 3101540764879250032336735)
          ·
            refine ⟨4652311147318875048505103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3101540764879250032336735 4652311147318875048505103)
            ·
              refine ⟨6978466720978312572757655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4652311147318875048505103 6978466720978312572757655)
              ·
                refine ⟨10467700081467468859136483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6978466720978312572757655 10467700081467468859136483)
                ·
                  refine ⟨15701550122201203288704725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10467700081467468859136483 15701550122201203288704725)
                  ·
                    refine ⟨368005080989090702079017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15701550122201203288704725 368005080989090702079017)
                    ·
                      rfl

theorem cell23_2150062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2150062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150062 prefixEnd_2150062 := by exact prefixLift 2150062
  have htrace : WordTrace (prefixWord ++ tailWord_2150062) baseStart_2150062 baseEnd_2150062 := by
    simpa [prefixWord, tailWord_2150062, baseEnd_2150062] using wordTrace_append hprefix tailTrace_2150062
  have hstable : (prefixWord ++ tailWord_2150062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150062).length < 2 ^ (prefixWord ++ tailWord_2150062).sum := by decide
  have hdescent : baseEnd_2150062 < baseStart_2150062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150088 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 8]
def baseStart_2150088 : Nat := 118140960795 + 2150088 * 2 ^ 59
def prefixEnd_2150088 : Nat := 4983230072969 + 3 ^ 40 * 2150088 * 2
def baseEnd_2150088 : Nat := 122669843718254333834659

theorem tailTrace_2150088 : CollatzResearch.WordTrace tailWord_2150088 prefixEnd_2150088 122669843718254333834659 := by
  unfold tailWord_2150088
  simp only [CollatzResearch.WordTrace]
  refine ⟨39210075917302928320381459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52280101223070571093841945 39210075917302928320381459)
  ·
    refine ⟨58815113875954392480572189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39210075917302928320381459 58815113875954392480572189)
    ·
      refine ⟨22055667703482897180214571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58815113875954392480572189 22055667703482897180214571)
      ·
        refine ⟨33083501555224345770321857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22055667703482897180214571 33083501555224345770321857)
        ·
          refine ⟨24812626166418259327741393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33083501555224345770321857 24812626166418259327741393)
          ·
            refine ⟨18609469624813694495806045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24812626166418259327741393 18609469624813694495806045)
            ·
              refine ⟨6978551109305135435927267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18609469624813694495806045 6978551109305135435927267)
              ·
                refine ⟨10467826663957703153890901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6978551109305135435927267 10467826663957703153890901)
                ·
                  refine ⟨122669843718254333834659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10467826663957703153890901 122669843718254333834659)
                  ·
                    rfl

theorem cell23_2150088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 8].length) (baseStart_2150088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150088 prefixEnd_2150088 := by exact prefixLift 2150088
  have htrace : WordTrace (prefixWord ++ tailWord_2150088) baseStart_2150088 baseEnd_2150088 := by
    simpa [prefixWord, tailWord_2150088, baseEnd_2150088] using wordTrace_append hprefix tailTrace_2150088
  have hstable : (prefixWord ++ tailWord_2150088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150088).length < 2 ^ (prefixWord ++ tailWord_2150088).sum := by decide
  have hdescent : baseEnd_2150088 < baseStart_2150088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150135 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 1, 5]
def baseStart_2150135 : Nat := 118140960795 + 2150135 * 2 ^ 59
def prefixEnd_2150135 : Nat := 4983230072969 + 3 ^ 40 * 2150135 * 2
def baseEnd_2150135 : Nat := 368017575685016773541405

theorem tailTrace_2150135 : CollatzResearch.WordTrace tailWord_2150135 prefixEnd_2150135 368017575685016773541405 := by
  unfold tailWord_2150135
  simp only [CollatzResearch.WordTrace]
  refine ⟨78421866065435583667723859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52281244043623722445149239 78421866065435583667723859)
  ·
    refine ⟨117632799098153375501585789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78421866065435583667723859 117632799098153375501585789)
    ·
      refine ⟨44112299661807515813094671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117632799098153375501585789 44112299661807515813094671)
      ·
        refine ⟨66168449492711273719642007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44112299661807515813094671 66168449492711273719642007)
        ·
          refine ⟨99252674239066910579463011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66168449492711273719642007 99252674239066910579463011)
          ·
            refine ⟨148879011358600365869194517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99252674239066910579463011 148879011358600365869194517)
            ·
              refine ⟨6978703657434392150118493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 148879011358600365869194517 6978703657434392150118493)
              ·
                refine ⟨2617013871537897056294435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6978703657434392150118493 2617013871537897056294435)
                ·
                  refine ⟨3925520807306845584441653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617013871537897056294435 3925520807306845584441653)
                  ·
                    refine ⟨368017575685016773541405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3925520807306845584441653 368017575685016773541405)
                    ·
                      rfl

theorem cell23_2150135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_2150135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150135 prefixEnd_2150135 := by exact prefixLift 2150135
  have htrace : WordTrace (prefixWord ++ tailWord_2150135) baseStart_2150135 baseEnd_2150135 := by
    simpa [prefixWord, tailWord_2150135, baseEnd_2150135] using wordTrace_append hprefix tailTrace_2150135
  have hstable : (prefixWord ++ tailWord_2150135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150135).length < 2 ^ (prefixWord ++ tailWord_2150135).sum := by decide
  have hdescent : baseEnd_2150135 < baseStart_2150135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150195 : List Nat := [1, 1, 1, 2, 8, 10]
def baseStart_2150195 : Nat := 118140960795 + 2150195 * 2 ^ 59
def prefixEnd_2150195 : Nat := 4983230072969 + 3 ^ 40 * 2150195 * 2
def baseEnd_2150195 : Nat := 4543553645655638213473

theorem tailTrace_2150195 : CollatzResearch.WordTrace tailWord_2150195 prefixEnd_2150195 4543553645655638213473 := by
  unfold tailWord_2150195
  simp only [CollatzResearch.WordTrace]
  refine ⟨78424054445218213914908039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52282702963478809276605359 78424054445218213914908039)
  ·
    refine ⟨117636081667827320872362059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78424054445218213914908039 117636081667827320872362059)
    ·
      refine ⟨176454122501740981308543089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117636081667827320872362059 176454122501740981308543089)
      ·
        refine ⟨132340591876305735981407317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176454122501740981308543089 132340591876305735981407317)
        ·
          refine ⟨1550866311050457843532117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 132340591876305735981407317 1550866311050457843532117)
          ·
            refine ⟨4543553645655638213473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1550866311050457843532117 4543553645655638213473)
            ·
              rfl

theorem cell23_2150195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 10].length) (baseStart_2150195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150195 prefixEnd_2150195 := by exact prefixLift 2150195
  have htrace : WordTrace (prefixWord ++ tailWord_2150195) baseStart_2150195 baseEnd_2150195 := by
    simpa [prefixWord, tailWord_2150195, baseEnd_2150195] using wordTrace_append hprefix tailTrace_2150195
  have hstable : (prefixWord ++ tailWord_2150195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150195).length < 2 ^ (prefixWord ++ tailWord_2150195).sum := by decide
  have hdescent : baseEnd_2150195 < baseStart_2150195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150222 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_2150222 : Nat := 118140960795 + 2150222 * 2 ^ 59
def prefixEnd_2150222 : Nat := 4983230072969 + 3 ^ 40 * 2150222 * 2
def baseEnd_2150222 : Nat := 1104097399871991480236315

theorem tailTrace_2150222 : CollatzResearch.WordTrace tailWord_2150222 prefixEnd_2150222 1104097399871991480236315 := by
  unfold tailWord_2150222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9803129902015049690767615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52283359477413598350760613 9803129902015049690767615)
  ·
    refine ⟨14704694853022574536151423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9803129902015049690767615 14704694853022574536151423)
    ·
      refine ⟨22057042279533861804227135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14704694853022574536151423 22057042279533861804227135)
      ·
        refine ⟨33085563419300792706340703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22057042279533861804227135 33085563419300792706340703)
        ·
          refine ⟨49628345128951189059511055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33085563419300792706340703 49628345128951189059511055)
          ·
            refine ⟨74442517693426783589266583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49628345128951189059511055 74442517693426783589266583)
            ·
              refine ⟨111663776540140175383899875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74442517693426783589266583 111663776540140175383899875)
              ·
                refine ⟨167495664810210263075849813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111663776540140175383899875 167495664810210263075849813)
                ·
                  refine ⟨1962839821994651520420115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 167495664810210263075849813 1962839821994651520420115)
                  ·
                    refine ⟨2944259732991977280630173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1962839821994651520420115 2944259732991977280630173)
                    ·
                      refine ⟨1104097399871991480236315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2944259732991977280630173 1104097399871991480236315)
                      ·
                        rfl

theorem cell23_2150222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_2150222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150222 prefixEnd_2150222 := by exact prefixLift 2150222
  have htrace : WordTrace (prefixWord ++ tailWord_2150222) baseStart_2150222 baseEnd_2150222 := by
    simpa [prefixWord, tailWord_2150222, baseEnd_2150222] using wordTrace_append hprefix tailTrace_2150222
  have hstable : (prefixWord ++ tailWord_2150222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150222).length < 2 ^ (prefixWord ++ tailWord_2150222).sum := by decide
  have hdescent : baseEnd_2150222 < baseStart_2150222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150243 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 1, 2, 3]
def baseStart_2150243 : Nat := 118140960795 + 2150243 * 2 ^ 59
def prefixEnd_2150243 : Nat := 4983230072969 + 3 ^ 40 * 2150243 * 2
def baseEnd_2150243 : Nat := 1104108182965735898073719

theorem tailTrace_2150243 : CollatzResearch.WordTrace tailWord_2150243 prefixEnd_2150243 1104108182965735898073719 := by
  unfold tailWord_2150243
  simp only [CollatzResearch.WordTrace]
  refine ⟨78425805149044318112655383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52283870099362878741770255 78425805149044318112655383)
  ·
    refine ⟨117638707723566477168983075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78425805149044318112655383 117638707723566477168983075)
    ·
      refine ⟨176458061585349715753474613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117638707723566477168983075 176458061585349715753474613)
      ·
        refine ⟨16542943273626535851888245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176458061585349715753474613 16542943273626535851888245)
        ·
          refine ⟨1550900931902487736114523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16542943273626535851888245 1550900931902487736114523)
          ·
            refine ⟨2326351397853731604171785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550900931902487736114523 2326351397853731604171785)
            ·
              refine ⟨1744763548390298703128839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2326351397853731604171785 1744763548390298703128839)
              ·
                refine ⟨2617145322585448054693259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744763548390298703128839 2617145322585448054693259)
                ·
                  refine ⟨3925717983878172082039889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617145322585448054693259 3925717983878172082039889)
                  ·
                    refine ⟨2944288487908629061529917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3925717983878172082039889 2944288487908629061529917)
                    ·
                      refine ⟨1104108182965735898073719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2944288487908629061529917 1104108182965735898073719)
                      ·
                        rfl

theorem cell23_2150243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_2150243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150243 prefixEnd_2150243 := by exact prefixLift 2150243
  have htrace : WordTrace (prefixWord ++ tailWord_2150243) baseStart_2150243 baseEnd_2150243 := by
    simpa [prefixWord, tailWord_2150243, baseEnd_2150243] using wordTrace_append hprefix tailTrace_2150243
  have hstable : (prefixWord ++ tailWord_2150243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150243).length < 2 ^ (prefixWord ++ tailWord_2150243).sum := by decide
  have hdescent : baseEnd_2150243 < baseStart_2150243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150273 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_2150273 : Nat := 118140960795 + 2150273 * 2 ^ 59
def prefixEnd_2150273 : Nat := 4983230072969 + 3 ^ 40 * 2150273 * 2
def baseEnd_2150273 : Nat := 1104123587385370780698581

theorem tailTrace_2150273 : CollatzResearch.WordTrace tailWord_2150273 prefixEnd_2150273 1104123587385370780698581 := by
  unfold tailWord_2150273
  simp only [CollatzResearch.WordTrace]
  refine ⟨78426899338935633236247473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52284599559290422157498315 78426899338935633236247473)
  ·
    refine ⟨58820174504201724927185605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78426899338935633236247473 58820174504201724927185605)
    ·
      refine ⟨11028782719537823423847301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58820174504201724927185605 11028782719537823423847301)
      ·
        refine ⟨2067896759913341891971369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11028782719537823423847301 2067896759913341891971369)
        ·
          refine ⟨1550922569935006418978527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2067896759913341891971369 1550922569935006418978527)
          ·
            refine ⟨2326383854902509628467791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550922569935006418978527 2326383854902509628467791)
            ·
              refine ⟨3489575782353764442701687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326383854902509628467791 3489575782353764442701687)
              ·
                refine ⟨5234363673530646664052531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3489575782353764442701687 5234363673530646664052531)
                ·
                  refine ⟨7851545510295969996078797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5234363673530646664052531 7851545510295969996078797)
                  ·
                    refine ⟨2944329566360988748529549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7851545510295969996078797 2944329566360988748529549)
                    ·
                      refine ⟨1104123587385370780698581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2944329566360988748529549 1104123587385370780698581)
                      ·
                        rfl

theorem cell23_2150273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_2150273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150273 prefixEnd_2150273 := by exact prefixLift 2150273
  have htrace : WordTrace (prefixWord ++ tailWord_2150273) baseStart_2150273 baseEnd_2150273 := by
    simpa [prefixWord, tailWord_2150273, baseEnd_2150273] using wordTrace_append hprefix tailTrace_2150273
  have hstable : (prefixWord ++ tailWord_2150273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150273).length < 2 ^ (prefixWord ++ tailWord_2150273).sum := by decide
  have hdescent : baseEnd_2150273 < baseStart_2150273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150319 : List Nat := [1, 1, 2, 1, 2, 2, 7, 2, 5]
def baseStart_2150319 : Nat := 118140960795 + 2150319 * 2 ^ 59
def prefixEnd_2150319 : Nat := 4983230072969 + 3 ^ 40 * 2150319 * 2
def baseEnd_2150319 : Nat := 122683023055053066747041

theorem tailTrace_2150319 : CollatzResearch.WordTrace tailWord_2150319 prefixEnd_2150319 122683023055053066747041 := by
  unfold tailWord_2150319
  simp only [CollatzResearch.WordTrace]
  refine ⟨78428577096768983092422011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52285718064512655394948007 78428577096768983092422011)
  ·
    refine ⟨117642865645153474638633017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78428577096768983092422011 117642865645153474638633017)
    ·
      refine ⟨88232149233865105978974763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117642865645153474638633017 88232149233865105978974763)
      ·
        refine ⟨132348223850797658968462145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88232149233865105978974763 132348223850797658968462145)
        ·
          refine ⟨99261167888098244226346609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132348223850797658968462145 99261167888098244226346609)
          ·
            refine ⟨74445875916073683169759957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99261167888098244226346609 74445875916073683169759957)
            ·
              refine ⟨1744825216782976949291249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74445875916073683169759957 1744825216782976949291249)
              ·
                refine ⟨1308618912587232711968437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744825216782976949291249 1308618912587232711968437)
                ·
                  refine ⟨122683023055053066747041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1308618912587232711968437 122683023055053066747041)
                  ·
                    rfl

theorem cell23_2150319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 5].length) (baseStart_2150319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150319 prefixEnd_2150319 := by exact prefixLift 2150319
  have htrace : WordTrace (prefixWord ++ tailWord_2150319) baseStart_2150319 baseEnd_2150319 := by
    simpa [prefixWord, tailWord_2150319, baseEnd_2150319] using wordTrace_append hprefix tailTrace_2150319
  have hstable : (prefixWord ++ tailWord_2150319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150319).length < 2 ^ (prefixWord ++ tailWord_2150319).sum := by decide
  have hdescent : baseEnd_2150319 < baseStart_2150319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150352 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 4]
def baseStart_2150352 : Nat := 118140960795 + 2150352 * 2 ^ 59
def prefixEnd_2150352 : Nat := 4983230072969 + 3 ^ 40 * 2150352 * 2
def baseEnd_2150352 : Nat := 1104164152357075971610717

theorem tailTrace_2150352 : CollatzResearch.WordTrace tailWord_2150352 prefixEnd_2150352 1104164152357075971610717 := by
  unfold tailWord_2150352
  simp only [CollatzResearch.WordTrace]
  refine ⟨39214890352824714864186655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52286520470432953152248873 39214890352824714864186655)
  ·
    refine ⟨58822335529237072296279983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39214890352824714864186655 58822335529237072296279983)
    ·
      refine ⟨88233503293855608444419975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58822335529237072296279983 88233503293855608444419975)
      ·
        refine ⟨132350254940783412666629963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88233503293855608444419975 132350254940783412666629963)
        ·
          refine ⟨198525382411175118999944945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132350254940783412666629963 198525382411175118999944945)
          ·
            refine ⟨148894036808381339249958709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198525382411175118999944945 148894036808381339249958709)
            ·
              refine ⟨13958815950785750554683629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148894036808381339249958709 13958815950785750554683629)
              ·
                refine ⟨5234555981544656458006361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13958815950785750554683629 5234555981544656458006361)
                ·
                  refine ⟨3925916986158492343504771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5234555981544656458006361 3925916986158492343504771)
                  ·
                    refine ⟨5888875479237738515257157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3925916986158492343504771 5888875479237738515257157)
                    ·
                      refine ⟨1104164152357075971610717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5888875479237738515257157 1104164152357075971610717)
                      ·
                        rfl

theorem cell23_2150352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_2150352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150352 prefixEnd_2150352 := by exact prefixLift 2150352
  have htrace : WordTrace (prefixWord ++ tailWord_2150352) baseStart_2150352 baseEnd_2150352 := by
    simpa [prefixWord, tailWord_2150352, baseEnd_2150352] using wordTrace_append hprefix tailTrace_2150352
  have hstable : (prefixWord ++ tailWord_2150352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150352).length < 2 ^ (prefixWord ++ tailWord_2150352).sum := by decide
  have hdescent : baseEnd_2150352 < baseStart_2150352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150370 : List Nat := [3, 3, 3, 1, 2, 2, 2, 2, 5]
def baseStart_2150370 : Nat := 118140960795 + 2150370 * 2 ^ 59
def prefixEnd_2150370 : Nat := 4983230072969 + 3 ^ 40 * 2150370 * 2
def baseEnd_2150370 : Nat := 122685932778761877909515

theorem tailTrace_2150370 : CollatzResearch.WordTrace tailWord_2150370 prefixEnd_2150370 122685932778761877909515 := by
  unfold tailWord_2150370
  simp only [CollatzResearch.WordTrace]
  refine ⟨19607609304896054700632141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52286958146389479201685709 19607609304896054700632141)
  ·
    refine ⟨7352853489336020512737053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19607609304896054700632141 7352853489336020512737053)
    ·
      refine ⟨2757320058501007692276395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7352853489336020512737053 2757320058501007692276395)
      ·
        refine ⟨4135980087751511538414593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2757320058501007692276395 4135980087751511538414593)
        ·
          refine ⟨3101985065813633653810945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4135980087751511538414593 3101985065813633653810945)
          ·
            refine ⟨2326488799360225240358209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3101985065813633653810945 2326488799360225240358209)
            ·
              refine ⟨1744866599520168930268657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2326488799360225240358209 1744866599520168930268657)
              ·
                refine ⟨1308649949640126697701493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744866599520168930268657 1308649949640126697701493)
                ·
                  refine ⟨122685932778761877909515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1308649949640126697701493 122685932778761877909515)
                  ·
                    rfl

theorem cell23_2150370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_2150370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150370 prefixEnd_2150370 := by exact prefixLift 2150370
  have htrace : WordTrace (prefixWord ++ tailWord_2150370) baseStart_2150370 baseEnd_2150370 := by
    simpa [prefixWord, tailWord_2150370, baseEnd_2150370] using wordTrace_append hprefix tailTrace_2150370
  have hstable : (prefixWord ++ tailWord_2150370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150370).length < 2 ^ (prefixWord ++ tailWord_2150370).sum := by decide
  have hdescent : baseEnd_2150370 < baseStart_2150370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150392 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 6]
def baseStart_2150392 : Nat := 118140960795 + 2150392 * 2 ^ 59
def prefixEnd_2150392 : Nat := 4983230072969 + 3 ^ 40 * 2150392 * 2
def baseEnd_2150392 : Nat := 122687187953695090567837

theorem tailTrace_2150392 : CollatzResearch.WordTrace tailWord_2150392 prefixEnd_2150392 122687187953695090567837 := by
  unfold tailWord_2150392
  simp only [CollatzResearch.WordTrace]
  refine ⟨39215619812752258279914715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52287493083669677706552953 39215619812752258279914715)
  ·
    refine ⟨58823429719128387419872073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39215619812752258279914715 58823429719128387419872073)
    ·
      refine ⟨44117572289346290564904055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58823429719128387419872073 44117572289346290564904055)
      ·
        refine ⟨66176358434019435847356083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44117572289346290564904055 66176358434019435847356083)
        ·
          refine ⟨99264537651029153771034125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66176358434019435847356083 99264537651029153771034125)
          ·
            refine ⟨37224201619135932664137797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99264537651029153771034125 37224201619135932664137797)
            ·
              refine ⟨6979537803587987374525837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37224201619135932664137797 6979537803587987374525837)
              ·
                refine ⟨2617326676345495265447189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6979537803587987374525837 2617326676345495265447189)
                ·
                  refine ⟨122687187953695090567837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2617326676345495265447189 122687187953695090567837)
                  ·
                    rfl

theorem cell23_2150392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 6].length) (baseStart_2150392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150392 prefixEnd_2150392 := by exact prefixLift 2150392
  have htrace : WordTrace (prefixWord ++ tailWord_2150392) baseStart_2150392 baseEnd_2150392 := by
    simpa [prefixWord, tailWord_2150392, baseEnd_2150392] using wordTrace_append hprefix tailTrace_2150392
  have hstable : (prefixWord ++ tailWord_2150392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150392).length < 2 ^ (prefixWord ++ tailWord_2150392).sum := by decide
  have hdescent : baseEnd_2150392 < baseStart_2150392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150446 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_2150446 : Nat := 118140960795 + 2150446 * 2 ^ 59
def prefixEnd_2150446 : Nat := 4983230072969 + 3 ^ 40 * 2150446 * 2
def baseEnd_2150446 : Nat := 1104212419538598603835285

theorem tailTrace_2150446 : CollatzResearch.WordTrace tailWord_2150446 prefixEnd_2150446 1104212419538598603835285 := by
  unfold tailWord_2150446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9804151145913610472786899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52288806111539255854863461 9804151145913610472786899)
  ·
    refine ⟨14706226718870415709180349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9804151145913610472786899 14706226718870415709180349)
    ·
      refine ⟨5514835019576405890942631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14706226718870415709180349 5514835019576405890942631)
      ·
        refine ⟨8272252529364608836413947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5514835019576405890942631 8272252529364608836413947)
        ·
          refine ⟨12408378794046913254620921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8272252529364608836413947 12408378794046913254620921)
          ·
            refine ⟨9306284095535184940965691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12408378794046913254620921 9306284095535184940965691)
            ·
              refine ⟨13959426143302777411448537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9306284095535184940965691 13959426143302777411448537)
              ·
                refine ⟨10469569607477083058586403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13959426143302777411448537 10469569607477083058586403)
                ·
                  refine ⟨15704354411215624587879605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10469569607477083058586403 15704354411215624587879605)
                  ·
                    refine ⟨1472283226051464805113713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15704354411215624587879605 1472283226051464805113713)
                    ·
                      refine ⟨1104212419538598603835285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1472283226051464805113713 1104212419538598603835285)
                      ·
                        rfl

theorem cell23_2150446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_2150446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150446 prefixEnd_2150446 := by exact prefixLift 2150446
  have htrace : WordTrace (prefixWord ++ tailWord_2150446) baseStart_2150446 baseEnd_2150446 := by
    simpa [prefixWord, tailWord_2150446, baseEnd_2150446] using wordTrace_append hprefix tailTrace_2150446
  have hstable : (prefixWord ++ tailWord_2150446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150446).length < 2 ^ (prefixWord ++ tailWord_2150446).sum := by decide
  have hdescent : baseEnd_2150446 < baseStart_2150446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150456 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 1, 5]
def baseStart_2150456 : Nat := 118140960795 + 2150456 * 2 ^ 59
def prefixEnd_2150456 : Nat := 4983230072969 + 3 ^ 40 * 2150456 * 2
def baseEnd_2150456 : Nat := 368072518115047854903413

theorem tailTrace_2150456 : CollatzResearch.WordTrace tailWord_2150456 prefixEnd_2150456 368072518115047854903413 := by
  unfold tailWord_2150456
  simp only [CollatzResearch.WordTrace]
  refine ⟨39216786948636327745079611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52289049264848436993439481 39216786948636327745079611)
  ·
    refine ⟨58825180422954491617619417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39216786948636327745079611 58825180422954491617619417)
    ·
      refine ⟨44118885317215868713214563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58825180422954491617619417 44118885317215868713214563)
      ·
        refine ⟨66178327975823803069821845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44118885317215868713214563 66178327975823803069821845)
        ·
          refine ⟨3102109123866740768897899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66178327975823803069821845 3102109123866740768897899)
          ·
            refine ⟨4653163685800111153346849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102109123866740768897899 4653163685800111153346849)
            ·
              refine ⟨3489872764350083365010137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4653163685800111153346849 3489872764350083365010137)
              ·
                refine ⟨2617404573262562523757603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3489872764350083365010137 2617404573262562523757603)
                ·
                  refine ⟨3926106859893843785636405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617404573262562523757603 3926106859893843785636405)
                  ·
                    refine ⟨368072518115047854903413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3926106859893843785636405 368072518115047854903413)
                    ·
                      rfl

theorem cell23_2150456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_2150456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150456 prefixEnd_2150456 := by exact prefixLift 2150456
  have htrace : WordTrace (prefixWord ++ tailWord_2150456) baseStart_2150456 baseEnd_2150456 := by
    simpa [prefixWord, tailWord_2150456, baseEnd_2150456] using wordTrace_append hprefix tailTrace_2150456
  have hstable : (prefixWord ++ tailWord_2150456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150456).length < 2 ^ (prefixWord ++ tailWord_2150456).sum := by decide
  have hdescent : baseEnd_2150456 < baseStart_2150456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150476 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 5, 2, 2]
def baseStart_2150476 : Nat := 118140960795 + 2150476 * 2 ^ 59
def prefixEnd_2150476 : Nat := 4983230072969 + 3 ^ 40 * 2150476 * 2
def baseEnd_2150476 : Nat := 1104227823958233486460147

theorem tailTrace_2150476 : CollatzResearch.WordTrace tailWord_2150476 prefixEnd_2150476 1104227823958233486460147 := by
  unfold tailWord_2150476
  simp only [CollatzResearch.WordTrace]
  refine ⟨39217151678600099452943641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52289535571466799270591521 39217151678600099452943641)
  ·
    refine ⟨29412863758950074589707731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39217151678600099452943641 29412863758950074589707731)
    ·
      refine ⟨44119295638425111884561597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29412863758950074589707731 44119295638425111884561597)
      ·
        refine ⟨16544735864409416956710599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44119295638425111884561597 16544735864409416956710599)
        ·
          refine ⟨24817103796614125435065899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16544735864409416956710599 24817103796614125435065899)
          ·
            refine ⟨37225655694921188152598849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24817103796614125435065899 37225655694921188152598849)
            ·
              refine ⟨27919241771190891114449137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37225655694921188152598849 27919241771190891114449137)
              ·
                refine ⟨20939431328393168335836853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27919241771190891114449137 20939431328393168335836853)
                ·
                  refine ⟨1963071687036859531484705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20939431328393168335836853 1963071687036859531484705)
                  ·
                    refine ⟨1472303765277644648613529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1963071687036859531484705 1472303765277644648613529)
                    ·
                      refine ⟨1104227823958233486460147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1472303765277644648613529 1104227823958233486460147)
                      ·
                        rfl

theorem cell23_2150476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_2150476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150476 prefixEnd_2150476 := by exact prefixLift 2150476
  have htrace : WordTrace (prefixWord ++ tailWord_2150476) baseStart_2150476 baseEnd_2150476 := by
    simpa [prefixWord, tailWord_2150476, baseEnd_2150476] using wordTrace_append hprefix tailTrace_2150476
  have hstable : (prefixWord ++ tailWord_2150476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150476).length < 2 ^ (prefixWord ++ tailWord_2150476).sum := by decide
  have hdescent : baseEnd_2150476 < baseStart_2150476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150559 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 1, 8]
def baseStart_2150559 : Nat := 118140960795 + 2150559 * 2 ^ 59
def prefixEnd_2150559 : Nat := 4983230072969 + 3 ^ 40 * 2150559 * 2
def baseEnd_2150559 : Nat := 368090147617518887240755

theorem tailTrace_2150559 : CollatzResearch.WordTrace tailWord_2150559 prefixEnd_2150559 368090147617518887240755 := by
  unfold tailWord_2150559
  simp only [CollatzResearch.WordTrace]
  refine ⟨78437330615899504081158731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52291553743933002720772487 78437330615899504081158731)
  ·
    refine ⟨117655995923849256121738097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78437330615899504081158731 117655995923849256121738097)
    ·
      refine ⟨88241996942886942091303573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117655995923849256121738097 88241996942886942091303573)
      ·
        refine ⟨4136343606697825410529855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88241996942886942091303573 4136343606697825410529855)
        ·
          refine ⟨6204515410046738115794783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4136343606697825410529855 6204515410046738115794783)
          ·
            refine ⟨9306773115070107173692175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6204515410046738115794783 9306773115070107173692175)
            ·
              refine ⟨13960159672605160760538263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9306773115070107173692175 13960159672605160760538263)
              ·
                refine ⟨20940239508907741140807395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13960159672605160760538263 20940239508907741140807395)
                ·
                  refine ⟨31410359263361611711211093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20940239508907741140807395 31410359263361611711211093)
                  ·
                    refine ⟨368090147617518887240755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31410359263361611711211093 368090147617518887240755)
                    ·
                      rfl

theorem cell23_2150559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_2150559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150559 prefixEnd_2150559 := by exact prefixLift 2150559
  have htrace : WordTrace (prefixWord ++ tailWord_2150559) baseStart_2150559 baseEnd_2150559 := by
    simpa [prefixWord, tailWord_2150559, baseEnd_2150559] using wordTrace_append hprefix tailTrace_2150559
  have hstable : (prefixWord ++ tailWord_2150559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150559).length < 2 ^ (prefixWord ++ tailWord_2150559).sum := by decide
  have hdescent : baseEnd_2150559 < baseStart_2150559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150594 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2150594 : Nat := 118140960795 + 2150594 * 2 ^ 59
def prefixEnd_2150594 : Nat := 4983230072969 + 3 ^ 40 * 2150594 * 2
def baseEnd_2150594 : Nat := 1104288414675464024784605

theorem tailTrace_2150594 : CollatzResearch.WordTrace tailWord_2150594 prefixEnd_2150594 1104288414675464024784605 := by
  unfold tailWord_2150594
  simp only [CollatzResearch.WordTrace]
  refine ⟨19609651792693176264670709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52292404780515136705788557 19609651792693176264670709)
  ·
    refine ⟨1838404855564985274812879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19609651792693176264670709 1838404855564985274812879)
    ·
      refine ⟨2757607283347477912219319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1838404855564985274812879 2757607283347477912219319)
      ·
        refine ⟨4136410925021216868328979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2757607283347477912219319 4136410925021216868328979)
        ·
          refine ⟨6204616387531825302493469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4136410925021216868328979 6204616387531825302493469)
          ·
            refine ⟨2326731145324434488435051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6204616387531825302493469 2326731145324434488435051)
            ·
              refine ⟨3490096717986651732652577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326731145324434488435051 3490096717986651732652577)
              ·
                refine ⟨2617572538489988799489433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3490096717986651732652577 2617572538489988799489433)
                ·
                  refine ⟨1963179403867491599617075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2617572538489988799489433 1963179403867491599617075)
                  ·
                    refine ⟨2944769105801237399425613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1963179403867491599617075 2944769105801237399425613)
                    ·
                      refine ⟨1104288414675464024784605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2944769105801237399425613 1104288414675464024784605)
                      ·
                        rfl

theorem cell23_2150594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2150594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150594 prefixEnd_2150594 := by exact prefixLift 2150594
  have htrace : WordTrace (prefixWord ++ tailWord_2150594) baseStart_2150594 baseEnd_2150594 := by
    simpa [prefixWord, tailWord_2150594, baseEnd_2150594] using wordTrace_append hprefix tailTrace_2150594
  have hstable : (prefixWord ++ tailWord_2150594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150594).length < 2 ^ (prefixWord ++ tailWord_2150594).sum := by decide
  have hdescent : baseEnd_2150594 < baseStart_2150594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150596 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2150596 : Nat := 118140960795 + 2150596 * 2 ^ 59
def prefixEnd_2150596 : Nat := 4983230072969 + 3 ^ 40 * 2150596 * 2
def baseEnd_2150596 : Nat := 1104289441636773016959595

theorem tailTrace_2150596 : CollatzResearch.WordTrace tailWord_2150596 prefixEnd_2150596 1104289441636773016959595 := by
  unfold tailWord_2150596
  simp only [CollatzResearch.WordTrace]
  refine ⟨39219340058382729700127821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52292453411176972933503761 39219340058382729700127821)
  ·
    refine ⟨14707252521893523637547933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39219340058382729700127821 14707252521893523637547933)
    ·
      refine ⟨5515219695710071364080475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14707252521893523637547933 5515219695710071364080475)
      ·
        refine ⟨8272829543565107046120713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5515219695710071364080475 8272829543565107046120713)
        ·
          refine ⟨6204622157673830284590535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8272829543565107046120713 6204622157673830284590535)
          ·
            refine ⟨9306933236510745426885803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6204622157673830284590535 9306933236510745426885803)
            ·
              refine ⟨13960399854766118140328705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9306933236510745426885803 13960399854766118140328705)
              ·
                refine ⟨10470299891074588605246529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13960399854766118140328705 10470299891074588605246529)
                ·
                  refine ⟨7852724918305941453934897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10470299891074588605246529 7852724918305941453934897)
                  ·
                    refine ⟨5889543688729456090451173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7852724918305941453934897 5889543688729456090451173)
                    ·
                      refine ⟨1104289441636773016959595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5889543688729456090451173 1104289441636773016959595)
                      ·
                        rfl

theorem cell23_2150596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2150596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150596 prefixEnd_2150596 := by exact prefixLift 2150596
  have htrace : WordTrace (prefixWord ++ tailWord_2150596) baseStart_2150596 baseEnd_2150596 := by
    simpa [prefixWord, tailWord_2150596, baseEnd_2150596] using wordTrace_append hprefix tailTrace_2150596
  have hstable : (prefixWord ++ tailWord_2150596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150596).length < 2 ^ (prefixWord ++ tailWord_2150596).sum := by decide
  have hdescent : baseEnd_2150596 < baseStart_2150596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150606 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_2150606 : Nat := 118140960795 + 2150606 * 2 ^ 59
def prefixEnd_2150606 : Nat := 4983230072969 + 3 ^ 40 * 2150606 * 2
def baseEnd_2150606 : Nat := 122699397382590886426061

theorem tailTrace_2150606 : CollatzResearch.WordTrace tailWord_2150606 prefixEnd_2150606 122699397382590886426061 := by
  unfold tailWord_2150606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9804880605841153888514959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52292696564486154072079781 9804880605841153888514959)
  ·
    refine ⟨14707320908761730832772439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9804880605841153888514959 14707320908761730832772439)
    ·
      refine ⟨22060981363142596249158659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14707320908761730832772439 22060981363142596249158659)
      ·
        refine ⟨33091472044713894373737989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22060981363142596249158659 33091472044713894373737989)
        ·
          refine ⟨6204651008383855195075873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33091472044713894373737989 6204651008383855195075873)
          ·
            refine ⟨4653488256287891396306905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6204651008383855195075873 4653488256287891396306905)
            ·
              refine ⟨3490116192215918547230179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4653488256287891396306905 3490116192215918547230179)
              ·
                refine ⟨5235174288323877820845269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490116192215918547230179 5235174288323877820845269)
                ·
                  refine ⟨122699397382590886426061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5235174288323877820845269 122699397382590886426061)
                  ·
                    rfl

theorem cell23_2150606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_2150606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150606 prefixEnd_2150606 := by exact prefixLift 2150606
  have htrace : WordTrace (prefixWord ++ tailWord_2150606) baseStart_2150606 baseEnd_2150606 := by
    simpa [prefixWord, tailWord_2150606, baseEnd_2150606] using wordTrace_append hprefix tailTrace_2150606
  have hstable : (prefixWord ++ tailWord_2150606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150606).length < 2 ^ (prefixWord ++ tailWord_2150606).sum := by decide
  have hdescent : baseEnd_2150606 < baseStart_2150606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150616 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 2, 3, 3]
def baseStart_2150616 : Nat := 118140960795 + 2150616 * 2 ^ 59
def prefixEnd_2150616 : Nat := 4983230072969 + 3 ^ 40 * 2150616 * 2
def baseEnd_2150616 : Nat := 1104299711249862938709503

theorem tailTrace_2150616 : CollatzResearch.WordTrace tailWord_2150616 prefixEnd_2150616 1104299711249862938709503 := by
  unfold tailWord_2150616
  simp only [CollatzResearch.WordTrace]
  refine ⟨39219704788346501407991851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52292939717795335210655801 39219704788346501407991851)
  ·
    refine ⟨58829557182519752111987777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39219704788346501407991851 58829557182519752111987777)
    ·
      refine ⟨44122167886889814083990833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58829557182519752111987777 44122167886889814083990833)
      ·
        refine ⟨33091625915167360562993125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44122167886889814083990833 33091625915167360562993125)
        ·
          refine ⟨6204679859093880105561211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33091625915167360562993125 6204679859093880105561211)
          ·
            refine ⟨9307019788640820158341817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6204679859093880105561211 9307019788640820158341817)
            ·
              refine ⟨6980264841480615118756363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9307019788640820158341817 6980264841480615118756363)
              ·
                refine ⟨10470397262220922678134545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6980264841480615118756363 10470397262220922678134545)
                ·
                  refine ⟨7852797946665692008600909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10470397262220922678134545 7852797946665692008600909)
                  ·
                    refine ⟨2944799229999634503225341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7852797946665692008600909 2944799229999634503225341)
                    ·
                      refine ⟨1104299711249862938709503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2944799229999634503225341 1104299711249862938709503)
                      ·
                        rfl

theorem cell23_2150616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_2150616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150616 prefixEnd_2150616 := by exact prefixLift 2150616
  have htrace : WordTrace (prefixWord ++ tailWord_2150616) baseStart_2150616 baseEnd_2150616 := by
    simpa [prefixWord, tailWord_2150616, baseEnd_2150616] using wordTrace_append hprefix tailTrace_2150616
  have hstable : (prefixWord ++ tailWord_2150616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150616).length < 2 ^ (prefixWord ++ tailWord_2150616).sum := by decide
  have hdescent : baseEnd_2150616 < baseStart_2150616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150656 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 4, 4, 2]
def baseStart_2150656 : Nat := 118140960795 + 2150656 * 2 ^ 59
def prefixEnd_2150656 : Nat := 4983230072969 + 3 ^ 40 * 2150656 * 2
def baseEnd_2150656 : Nat := 1104320250476042782209319

theorem tailTrace_2150656 : CollatzResearch.WordTrace tailWord_2150656 prefixEnd_2150656 1104320250476042782209319 := by
  unfold tailWord_2150656
  simp only [CollatzResearch.WordTrace]
  refine ⟨39220434248274044823719911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52293912331032059764959881 39220434248274044823719911)
  ·
    refine ⟨58830651372411067235579867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39220434248274044823719911 58830651372411067235579867)
    ·
      refine ⟨88245977058616600853369801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58830651372411067235579867 88245977058616600853369801)
      ·
        refine ⟨66184482793962450640027351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88245977058616600853369801 66184482793962450640027351)
        ·
          refine ⟨99276724190943675960041027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66184482793962450640027351 99276724190943675960041027)
          ·
            refine ⟨148915086286415513940061541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99276724190943675960041027 148915086286415513940061541)
            ·
              refine ⟨27921578678702908863761539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148915086286415513940061541 27921578678702908863761539)
              ·
                refine ⟨41882368018054363295642309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27921578678702908863761539 41882368018054363295642309)
                ·
                  refine ⟨7852944003385193117932933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41882368018054363295642309 7852944003385193117932933)
                  ·
                    refine ⟨1472427000634723709612425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7852944003385193117932933 1472427000634723709612425)
                    ·
                      refine ⟨1104320250476042782209319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1472427000634723709612425 1104320250476042782209319)
                      ·
                        rfl

theorem cell23_2150656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_2150656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150656 prefixEnd_2150656 := by exact prefixLift 2150656
  have htrace : WordTrace (prefixWord ++ tailWord_2150656) baseStart_2150656 baseEnd_2150656 := by
    simpa [prefixWord, tailWord_2150656, baseEnd_2150656] using wordTrace_append hprefix tailTrace_2150656
  have hstable : (prefixWord ++ tailWord_2150656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150656).length < 2 ^ (prefixWord ++ tailWord_2150656).sum := by decide
  have hdescent : baseEnd_2150656 < baseStart_2150656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150663 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2150663 : Nat := 118140960795 + 2150663 * 2 ^ 59
def prefixEnd_2150663 : Nat := 4983230072969 + 3 ^ 40 * 2150663 * 2
def baseEnd_2150663 : Nat := 1104323844840624254821787

theorem tailTrace_2150663 : CollatzResearch.WordTrace tailWord_2150663 prefixEnd_2150663 1104323844840624254821787 := by
  unfold tailWord_2150663
  simp only [CollatzResearch.WordTrace]
  refine ⟨78441123807522729842944643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52294082538348486561963095 78441123807522729842944643)
  ·
    refine ⟨117661685711284094764416965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78441123807522729842944643 117661685711284094764416965)
    ·
      refine ⟨22061566070865767768328181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117661685711284094764416965 22061566070865767768328181)
      ·
        refine ⟨2068271819143665728280767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22061566070865767768328181 2068271819143665728280767)
        ·
          refine ⟨3102407728715498592421151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068271819143665728280767 3102407728715498592421151)
          ·
            refine ⟨4653611593073247888631727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102407728715498592421151 4653611593073247888631727)
            ·
              refine ⟨6980417389609871832947591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4653611593073247888631727 6980417389609871832947591)
              ·
                refine ⟨10470626084414807749421387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6980417389609871832947591 10470626084414807749421387)
                ·
                  refine ⟨15705939126622211624132081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10470626084414807749421387 15705939126622211624132081)
                  ·
                    refine ⟨11779454344966658718099061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15705939126622211624132081 11779454344966658718099061)
                    ·
                      refine ⟨1104323844840624254821787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11779454344966658718099061 1104323844840624254821787)
                      ·
                        rfl

theorem cell23_2150663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2150663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150663 prefixEnd_2150663 := by exact prefixLift 2150663
  have htrace : WordTrace (prefixWord ++ tailWord_2150663) baseStart_2150663 baseEnd_2150663 := by
    simpa [prefixWord, tailWord_2150663, baseEnd_2150663] using wordTrace_append hprefix tailTrace_2150663
  have hstable : (prefixWord ++ tailWord_2150663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150663).length < 2 ^ (prefixWord ++ tailWord_2150663).sum := by decide
  have hdescent : baseEnd_2150663 < baseStart_2150663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150713 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 6]
def baseStart_2150713 : Nat := 118140960795 + 2150713 * 2 ^ 59
def prefixEnd_2150713 : Nat := 4983230072969 + 3 ^ 40 * 2150713 * 2
def baseEnd_2150713 : Nat := 122705502097038784355173

theorem tailTrace_2150713 : CollatzResearch.WordTrace tailWord_2150713 prefixEnd_2150713 122705502097038784355173 := by
  unfold tailWord_2150713
  simp only [CollatzResearch.WordTrace]
  refine ⟨78442947457341588382264793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52295298304894392254843195 78442947457341588382264793)
  ·
    refine ⟨58832210593006191286698595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78442947457341588382264793 58832210593006191286698595)
    ·
      refine ⟨88248315889509286930047893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58832210593006191286698595 88248315889509286930047893)
      ·
        refine ⟨4136639807320747824845995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88248315889509286930047893 4136639807320747824845995)
        ·
          refine ⟨6204959710981121737268993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4136639807320747824845995 6204959710981121737268993)
          ·
            refine ⟨4653719783235841302951745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6204959710981121737268993 4653719783235841302951745)
            ·
              refine ⟨3490289837426880977213809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4653719783235841302951745 3490289837426880977213809)
              ·
                refine ⟨2617717378070160732910357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3490289837426880977213809 2617717378070160732910357)
                ·
                  refine ⟨122705502097038784355173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2617717378070160732910357 122705502097038784355173)
                  ·
                    rfl

theorem cell23_2150713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 6].length) (baseStart_2150713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150713 prefixEnd_2150713 := by exact prefixLift 2150713
  have htrace : WordTrace (prefixWord ++ tailWord_2150713) baseStart_2150713 baseEnd_2150713 := by
    simpa [prefixWord, tailWord_2150713, baseEnd_2150713] using wordTrace_append hprefix tailTrace_2150713
  have hstable : (prefixWord ++ tailWord_2150713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150713).length < 2 ^ (prefixWord ++ tailWord_2150713).sum := by decide
  have hdescent : baseEnd_2150713 < baseStart_2150713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150740 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_2150740 : Nat := 118140960795 + 2150740 * 2 ^ 59
def prefixEnd_2150740 : Nat := 4983230072969 + 3 ^ 40 * 2150740 * 2
def baseEnd_2150740 : Nat := 1104363382851020453558933

theorem tailTrace_2150740 : CollatzResearch.WordTrace tailWord_2150740 prefixEnd_2150740 1104363382851020453558933 := by
  unfold tailWord_2150740
  simp only [CollatzResearch.WordTrace]
  refine ⟨39221966114121885996748837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52295954818829181328998449 39221966114121885996748837)
  ·
    refine ⟨7354118646397853624390407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39221966114121885996748837 7354118646397853624390407)
    ·
      refine ⟨11031177969596780436585611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7354118646397853624390407 11031177969596780436585611)
      ·
        refine ⟨16546766954395170654878417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11031177969596780436585611 16546766954395170654878417)
        ·
          refine ⟨12410075215796377991158813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16546766954395170654878417 12410075215796377991158813)
          ·
            refine ⟨4653778205923641746684555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12410075215796377991158813 4653778205923641746684555)
            ·
              refine ⟨6980667308885462620026833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4653778205923641746684555 6980667308885462620026833)
              ·
                refine ⟨5235500481664096965020125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6980667308885462620026833 5235500481664096965020125)
                ·
                  refine ⟨1963312680624036361882547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5235500481664096965020125 1963312680624036361882547)
                  ·
                    refine ⟨2944969020936054542823821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1963312680624036361882547 2944969020936054542823821)
                    ·
                      refine ⟨1104363382851020453558933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2944969020936054542823821 1104363382851020453558933)
                      ·
                        rfl

theorem cell23_2150740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_2150740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150740 prefixEnd_2150740 := by exact prefixLift 2150740
  have htrace : WordTrace (prefixWord ++ tailWord_2150740) baseStart_2150740 baseEnd_2150740 := by
    simpa [prefixWord, tailWord_2150740, baseEnd_2150740] using wordTrace_append hprefix tailTrace_2150740
  have hstable : (prefixWord ++ tailWord_2150740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150740).length < 2 ^ (prefixWord ++ tailWord_2150740).sum := by decide
  have hdescent : baseEnd_2150740 < baseStart_2150740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150756 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_2150756 : Nat := 118140960795 + 2150756 * 2 ^ 59
def prefixEnd_2150756 : Nat := 4983230072969 + 3 ^ 40 * 2150756 * 2
def baseEnd_2150756 : Nat := 368123866180497463652953

theorem tailTrace_2150756 : CollatzResearch.WordTrace tailWord_2150756 prefixEnd_2150756 368123866180497463652953 := by
  unfold tailWord_2150756
  simp only [CollatzResearch.WordTrace]
  refine ⟨39222257898092903363040061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52296343864123871150720081 39222257898092903363040061)
  ·
    refine ⟨14708346711784838761140023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39222257898092903363040061 14708346711784838761140023)
    ·
      refine ⟨22062520067677258141710035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14708346711784838761140023 22062520067677258141710035)
      ·
        refine ⟨33093780101515887212565053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22062520067677258141710035 33093780101515887212565053)
        ·
          refine ⟨12410167538068457704711895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33093780101515887212565053 12410167538068457704711895)
          ·
            refine ⟨18615251307102686557067843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12410167538068457704711895 18615251307102686557067843)
            ·
              refine ⟨27922876960654029835601765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18615251307102686557067843 27922876960654029835601765)
              ·
                refine ⟨5235539430122630594175331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27922876960654029835601765 5235539430122630594175331)
                ·
                  refine ⟨7853309145183945891262997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5235539430122630594175331 7853309145183945891262997)
                  ·
                    refine ⟨368123866180497463652953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7853309145183945891262997 368123866180497463652953)
                    ·
                      rfl

theorem cell23_2150756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_2150756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150756 prefixEnd_2150756 := by exact prefixLift 2150756
  have htrace : WordTrace (prefixWord ++ tailWord_2150756) baseStart_2150756 baseEnd_2150756 := by
    simpa [prefixWord, tailWord_2150756, baseEnd_2150756] using wordTrace_append hprefix tailTrace_2150756
  have hstable : (prefixWord ++ tailWord_2150756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150756).length < 2 ^ (prefixWord ++ tailWord_2150756).sum := by decide
  have hdescent : baseEnd_2150756 < baseStart_2150756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150757 : List Nat := [1, 3, 1, 3, 1, 4, 2, 3, 1, 1, 3]
def baseStart_2150757 : Nat := 118140960795 + 2150757 * 2 ^ 59
def prefixEnd_2150757 : Nat := 4983230072969 + 3 ^ 40 * 2150757 * 2
def baseEnd_2150757 : Nat := 1104372112022146887046355

theorem tailTrace_2150757 : CollatzResearch.WordTrace tailWord_2150757 prefixEnd_2150757 1104372112022146887046355 := by
  unfold tailWord_2150757
  simp only [CollatzResearch.WordTrace]
  refine ⟨78444552269182183896866525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52296368179454789264577683 78444552269182183896866525)
  ·
    refine ⟨29416707100943318961324947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78444552269182183896866525 29416707100943318961324947)
    ·
      refine ⟨44125060651414978441987421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29416707100943318961324947 44125060651414978441987421)
      ·
        refine ⟨16546897744280616915745283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44125060651414978441987421 16546897744280616915745283)
        ·
          refine ⟨24820346616420925373617925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16546897744280616915745283 24820346616420925373617925)
          ·
            refine ⟨4653814990578923507553361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24820346616420925373617925 4653814990578923507553361)
            ·
              refine ⟨3490361242934192630665021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4653814990578923507553361 3490361242934192630665021)
              ·
                refine ⟨1308885466100322236499383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3490361242934192630665021 1308885466100322236499383)
                ·
                  refine ⟨1963328199150483354749075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308885466100322236499383 1963328199150483354749075)
                  ·
                    refine ⟨2944992298725725032123613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1963328199150483354749075 2944992298725725032123613)
                    ·
                      refine ⟨1104372112022146887046355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2944992298725725032123613 1104372112022146887046355)
                      ·
                        rfl

theorem cell23_2150757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_2150757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150757 prefixEnd_2150757 := by exact prefixLift 2150757
  have htrace : WordTrace (prefixWord ++ tailWord_2150757) baseStart_2150757 baseEnd_2150757 := by
    simpa [prefixWord, tailWord_2150757, baseEnd_2150757] using wordTrace_append hprefix tailTrace_2150757
  have hstable : (prefixWord ++ tailWord_2150757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150757).length < 2 ^ (prefixWord ++ tailWord_2150757).sum := by decide
  have hdescent : baseEnd_2150757 < baseStart_2150757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150760 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 1, 5]
def baseStart_2150760 : Nat := 118140960795 + 2150760 * 2 ^ 59
def prefixEnd_2150760 : Nat := 4983230072969 + 3 ^ 40 * 2150760 * 2
def baseEnd_2150760 : Nat := 368124550821370125102947

theorem tailTrace_2150760 : CollatzResearch.WordTrace tailWord_2150760 prefixEnd_2150760 368124550821370125102947 := by
  unfold tailWord_2150760
  simp only [CollatzResearch.WordTrace]
  refine ⟨39222330844085657704612867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52296441125447543606150489 39222330844085657704612867)
  ·
    refine ⟨58833496266128486556919301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39222330844085657704612867 58833496266128486556919301)
    ·
      refine ⟨11031280549899091229422369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58833496266128486556919301 11031280549899091229422369)
      ·
        refine ⟨8273460412424318422066777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11031280549899091229422369 8273460412424318422066777)
        ·
          refine ⟨6205095309318238816550083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8273460412424318422066777 6205095309318238816550083)
          ·
            refine ⟨9307642963977358224825125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6205095309318238816550083 9307642963977358224825125)
            ·
              refine ⟨1745183055745754667154711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9307642963977358224825125 1745183055745754667154711)
              ·
                refine ⟨2617774583618632000732067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1745183055745754667154711 2617774583618632000732067)
                ·
                  refine ⟨3926661875427948001098101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617774583618632000732067 3926661875427948001098101)
                  ·
                    refine ⟨368124550821370125102947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3926661875427948001098101 368124550821370125102947)
                    ·
                      rfl

theorem cell23_2150760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_2150760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150760 prefixEnd_2150760 := by exact prefixLift 2150760
  have htrace : WordTrace (prefixWord ++ tailWord_2150760) baseStart_2150760 baseEnd_2150760 := by
    simpa [prefixWord, tailWord_2150760, baseEnd_2150760] using wordTrace_append hprefix tailTrace_2150760
  have hstable : (prefixWord ++ tailWord_2150760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150760).length < 2 ^ (prefixWord ++ tailWord_2150760).sum := by decide
  have hdescent : baseEnd_2150760 < baseStart_2150760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150774 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2150774 : Nat := 118140960795 + 2150774 * 2 ^ 59
def prefixEnd_2150774 : Nat := 4983230072969 + 3 ^ 40 * 2150774 * 2
def baseEnd_2150774 : Nat := 1104380841193273320533777

theorem tailTrace_2150774 : CollatzResearch.WordTrace tailWord_2150774 prefixEnd_2150774 1104380841193273320533777 := by
  unfold tailWord_2150774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4902823269382537237514711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52296781540080397200156917 4902823269382537237514711)
  ·
    refine ⟨7354234904073805856272067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4902823269382537237514711 7354234904073805856272067)
    ·
      refine ⟨11031352356110708784408101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7354234904073805856272067 11031352356110708784408101)
      ·
        refine ⟨2068378566770757897076519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11031352356110708784408101 2068378566770757897076519)
        ·
          refine ⟨3102567850156136845614779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068378566770757897076519 3102567850156136845614779)
          ·
            refine ⟨4653851775234205268422169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102567850156136845614779 4653851775234205268422169)
            ·
              refine ⟨3490388831425653951316627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4653851775234205268422169 3490388831425653951316627)
              ·
                refine ⟨5235583247138480926974941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490388831425653951316627 5235583247138480926974941)
                ·
                  refine ⟨1963343717676930347615603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5235583247138480926974941 1963343717676930347615603)
                  ·
                    refine ⟨2945015576515395521423405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1963343717676930347615603 2945015576515395521423405)
                    ·
                      refine ⟨1104380841193273320533777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2945015576515395521423405 1104380841193273320533777)
                      ·
                        rfl

theorem cell23_2150774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2150774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150774 prefixEnd_2150774 := by exact prefixLift 2150774
  have htrace : WordTrace (prefixWord ++ tailWord_2150774) baseStart_2150774 baseEnd_2150774 := by
    simpa [prefixWord, tailWord_2150774, baseEnd_2150774] using wordTrace_append hprefix tailTrace_2150774
  have hstable : (prefixWord ++ tailWord_2150774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150774).length < 2 ^ (prefixWord ++ tailWord_2150774).sum := by decide
  have hdescent : baseEnd_2150774 < baseStart_2150774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150793 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 4]
def baseStart_2150793 : Nat := 118140960795 + 2150793 * 2 ^ 59
def prefixEnd_2150793 : Nat := 4983230072969 + 3 ^ 40 * 2150793 * 2
def baseEnd_2150793 : Nat := 1104390597325708746196189

theorem tailTrace_2150793 : CollatzResearch.WordTrace tailWord_2150793 prefixEnd_2150793 1104390597325708746196189 := by
  unfold tailWord_2150793
  simp only [CollatzResearch.WordTrace]
  refine ⟨78445865297051762045177033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52297243531367841363451355 78445865297051762045177033)
  ·
    refine ⟨58834398972788821533882775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78445865297051762045177033 58834398972788821533882775)
    ·
      refine ⟨88251598459183232300824163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58834398972788821533882775 88251598459183232300824163)
      ·
        refine ⟨132377397688774848451236245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88251598459183232300824163 132377397688774848451236245)
        ·
          refine ⟨6205190516661321021151699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 132377397688774848451236245 6205190516661321021151699)
          ·
            refine ⟨9307785774991981531727549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6205190516661321021151699 9307785774991981531727549)
            ·
              refine ⟨3490419665621993074397831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9307785774991981531727549 3490419665621993074397831)
              ·
                refine ⟨5235629498432989611596747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490419665621993074397831 5235629498432989611596747)
                ·
                  refine ⟨7853444247649484417395121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5235629498432989611596747 7853444247649484417395121)
                  ·
                    refine ⟨5890083185737113313046341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7853444247649484417395121 5890083185737113313046341)
                    ·
                      refine ⟨1104390597325708746196189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5890083185737113313046341 1104390597325708746196189)
                      ·
                        rfl

theorem cell23_2150793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 4].length) (baseStart_2150793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150793 prefixEnd_2150793 := by exact prefixLift 2150793
  have htrace : WordTrace (prefixWord ++ tailWord_2150793) baseStart_2150793 baseEnd_2150793 := by
    simpa [prefixWord, tailWord_2150793, baseEnd_2150793] using wordTrace_append hprefix tailTrace_2150793
  have hstable : (prefixWord ++ tailWord_2150793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150793).length < 2 ^ (prefixWord ++ tailWord_2150793).sum := by decide
  have hdescent : baseEnd_2150793 < baseStart_2150793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150853 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 7, 4, 2]
def baseStart_2150853 : Nat := 118140960795 + 2150853 * 2 ^ 59
def prefixEnd_2150853 : Nat := 4983230072969 + 3 ^ 40 * 2150853 * 2
def baseEnd_2150853 : Nat := 1104421406164978511445913

theorem tailTrace_2150853 : CollatzResearch.WordTrace tailWord_2150853 prefixEnd_2150853 1104421406164978511445913 := by
  unfold tailWord_2150853
  simp only [CollatzResearch.WordTrace]
  refine ⟨78448053676834392292361213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52298702451222928194907475 78448053676834392292361213)
  ·
    refine ⟨29418020128812897109635455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78448053676834392292361213 29418020128812897109635455)
    ·
      refine ⟨44127030193219345664453183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29418020128812897109635455 44127030193219345664453183)
      ·
        refine ⟨66190545289829018496679775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44127030193219345664453183 66190545289829018496679775)
        ·
          refine ⟨99285817934743527745019663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66190545289829018496679775 99285817934743527745019663)
          ·
            refine ⟨148928726902115291617529495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99285817934743527745019663 148928726902115291617529495)
            ·
              refine ⟨223393090353172937426294243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148928726902115291617529495 223393090353172937426294243)
              ·
                refine ⟨335089635529759406139441365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223393090353172937426294243 335089635529759406139441365)
                ·
                  refine ⟨7853663332728736081393157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 335089635529759406139441365 7853663332728736081393157)
                  ·
                    refine ⟨1472561874886638015261217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7853663332728736081393157 1472561874886638015261217)
                    ·
                      refine ⟨1104421406164978511445913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1472561874886638015261217 1104421406164978511445913)
                      ·
                        rfl

theorem cell23_2150853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_2150853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150853 prefixEnd_2150853 := by exact prefixLift 2150853
  have htrace : WordTrace (prefixWord ++ tailWord_2150853) baseStart_2150853 baseEnd_2150853 := by
    simpa [prefixWord, tailWord_2150853, baseEnd_2150853] using wordTrace_append hprefix tailTrace_2150853
  have hstable : (prefixWord ++ tailWord_2150853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150853).length < 2 ^ (prefixWord ++ tailWord_2150853).sum := by decide
  have hdescent : baseEnd_2150853 < baseStart_2150853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150882 : List Nat := [3, 3, 3, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2150882 : Nat := 118140960795 + 2150882 * 2 ^ 59
def prefixEnd_2150882 : Nat := 4983230072969 + 3 ^ 40 * 2150882 * 2
def baseEnd_2150882 : Nat := 1104436297103958897983281

theorem tailTrace_2150882 : CollatzResearch.WordTrace tailWord_2150882 prefixEnd_2150882 1104436297103958897983281 := by
  unfold tailWord_2150882
  simp only [CollatzResearch.WordTrace]
  refine ⟨19612277848432332561291725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52299407595819553496777933 19612277848432332561291725)
  ·
    refine ⟨7354604193162124710484397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19612277848432332561291725 7354604193162124710484397)
    ·
      refine ⟨2757976572435796766431649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7354604193162124710484397 2757976572435796766431649)
      ·
        refine ⟨2068482429326847574823737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2757976572435796766431649 2068482429326847574823737)
        ·
          refine ⟨1551361821995135681117803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2068482429326847574823737 1551361821995135681117803)
          ·
            refine ⟨2327042732992703521676705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551361821995135681117803 2327042732992703521676705)
            ·
              refine ⟨1745282049744527641257529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2327042732992703521676705 1745282049744527641257529)
              ·
                refine ⟨1308961537308395730943147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1745282049744527641257529 1308961537308395730943147)
                ·
                  refine ⟨1963442305962593596414721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308961537308395730943147 1963442305962593596414721)
                  ·
                    refine ⟨1472581729471945197311041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1963442305962593596414721 1472581729471945197311041)
                    ·
                      refine ⟨1104436297103958897983281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1472581729471945197311041 1104436297103958897983281)
                      ·
                        rfl

theorem cell23_2150882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2150882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150882 prefixEnd_2150882 := by exact prefixLift 2150882
  have htrace : WordTrace (prefixWord ++ tailWord_2150882) baseStart_2150882 baseEnd_2150882 := by
    simpa [prefixWord, tailWord_2150882, baseEnd_2150882] using wordTrace_append hprefix tailTrace_2150882
  have hstable : (prefixWord ++ tailWord_2150882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150882).length < 2 ^ (prefixWord ++ tailWord_2150882).sum := by decide
  have hdescent : baseEnd_2150882 < baseStart_2150882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150923 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 1, 7]
def baseStart_2150923 : Nat := 118140960795 + 2150923 * 2 ^ 59
def prefixEnd_2150923 : Nat := 4983230072969 + 3 ^ 40 * 2150923 * 2
def baseEnd_2150923 : Nat := 368152449936931079190197

theorem tailTrace_2150923 : CollatzResearch.WordTrace tailWord_2150923 prefixEnd_2150923 368152449936931079190197 := by
  unfold tailWord_2150923
  simp only [CollatzResearch.WordTrace]
  refine ⟨78450606786580794247409423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52300404524387196164939615 78450606786580794247409423)
  ·
    refine ⟨117675910179871191371114135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78450606786580794247409423 117675910179871191371114135)
    ·
      refine ⟨176513865269806787056671203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117675910179871191371114135 176513865269806787056671203)
      ·
        refine ⟨264770797904710180585006805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176513865269806787056671203 264770797904710180585006805)
        ·
          refine ⟨6205565575891644857461097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 264770797904710180585006805 6205565575891644857461097)
          ·
            refine ⟨4654174181918733643095823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6205565575891644857461097 4654174181918733643095823)
            ·
              refine ⟨6981261272878100464643735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4654174181918733643095823 6981261272878100464643735)
              ·
                refine ⟨10471891909317150696965603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6981261272878100464643735 10471891909317150696965603)
                ·
                  refine ⟨15707837863975726045448405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10471891909317150696965603 15707837863975726045448405)
                  ·
                    refine ⟨368152449936931079190197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15707837863975726045448405 368152449936931079190197)
                    ·
                      rfl

theorem cell23_2150923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 7].length) (baseStart_2150923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150923 prefixEnd_2150923 := by exact prefixLift 2150923
  have htrace : WordTrace (prefixWord ++ tailWord_2150923) baseStart_2150923 baseEnd_2150923 := by
    simpa [prefixWord, tailWord_2150923, baseEnd_2150923] using wordTrace_append hprefix tailTrace_2150923
  have hstable : (prefixWord ++ tailWord_2150923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150923).length < 2 ^ (prefixWord ++ tailWord_2150923).sum := by decide
  have hdescent : baseEnd_2150923 < baseStart_2150923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150943 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 4]
def baseStart_2150943 : Nat := 118140960795 + 2150943 * 2 ^ 59
def prefixEnd_2150943 : Nat := 4983230072969 + 3 ^ 40 * 2150943 * 2
def baseEnd_2150943 : Nat := 1104467619423883159320499

theorem tailTrace_2150943 : CollatzResearch.WordTrace tailWord_2150943 prefixEnd_2150943 1104467619423883159320499 := by
  unfold tailWord_2150943
  simp only [CollatzResearch.WordTrace]
  refine ⟨78451336246508337663137483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52300890831005558442091655 78451336246508337663137483)
  ·
    refine ⟨117677004369762506494706225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78451336246508337663137483 117677004369762506494706225)
    ·
      refine ⟨88257753277321879871029669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117677004369762506494706225 88257753277321879871029669)
      ·
        refine ⟨16548328739497852475818063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88257753277321879871029669 16548328739497852475818063)
        ·
          refine ⟨24822493109246778713727095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16548328739497852475818063 24822493109246778713727095)
          ·
            refine ⟨37233739663870168070590643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24822493109246778713727095 37233739663870168070590643)
            ·
              refine ⟨55850609495805252105885965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37233739663870168070590643 55850609495805252105885965)
              ·
                refine ⟨20943978560926969539707237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55850609495805252105885965 20943978560926969539707237)
                ·
                  refine ⟨3926995980173806788695107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20943978560926969539707237 3926995980173806788695107)
                  ·
                    refine ⟨5890493970260710183042661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3926995980173806788695107 5890493970260710183042661)
                    ·
                      refine ⟨1104467619423883159320499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5890493970260710183042661 1104467619423883159320499)
                      ·
                        rfl

theorem cell23_2150943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_2150943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150943 prefixEnd_2150943 := by exact prefixLift 2150943
  have htrace : WordTrace (prefixWord ++ tailWord_2150943) baseStart_2150943 baseEnd_2150943 := by
    simpa [prefixWord, tailWord_2150943, baseEnd_2150943] using wordTrace_append hprefix tailTrace_2150943
  have hstable : (prefixWord ++ tailWord_2150943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150943).length < 2 ^ (prefixWord ++ tailWord_2150943).sum := by decide
  have hdescent : baseEnd_2150943 < baseStart_2150943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150960 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 2, 4, 2]
def baseStart_2150960 : Nat := 118140960795 + 2150960 * 2 ^ 59
def prefixEnd_2150960 : Nat := 4983230072969 + 3 ^ 40 * 2150960 * 2
def baseEnd_2150960 : Nat := 1104476348595009592807921

theorem tailTrace_2150960 : CollatzResearch.WordTrace tailWord_2150960 prefixEnd_2150960 1104476348595009592807921 := by
  unfold tailWord_2150960
  simp only [CollatzResearch.WordTrace]
  refine ⟨39225978143723374783253167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52301304191631166377670889 39225978143723374783253167)
  ·
    refine ⟨58838967215585062174879751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39225978143723374783253167 58838967215585062174879751)
    ·
      refine ⟨88258450823377593262319627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58838967215585062174879751 88258450823377593262319627)
      ·
        refine ⟨132387676235066389893479441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88258450823377593262319627 132387676235066389893479441)
        ·
          refine ⟨99290757176299792420109581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132387676235066389893479441 99290757176299792420109581)
          ·
            refine ⟨37234033941112422157541093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99290757176299792420109581 37234033941112422157541093)
            ·
              refine ⟨6981381363958579154538955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37234033941112422157541093 6981381363958579154538955)
              ·
                refine ⟨10472072045937868731808433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6981381363958579154538955 10472072045937868731808433)
                ·
                  refine ⟨7854054034453401548856325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10472072045937868731808433 7854054034453401548856325)
                  ·
                    refine ⟨1472635131460012790410561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7854054034453401548856325 1472635131460012790410561)
                    ·
                      refine ⟨1104476348595009592807921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1472635131460012790410561 1104476348595009592807921)
                      ·
                        rfl

theorem cell23_2150960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 4, 2].length) (baseStart_2150960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150960 prefixEnd_2150960 := by exact prefixLift 2150960
  have htrace : WordTrace (prefixWord ++ tailWord_2150960) baseStart_2150960 baseEnd_2150960 := by
    simpa [prefixWord, tailWord_2150960, baseEnd_2150960] using wordTrace_append hprefix tailTrace_2150960
  have hstable : (prefixWord ++ tailWord_2150960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150960).length < 2 ^ (prefixWord ++ tailWord_2150960).sum := by decide
  have hdescent : baseEnd_2150960 < baseStart_2150960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150963 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 3]
def baseStart_2150963 : Nat := 118140960795 + 2150963 * 2 ^ 59
def prefixEnd_2150963 : Nat := 4983230072969 + 3 ^ 40 * 2150963 * 2
def baseEnd_2150963 : Nat := 1104477889036973081070407

theorem tailTrace_2150963 : CollatzResearch.WordTrace tailWord_2150963 prefixEnd_2150963 1104477889036973081070407 := by
  unfold tailWord_2150963
  simp only [CollatzResearch.WordTrace]
  refine ⟨78452065706435881078865543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52301377137623920719243695 78452065706435881078865543)
  ·
    refine ⟨117678098559653821618298315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78452065706435881078865543 117678098559653821618298315)
    ·
      refine ⟨176517147839480732427447473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117678098559653821618298315 176517147839480732427447473)
      ·
        refine ⟨132387860879610549320585605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176517147839480732427447473 132387860879610549320585605)
        ·
          refine ⟨24822723914926977997609801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132387860879610549320585605 24822723914926977997609801)
          ·
            refine ⟨18617042936195233498207351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24822723914926977997609801 18617042936195233498207351)
            ·
              refine ⟨27925564404292850247311027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18617042936195233498207351 27925564404292850247311027)
              ·
                refine ⟨41888346606439275370966541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27925564404292850247311027 41888346606439275370966541)
                ·
                  refine ⟨15708129977414728264112453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41888346606439275370966541 15708129977414728264112453)
                  ·
                    refine ⟨2945274370765261549521085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15708129977414728264112453 2945274370765261549521085)
                    ·
                      refine ⟨1104477889036973081070407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2945274370765261549521085 1104477889036973081070407)
                      ·
                        rfl

theorem cell23_2150963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 3].length) (baseStart_2150963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150963 prefixEnd_2150963 := by exact prefixLift 2150963
  have htrace : WordTrace (prefixWord ++ tailWord_2150963) baseStart_2150963 baseEnd_2150963 := by
    simpa [prefixWord, tailWord_2150963, baseEnd_2150963] using wordTrace_append hprefix tailTrace_2150963
  have hstable : (prefixWord ++ tailWord_2150963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150963).length < 2 ^ (prefixWord ++ tailWord_2150963).sum := by decide
  have hdescent : baseEnd_2150963 < baseStart_2150963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150970 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_2150970 : Nat := 118140960795 + 2150970 * 2 ^ 59
def prefixEnd_2150970 : Nat := 4983230072969 + 3 ^ 40 * 2150970 * 2
def baseEnd_2150970 : Nat := 368160494467184851227625

theorem tailTrace_2150970 : CollatzResearch.WordTrace tailWord_2150970 prefixEnd_2150970 368160494467184851227625 := by
  unfold tailWord_2150970
  simp only [CollatzResearch.WordTrace]
  refine ⟨19613080254352630318592591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52301547344940347516246909 19613080254352630318592591)
  ·
    refine ⟨29419620381528945477888887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19613080254352630318592591 29419620381528945477888887)
    ·
      refine ⟨44129430572293418216833331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29419620381528945477888887 44129430572293418216833331)
      ·
        refine ⟨66194145858440127325249997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44129430572293418216833331 66194145858440127325249997)
        ·
          refine ⟨24822804696915047746968749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66194145858440127325249997 24822804696915047746968749)
          ·
            refine ⟨9308551761343142905113281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24822804696915047746968749 9308551761343142905113281)
            ·
              refine ⟨6981413821007357178834961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9308551761343142905113281 6981413821007357178834961)
              ·
                refine ⟨5236060365755517884126221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6981413821007357178834961 5236060365755517884126221)
                ·
                  refine ⟨1963522637158319206547333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5236060365755517884126221 1963522637158319206547333)
                  ·
                    refine ⟨368160494467184851227625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1963522637158319206547333 368160494467184851227625)
                    ·
                      rfl

theorem cell23_2150970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_2150970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150970 prefixEnd_2150970 := by exact prefixLift 2150970
  have htrace : WordTrace (prefixWord ++ tailWord_2150970) baseStart_2150970 baseEnd_2150970 := by
    simpa [prefixWord, tailWord_2150970, baseEnd_2150970] using wordTrace_append hprefix tailTrace_2150970
  have hstable : (prefixWord ++ tailWord_2150970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150970).length < 2 ^ (prefixWord ++ tailWord_2150970).sum := by decide
  have hdescent : baseEnd_2150970 < baseStart_2150970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150983 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 8]
def baseStart_2150983 : Nat := 118140960795 + 2150983 * 2 ^ 59
def prefixEnd_2150983 : Nat := 4983230072969 + 3 ^ 40 * 2150983 * 2
def baseEnd_2150983 : Nat := 122720906516673666980035

theorem tailTrace_2150983 : CollatzResearch.WordTrace tailWord_2150983 prefixEnd_2150983 122720906516673666980035 := by
  unfold tailWord_2150983
  simp only [CollatzResearch.WordTrace]
  refine ⟨78452795166363424494593603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52301863444242282996395735 78452795166363424494593603)
  ·
    refine ⟨117679192749545136741890405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78452795166363424494593603 117679192749545136741890405)
    ·
      refine ⟨22064848640539713139104451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117679192749545136741890405 22064848640539713139104451)
      ·
        refine ⟨33097272960809569708656677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22064848640539713139104451 33097272960809569708656677)
        ·
          refine ⟨6205738680151794320373127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33097272960809569708656677 6205738680151794320373127)
          ·
            refine ⟨9308608020227691480559691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6205738680151794320373127 9308608020227691480559691)
            ·
              refine ⟨13962912030341537220839537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9308608020227691480559691 13962912030341537220839537)
              ·
                refine ⟨10472184022756152915629653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13962912030341537220839537 10472184022756152915629653)
                ·
                  refine ⟨122720906516673666980035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10472184022756152915629653 122720906516673666980035)
                  ·
                    rfl

theorem cell23_2150983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 8].length) (baseStart_2150983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150983 prefixEnd_2150983 := by exact prefixLift 2150983
  have htrace : WordTrace (prefixWord ++ tailWord_2150983) baseStart_2150983 baseEnd_2150983 := by
    simpa [prefixWord, tailWord_2150983, baseEnd_2150983] using wordTrace_append hprefix tailTrace_2150983
  have hstable : (prefixWord ++ tailWord_2150983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150983).length < 2 ^ (prefixWord ++ tailWord_2150983).sum := by decide
  have hdescent : baseEnd_2150983 < baseStart_2150983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2150987 : List Nat := [1, 1, 1, 1, 3, 1, 7, 3, 1, 4]
def baseStart_2150987 : Nat := 118140960795 + 2150987 * 2 ^ 59
def prefixEnd_2150987 : Nat := 4983230072969 + 3 ^ 40 * 2150987 * 2
def baseEnd_2150987 : Nat := 368163404190893662390099

theorem tailTrace_2150987 : CollatzResearch.WordTrace tailWord_2150987 prefixEnd_2150987 368163404190893662390099 := by
  unfold tailWord_2150987
  simp only [CollatzResearch.WordTrace]
  refine ⟨78452941058348933177739215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52301960705565955451826143 78452941058348933177739215)
  ·
    refine ⟨117679411587523399766608823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78452941058348933177739215 117679411587523399766608823)
    ·
      refine ⟨176519117381285099649913235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117679411587523399766608823 176519117381285099649913235)
      ·
        refine ⟨264778676071927649474869853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176519117381285099649913235 264778676071927649474869853)
        ·
          refine ⟨99292003526972868553076195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264778676071927649474869853 99292003526972868553076195)
          ·
            refine ⟨148938005290459302829614293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99292003526972868553076195 148938005290459302829614293)
            ·
              refine ⟨3490734498995139910069085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 148938005290459302829614293 3490734498995139910069085)
              ·
                refine ⟨1309025437123177466275907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3490734498995139910069085 1309025437123177466275907)
                ·
                  refine ⟨1963538155684766199413861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309025437123177466275907 1963538155684766199413861)
                  ·
                    refine ⟨368163404190893662390099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1963538155684766199413861 368163404190893662390099)
                    ·
                      rfl

theorem cell23_2150987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 1, 4].length) (baseStart_2150987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2150987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2150987 prefixEnd_2150987 := by exact prefixLift 2150987
  have htrace : WordTrace (prefixWord ++ tailWord_2150987) baseStart_2150987 baseEnd_2150987 := by
    simpa [prefixWord, tailWord_2150987, baseEnd_2150987] using wordTrace_append hprefix tailTrace_2150987
  have hstable : (prefixWord ++ tailWord_2150987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2150987).length < 2 ^ (prefixWord ++ tailWord_2150987).sum := by decide
  have hdescent : baseEnd_2150987 < baseStart_2150987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2150987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151004 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_2151004 : Nat := 118140960795 + 2151004 * 2 ^ 59
def prefixEnd_2151004 : Nat := 4983230072969 + 3 ^ 40 * 2151004 * 2
def baseEnd_2151004 : Nat := 368166313914602473552573

theorem tailTrace_2151004 : CollatzResearch.WordTrace tailWord_2151004 prefixEnd_2151004 368166313914602473552573 := by
  unfold tailWord_2151004
  simp only [CollatzResearch.WordTrace]
  refine ⟨39226780549643672540554033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52302374066191563387405377 39226780549643672540554033)
  ·
    refine ⟨29420085412232754405415525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39226780549643672540554033 29420085412232754405415525)
    ·
      refine ⟨5516266014793641451015411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29420085412232754405415525 5516266014793641451015411)
      ·
        refine ⟨8274399022190462176523117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5516266014793641451015411 8274399022190462176523117)
        ·
          refine ⟨3102899633321423316196169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8274399022190462176523117 3102899633321423316196169)
          ·
            refine ⟨2327174724991067487147127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3102899633321423316196169 2327174724991067487147127)
            ·
              refine ⟨3490762087486601230720691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327174724991067487147127 3490762087486601230720691)
              ·
                refine ⟨5236143131229901846081037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490762087486601230720691 5236143131229901846081037)
                ·
                  refine ⟨1963553674211213192280389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5236143131229901846081037 1963553674211213192280389)
                  ·
                    refine ⟨368166313914602473552573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1963553674211213192280389 368166313914602473552573)
                    ·
                      rfl

theorem cell23_2151004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_2151004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151004 prefixEnd_2151004 := by exact prefixLift 2151004
  have htrace : WordTrace (prefixWord ++ tailWord_2151004) baseStart_2151004 baseEnd_2151004 := by
    simpa [prefixWord, tailWord_2151004, baseEnd_2151004] using wordTrace_append hprefix tailTrace_2151004
  have hstable : (prefixWord ++ tailWord_2151004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151004).length < 2 ^ (prefixWord ++ tailWord_2151004).sum := by decide
  have hdescent : baseEnd_2151004 < baseStart_2151004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151020 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 3, 5, 2]
def baseStart_2151020 : Nat := 118140960795 + 2151020 * 2 ^ 59
def prefixEnd_2151020 : Nat := 4983230072969 + 3 ^ 40 * 2151020 * 2
def baseEnd_2151020 : Nat := 1104507157434279358057645

theorem tailTrace_2151020 : CollatzResearch.WordTrace tailWord_2151020 prefixEnd_2151020 1104507157434279358057645 := by
  unfold tailWord_2151020
  simp only [CollatzResearch.WordTrace]
  refine ⟨39227072333614689906845257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52302763111486253209127009 39227072333614689906845257)
  ·
    refine ⟨29420304250211017430133943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39227072333614689906845257 29420304250211017430133943)
    ·
      refine ⟨44130456375316526145200915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29420304250211017430133943 44130456375316526145200915)
      ·
        refine ⟨66195684562974789217801373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44130456375316526145200915 66195684562974789217801373)
        ·
          refine ⟨24823381711115545956675515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66195684562974789217801373 24823381711115545956675515)
          ·
            refine ⟨37235072566673318935013273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24823381711115545956675515 37235072566673318935013273)
            ·
              refine ⟨27926304425004989201259955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37235072566673318935013273 27926304425004989201259955)
              ·
                refine ⟨41889456637507483801889933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27926304425004989201259955 41889456637507483801889933)
                ·
                  refine ⟨15708546239065306425708725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41889456637507483801889933 15708546239065306425708725)
                  ·
                    refine ⟨1472676209912372477410193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15708546239065306425708725 1472676209912372477410193)
                    ·
                      refine ⟨1104507157434279358057645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1472676209912372477410193 1104507157434279358057645)
                      ·
                        rfl

theorem cell23_2151020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_2151020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151020 prefixEnd_2151020 := by exact prefixLift 2151020
  have htrace : WordTrace (prefixWord ++ tailWord_2151020) baseStart_2151020 baseEnd_2151020 := by
    simpa [prefixWord, tailWord_2151020, baseEnd_2151020] using wordTrace_append hprefix tailTrace_2151020
  have hstable : (prefixWord ++ tailWord_2151020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151020).length < 2 ^ (prefixWord ++ tailWord_2151020).sum := by decide
  have hdescent : baseEnd_2151020 < baseStart_2151020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151043 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 3, 6]
def baseStart_2151043 : Nat := 118140960795 + 2151043 * 2 ^ 59
def prefixEnd_2151043 : Nat := 4983230072969 + 3 ^ 40 * 2151043 * 2
def baseEnd_2151043 : Nat := 368172989163110922690013

theorem tailTrace_2151043 : CollatzResearch.WordTrace tailWord_2151043 prefixEnd_2151043 368172989163110922690013 := by
  unfold tailWord_2151043
  simp only [CollatzResearch.WordTrace]
  refine ⟨78454983546146054741777783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52303322364097369827851855 78454983546146054741777783)
  ·
    refine ⟨117682475319219082112666675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78454983546146054741777783 117682475319219082112666675)
    ·
      refine ⟨176523712978828623169000013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117682475319219082112666675 176523712978828623169000013)
      ·
        refine ⟨66196392367060733688375005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176523712978828623169000013 66196392367060733688375005)
        ·
          refine ⟨24823647137647775133140627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66196392367060733688375005 24823647137647775133140627)
          ·
            refine ⟨37235470706471662699710941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24823647137647775133140627 37235470706471662699710941)
            ·
              refine ⟨13963301514926873512391603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37235470706471662699710941 13963301514926873512391603)
              ·
                refine ⟨20944952272390310268587405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13963301514926873512391603 20944952272390310268587405)
                ·
                  refine ⟨7854357102146366350720277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20944952272390310268587405 7854357102146366350720277)
                  ·
                    refine ⟨368172989163110922690013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7854357102146366350720277 368172989163110922690013)
                    ·
                      rfl

theorem cell23_2151043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 6].length) (baseStart_2151043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151043 prefixEnd_2151043 := by exact prefixLift 2151043
  have htrace : WordTrace (prefixWord ++ tailWord_2151043) baseStart_2151043 baseEnd_2151043 := by
    simpa [prefixWord, tailWord_2151043, baseEnd_2151043] using wordTrace_append hprefix tailTrace_2151043
  have hstable : (prefixWord ++ tailWord_2151043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151043).length < 2 ^ (prefixWord ++ tailWord_2151043).sum := by decide
  have hdescent : baseEnd_2151043 < baseStart_2151043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151047 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 1, 5]
def baseStart_2151047 : Nat := 118140960795 + 2151047 * 2 ^ 59
def prefixEnd_2151047 : Nat := 4983230072969 + 3 ^ 40 * 2151047 * 2
def baseEnd_2151047 : Nat := 368173673803983584140007

theorem tailTrace_2151047 : CollatzResearch.WordTrace tailWord_2151047 prefixEnd_2151047 368173673803983584140007 := by
  unfold tailWord_2151047
  simp only [CollatzResearch.WordTrace]
  refine ⟨78455129438131563424923395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52303419625421042283282263 78455129438131563424923395)
  ·
    refine ⟨117682694157197345137385093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78455129438131563424923395 117682694157197345137385093)
    ·
      refine ⟨22065505154474502213259705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117682694157197345137385093 22065505154474502213259705)
      ·
        refine ⟨16549128865855876659944779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22065505154474502213259705 16549128865855876659944779)
        ·
          refine ⟨24823693298783814989917169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16549128865855876659944779 24823693298783814989917169)
          ·
            refine ⟨18617769974087861242437877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24823693298783814989917169 18617769974087861242437877)
            ·
              refine ⟨1745415935070736991478551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18617769974087861242437877 1745415935070736991478551)
              ·
                refine ⟨2618123902606105487217827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1745415935070736991478551 2618123902606105487217827)
                ·
                  refine ⟨3927185853909158230826741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618123902606105487217827 3927185853909158230826741)
                  ·
                    refine ⟨368173673803983584140007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3927185853909158230826741 368173673803983584140007)
                    ·
                      rfl

theorem cell23_2151047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_2151047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151047 prefixEnd_2151047 := by exact prefixLift 2151047
  have htrace : WordTrace (prefixWord ++ tailWord_2151047) baseStart_2151047 baseEnd_2151047 := by
    simpa [prefixWord, tailWord_2151047, baseEnd_2151047] using wordTrace_append hprefix tailTrace_2151047
  have hstable : (prefixWord ++ tailWord_2151047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151047).length < 2 ^ (prefixWord ++ tailWord_2151047).sum := by decide
  have hdescent : baseEnd_2151047 < baseStart_2151047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151101 : List Nat := [1, 4, 1, 2, 1, 3, 1, 5, 1, 2, 2]
def baseStart_2151101 : Nat := 118140960795 + 2151101 * 2 ^ 59
def prefixEnd_2151101 : Nat := 4983230072969 + 3 ^ 40 * 2151101 * 2
def baseEnd_2151101 : Nat := 1104548749367293541144773

theorem tailTrace_2151101 : CollatzResearch.WordTrace tailWord_2151101 prefixEnd_2151101 1104548749367293541144773 := by
  unfold tailWord_2151101
  simp only [CollatzResearch.WordTrace]
  refine ⟨78457098979935930647389157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52304732653290620431592771 78457098979935930647389157)
  ·
    refine ⟨14710706058737986996385467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78457098979935930647389157 14710706058737986996385467)
    ·
      refine ⟨22066059088106980494578201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14710706058737986996385467 22066059088106980494578201)
      ·
        refine ⟨16549544316080235370933651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22066059088106980494578201 16549544316080235370933651)
        ·
          refine ⟨24824316474120353056400477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16549544316080235370933651 24824316474120353056400477)
          ·
            refine ⟨9309118677795132396150179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24824316474120353056400477 9309118677795132396150179)
            ·
              refine ⟨13963678016692698594225269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9309118677795132396150179 13963678016692698594225269)
              ·
                refine ⟨1309094814064940493208619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13963678016692698594225269 1309094814064940493208619)
                ·
                  refine ⟨1963642221097410739812929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309094814064940493208619 1963642221097410739812929)
                  ·
                    refine ⟨1472731665823058054859697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1963642221097410739812929 1472731665823058054859697)
                    ·
                      refine ⟨1104548749367293541144773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1472731665823058054859697 1104548749367293541144773)
                      ·
                        rfl

theorem cell23_2151101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_2151101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151101 prefixEnd_2151101 := by exact prefixLift 2151101
  have htrace : WordTrace (prefixWord ++ tailWord_2151101) baseStart_2151101 baseEnd_2151101 := by
    simpa [prefixWord, tailWord_2151101, baseEnd_2151101] using wordTrace_append hprefix tailTrace_2151101
  have hstable : (prefixWord ++ tailWord_2151101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151101).length < 2 ^ (prefixWord ++ tailWord_2151101).sum := by decide
  have hdescent : baseEnd_2151101 < baseStart_2151101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151104 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 1, 2, 3]
def baseStart_2151104 : Nat := 118140960795 + 2151104 * 2 ^ 59
def prefixEnd_2151104 : Nat := 4983230072969 + 3 ^ 40 * 2151104 * 2
def baseEnd_2151104 : Nat := 1104550289809257029407259

theorem tailTrace_2151104 : CollatzResearch.WordTrace tailWord_2151104 prefixEnd_2151104 1104550289809257029407259 := by
  unfold tailWord_2151104
  simp only [CollatzResearch.WordTrace]
  refine ⟨39228604199462531079874183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52304805599283374773165577 39228604199462531079874183)
  ·
    refine ⟨58842906299193796619811275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39228604199462531079874183 58842906299193796619811275)
    ·
      refine ⟨88264359448790694929716913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58842906299193796619811275 88264359448790694929716913)
      ·
        refine ⟨66198269586593021197287685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88264359448790694929716913 66198269586593021197287685)
        ·
          refine ⟨12412175547486191474491441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66198269586593021197287685 12412175547486191474491441)
          ·
            refine ⟨9309131660614643605868581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12412175547486191474491441 9309131660614643605868581)
            ·
              refine ⟨1745462186365245676100359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9309131660614643605868581 1745462186365245676100359)
              ·
                refine ⟨2618193279547868514150539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1745462186365245676100359 2618193279547868514150539)
                ·
                  refine ⟨3927289919321802771225809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618193279547868514150539 3927289919321802771225809)
                  ·
                    refine ⟨2945467439491352078419357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3927289919321802771225809 2945467439491352078419357)
                    ·
                      refine ⟨1104550289809257029407259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2945467439491352078419357 1104550289809257029407259)
                      ·
                        rfl

theorem cell23_2151104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_2151104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151104 prefixEnd_2151104 := by exact prefixLift 2151104
  have htrace : WordTrace (prefixWord ++ tailWord_2151104) baseStart_2151104 baseEnd_2151104 := by
    simpa [prefixWord, tailWord_2151104, baseEnd_2151104] using wordTrace_append hprefix tailTrace_2151104
  have hstable : (prefixWord ++ tailWord_2151104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151104).length < 2 ^ (prefixWord ++ tailWord_2151104).sum := by decide
  have hdescent : baseEnd_2151104 < baseStart_2151104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151160 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_2151160 : Nat := 118140960795 + 2151160 * 2 ^ 59
def prefixEnd_2151160 : Nat := 4983230072969 + 3 ^ 40 * 2151160 * 2
def baseEnd_2151160 : Nat := 1104579044725908810307001

theorem tailTrace_2151160 : CollatzResearch.WordTrace tailWord_2151160 prefixEnd_2151160 1104579044725908810307001 := by
  unfold tailWord_2151160
  simp only [CollatzResearch.WordTrace]
  refine ⟨39229625443361091861893467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52306167257814789149191289 39229625443361091861893467)
  ·
    refine ⟨58844438165041637792840201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39229625443361091861893467 58844438165041637792840201)
    ·
      refine ⟨44133328623781228344630151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58844438165041637792840201 44133328623781228344630151)
      ·
        refine ⟨66199992935671842516945227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44133328623781228344630151 66199992935671842516945227)
        ·
          refine ⟨99299989403507763775417841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66199992935671842516945227 99299989403507763775417841)
          ·
            refine ⟨74474992052630822831563381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99299989403507763775417841 74474992052630822831563381)
            ·
              refine ⟨6982030504934139640459067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74474992052630822831563381 6982030504934139640459067)
              ·
                refine ⟨10473045757401209460688601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6982030504934139640459067 10473045757401209460688601)
                ·
                  refine ⟨7854784318050907095516451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10473045757401209460688601 7854784318050907095516451)
                  ·
                    refine ⟨11782176477076360643274677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7854784318050907095516451 11782176477076360643274677)
                    ·
                      refine ⟨1104579044725908810307001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11782176477076360643274677 1104579044725908810307001)
                      ·
                        rfl

theorem cell23_2151160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_2151160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151160 prefixEnd_2151160 := by exact prefixLift 2151160
  have htrace : WordTrace (prefixWord ++ tailWord_2151160) baseStart_2151160 baseEnd_2151160 := by
    simpa [prefixWord, tailWord_2151160, baseEnd_2151160] using wordTrace_append hprefix tailTrace_2151160
  have hstable : (prefixWord ++ tailWord_2151160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151160).length < 2 ^ (prefixWord ++ tailWord_2151160).sum := by decide
  have hdescent : baseEnd_2151160 < baseStart_2151160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151231 : List Nat := [1, 1, 2, 2, 5, 3, 2, 2, 5]
def baseStart_2151231 : Nat := 118140960795 + 2151231 * 2 ^ 59
def prefixEnd_2151231 : Nat := 4983230072969 + 3 ^ 40 * 2151231 * 2
def baseEnd_2151231 : Nat := 122735055761375336946575

theorem tailTrace_2151231 : CollatzResearch.WordTrace tailWord_2151231 prefixEnd_2151231 122735055761375336946575 := by
  unfold tailWord_2151231
  simp only [CollatzResearch.WordTrace]
  refine ⟨78461840469464962849621547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52307893646309975233081031 78461840469464962849621547)
  ·
    refine ⟨117692760704197444274432321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78461840469464962849621547 117692760704197444274432321)
    ·
      refine ⟨88269570528148083205824241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117692760704197444274432321 88269570528148083205824241)
      ·
        refine ⟨66202177896111062404368181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88269570528148083205824241 66202177896111062404368181)
        ·
          refine ⟨6206454177760412100409517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66202177896111062404368181 6206454177760412100409517)
          ·
            refine ⟨2327420316660154537653569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6206454177760412100409517 2327420316660154537653569)
            ·
              refine ⟨1745565237495115903240177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2327420316660154537653569 1745565237495115903240177)
              ·
                refine ⟨1309173928121336927430133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1745565237495115903240177 1309173928121336927430133)
                ·
                  refine ⟨122735055761375336946575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1309173928121336927430133 122735055761375336946575)
                  ·
                    rfl

theorem cell23_2151231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 5].length) (baseStart_2151231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151231 prefixEnd_2151231 := by exact prefixLift 2151231
  have htrace : WordTrace (prefixWord ++ tailWord_2151231) baseStart_2151231 baseEnd_2151231 := by
    simpa [prefixWord, tailWord_2151231, baseEnd_2151231] using wordTrace_append hprefix tailTrace_2151231
  have hstable : (prefixWord ++ tailWord_2151231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151231).length < 2 ^ (prefixWord ++ tailWord_2151231).sum := by decide
  have hdescent : baseEnd_2151231 < baseStart_2151231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151257 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 5, 4]
def baseStart_2151257 : Nat := 118140960795 + 2151257 * 2 ^ 59
def prefixEnd_2151257 : Nat := 4983230072969 + 3 ^ 40 * 2151257 * 2
def baseEnd_2151257 : Nat := 368209617449798310264685

theorem tailTrace_2151257 : CollatzResearch.WordTrace tailWord_2151257 prefixEnd_2151257 368209617449798310264685 := by
  unfold tailWord_2151257
  simp only [CollatzResearch.WordTrace]
  refine ⟨78462788767370769290068025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52308525844913846193378683 78462788767370769290068025)
  ·
    refine ⟨58847091575528076967551019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78462788767370769290068025 58847091575528076967551019)
    ·
      refine ⟨88270637363292115451326529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58847091575528076967551019 88270637363292115451326529)
      ·
        refine ⟨66202978022469086588494897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88270637363292115451326529 66202978022469086588494897)
        ·
          refine ⟨49652233516851814941371173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66202978022469086588494897 49652233516851814941371173)
          ·
            refine ⟨9309793784409715301507095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49652233516851814941371173 9309793784409715301507095)
            ·
              refine ⟨13964690676614572952260643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9309793784409715301507095 13964690676614572952260643)
              ·
                refine ⟨20947036014921859428390965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13964690676614572952260643 20947036014921859428390965)
                ·
                  refine ⟨1963784626398924321411653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20947036014921859428390965 1963784626398924321411653)
                  ·
                    refine ⟨368209617449798310264685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1963784626398924321411653 368209617449798310264685)
                    ·
                      rfl

theorem cell23_2151257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 4].length) (baseStart_2151257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151257 prefixEnd_2151257 := by exact prefixLift 2151257
  have htrace : WordTrace (prefixWord ++ tailWord_2151257) baseStart_2151257 baseEnd_2151257 := by
    simpa [prefixWord, tailWord_2151257, baseEnd_2151257] using wordTrace_append hprefix tailTrace_2151257
  have hstable : (prefixWord ++ tailWord_2151257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151257).length < 2 ^ (prefixWord ++ tailWord_2151257).sum := by decide
  have hdescent : baseEnd_2151257 < baseStart_2151257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151318 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2151318 : Nat := 118140960795 + 2151318 * 2 ^ 59
def prefixEnd_2151318 : Nat := 4983230072969 + 3 ^ 40 * 2151318 * 2
def baseEnd_2151318 : Nat := 1104660174669319192131275

theorem tailTrace_2151318 : CollatzResearch.WordTrace tailWord_2151318 prefixEnd_2151318 1104660174669319192131275 := by
  unfold tailWord_2151318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4904063351259361044252413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52310009080099851138692405 4904063351259361044252413)
  ·
    refine ⟨1839023756722260391594655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4904063351259361044252413 1839023756722260391594655)
    ·
      refine ⟨2758535635083390587391983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1839023756722260391594655 2758535635083390587391983)
      ·
        refine ⟨4137803452625085881087975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2758535635083390587391983 4137803452625085881087975)
        ·
          refine ⟨6206705178937628821631963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4137803452625085881087975 6206705178937628821631963)
          ·
            refine ⟨9310057768406443232447945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6206705178937628821631963 9310057768406443232447945)
            ·
              refine ⟨6982543326304832424335959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9310057768406443232447945 6982543326304832424335959)
              ·
                refine ⟨10473814989457248636503939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6982543326304832424335959 10473814989457248636503939)
                ·
                  refine ⟨15710722484185872954755909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10473814989457248636503939 15710722484185872954755909)
                  ·
                    refine ⟨2945760465784851179016733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15710722484185872954755909 2945760465784851179016733)
                    ·
                      refine ⟨1104660174669319192131275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2945760465784851179016733 1104660174669319192131275)
                      ·
                        rfl

theorem cell23_2151318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2151318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151318 prefixEnd_2151318 := by exact prefixLift 2151318
  have htrace : WordTrace (prefixWord ++ tailWord_2151318) baseStart_2151318 baseEnd_2151318 := by
    simpa [prefixWord, tailWord_2151318, baseEnd_2151318] using wordTrace_append hprefix tailTrace_2151318
  have hstable : (prefixWord ++ tailWord_2151318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151318).length < 2 ^ (prefixWord ++ tailWord_2151318).sum := by decide
  have hdescent : baseEnd_2151318 < baseStart_2151318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151367 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_2151367 : Nat := 118140960795 + 2151367 * 2 ^ 59
def prefixEnd_2151367 : Nat := 4983230072969 + 3 ^ 40 * 2151367 * 2
def baseEnd_2151367 : Nat := 1104685335221389500418549

theorem tailTrace_2151367 : CollatzResearch.WordTrace tailWord_2151367 prefixEnd_2151367 1104685335221389500418549 := by
  unfold tailWord_2151367
  simp only [CollatzResearch.WordTrace]
  refine ⟨78466800796972258076572355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52311200531314838717714903 78466800796972258076572355)
  ·
    refine ⟨117700201195458387114858533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78466800796972258076572355 117700201195458387114858533)
    ·
      refine ⟨22068787724148447584035975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117700201195458387114858533 22068787724148447584035975)
      ·
        refine ⟨33103181586222671376053963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22068787724148447584035975 33103181586222671376053963)
        ·
          refine ⟨49654772379334007064080945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33103181586222671376053963 49654772379334007064080945)
          ·
            refine ⟨37241079284500505298060709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49654772379334007064080945 37241079284500505298060709)
            ·
              refine ⟨6982702365843844743386383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37241079284500505298060709 6982702365843844743386383)
              ·
                refine ⟨10474053548765767115079575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6982702365843844743386383 10474053548765767115079575)
                ·
                  refine ⟨15711080323148650672619363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10474053548765767115079575 15711080323148650672619363)
                  ·
                    refine ⟨23566620484722976008929045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15711080323148650672619363 23566620484722976008929045)
                    ·
                      refine ⟨1104685335221389500418549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23566620484722976008929045 1104685335221389500418549)
                      ·
                        rfl

theorem cell23_2151367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_2151367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151367 prefixEnd_2151367 := by exact prefixLift 2151367
  have htrace : WordTrace (prefixWord ++ tailWord_2151367) baseStart_2151367 baseEnd_2151367 := by
    simpa [prefixWord, tailWord_2151367, baseEnd_2151367] using wordTrace_append hprefix tailTrace_2151367
  have hstable : (prefixWord ++ tailWord_2151367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151367).length < 2 ^ (prefixWord ++ tailWord_2151367).sum := by decide
  have hdescent : baseEnd_2151367 < baseStart_2151367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151368 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 1, 5]
def baseStart_2151368 : Nat := 118140960795 + 2151368 * 2 ^ 59
def prefixEnd_2151368 : Nat := 4983230072969 + 3 ^ 40 * 2151368 * 2
def baseEnd_2151368 : Nat := 368228616234014665502015

theorem tailTrace_2151368 : CollatzResearch.WordTrace tailWord_2151368 prefixEnd_2151368 368228616234014665502015 := by
  unfold tailWord_2151368
  simp only [CollatzResearch.WordTrace]
  refine ⟨39233418634984317623679379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52311224846645756831572505 39233418634984317623679379)
  ·
    refine ⟨58850127952476476435519069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39233418634984317623679379 58850127952476476435519069)
    ·
      refine ⟨22068797982178678663319651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58850127952476476435519069 22068797982178678663319651)
      ·
        refine ⟨33103196973268017994979477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22068797982178678663319651 33103196973268017994979477)
        ·
          refine ⟨1551712358121938343514663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33103196973268017994979477 1551712358121938343514663)
          ·
            refine ⟨2327568537182907515271995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551712358121938343514663 2327568537182907515271995)
            ·
              refine ⟨3491352805774361272907993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327568537182907515271995 3491352805774361272907993)
              ·
                refine ⟨2618514604330770954680995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3491352805774361272907993 2618514604330770954680995)
                ·
                  refine ⟨3927771906496156432021493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618514604330770954680995 3927771906496156432021493)
                  ·
                    refine ⟨368228616234014665502015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3927771906496156432021493 368228616234014665502015)
                    ·
                      rfl

theorem cell23_2151368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_2151368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151368 prefixEnd_2151368 := by exact prefixLift 2151368
  have htrace : WordTrace (prefixWord ++ tailWord_2151368) baseStart_2151368 baseEnd_2151368 := by
    simpa [prefixWord, tailWord_2151368, baseEnd_2151368] using wordTrace_append hprefix tailTrace_2151368
  have hstable : (prefixWord ++ tailWord_2151368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151368).length < 2 ^ (prefixWord ++ tailWord_2151368).sum := by decide
  have hdescent : baseEnd_2151368 < baseStart_2151368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151371 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 4]
def baseStart_2151371 : Nat := 118140960795 + 2151371 * 2 ^ 59
def prefixEnd_2151371 : Nat := 4983230072969 + 3 ^ 40 * 2151371 * 2
def baseEnd_2151371 : Nat := 1104687389144007484768531

theorem tailTrace_2151371 : CollatzResearch.WordTrace tailWord_2151371 prefixEnd_2151371 1104687389144007484768531 := by
  unfold tailWord_2151371
  simp only [CollatzResearch.WordTrace]
  refine ⟨78466946688957766759717967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52311297792638511173145311 78466946688957766759717967)
  ·
    refine ⟨117700420033436650139576951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78466946688957766759717967 117700420033436650139576951)
    ·
      refine ⟨176550630050154975209365427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117700420033436650139576951 176550630050154975209365427)
      ·
        refine ⟨264825945075232462814048141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176550630050154975209365427 264825945075232462814048141)
        ·
          refine ⟨99309729403212173555268053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264825945075232462814048141 99309729403212173555268053)
          ·
            refine ⟨2327571782887785317701595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 99309729403212173555268053 2327571782887785317701595)
            ·
              refine ⟨3491357674331677976552393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327571782887785317701595 3491357674331677976552393)
              ·
                refine ⟨2618518255748758482414295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3491357674331677976552393 2618518255748758482414295)
                ·
                  refine ⟨3927777383623137723621443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618518255748758482414295 3927777383623137723621443)
                  ·
                    refine ⟨5891666075434706585432165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3927777383623137723621443 5891666075434706585432165)
                    ·
                      refine ⟨1104687389144007484768531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5891666075434706585432165 1104687389144007484768531)
                      ·
                        rfl

theorem cell23_2151371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 4].length) (baseStart_2151371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151371 prefixEnd_2151371 := by exact prefixLift 2151371
  have htrace : WordTrace (prefixWord ++ tailWord_2151371) baseStart_2151371 baseEnd_2151371 := by
    simpa [prefixWord, tailWord_2151371, baseEnd_2151371] using wordTrace_append hprefix tailTrace_2151371
  have hstable : (prefixWord ++ tailWord_2151371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151371).length < 2 ^ (prefixWord ++ tailWord_2151371).sum := by decide
  have hdescent : baseEnd_2151371 < baseStart_2151371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151384 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2151384 : Nat := 118140960795 + 2151384 * 2 ^ 59
def prefixEnd_2151384 : Nat := 4983230072969 + 3 ^ 40 * 2151384 * 2
def baseEnd_2151384 : Nat := 1104694064392515933905971

theorem tailTrace_2151384 : CollatzResearch.WordTrace tailWord_2151384 prefixEnd_2151384 1104694064392515933905971 := by
  unfold tailWord_2151384
  simp only [CollatzResearch.WordTrace]
  refine ⟨39233710418955334989970603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52311613891940446653294137 39233710418955334989970603)
  ·
    refine ⟨58850565628433002484955905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39233710418955334989970603 58850565628433002484955905)
    ·
      refine ⟨44137924221324751863716929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58850565628433002484955905 44137924221324751863716929)
      ·
        refine ⟨33103443165993563897787697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44137924221324751863716929 33103443165993563897787697)
        ·
          refine ⟨24827582374495172923340773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33103443165993563897787697 24827582374495172923340773)
          ·
            refine ⟨4655171695217844923126395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24827582374495172923340773 4655171695217844923126395)
            ·
              refine ⟨6982757542826767384689593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4655171695217844923126395 6982757542826767384689593)
              ·
                refine ⟨5237068157120075538517195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6982757542826767384689593 5237068157120075538517195)
                ·
                  refine ⟨7855602235680113307775793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5237068157120075538517195 7855602235680113307775793)
                  ·
                    refine ⟨5891701676760084980831845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7855602235680113307775793 5891701676760084980831845)
                    ·
                      refine ⟨1104694064392515933905971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5891701676760084980831845 1104694064392515933905971)
                      ·
                        rfl

theorem cell23_2151384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2151384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151384 prefixEnd_2151384 := by exact prefixLift 2151384
  have htrace : WordTrace (prefixWord ++ tailWord_2151384) baseStart_2151384 baseEnd_2151384 := by
    simpa [prefixWord, tailWord_2151384, baseEnd_2151384] using wordTrace_append hprefix tailTrace_2151384
  have hstable : (prefixWord ++ tailWord_2151384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151384).length < 2 ^ (prefixWord ++ tailWord_2151384).sum := by decide
  have hdescent : baseEnd_2151384 < baseStart_2151384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151391 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 5]
def baseStart_2151391 : Nat := 118140960795 + 2151391 * 2 ^ 59
def prefixEnd_2151391 : Nat := 4983230072969 + 3 ^ 40 * 2151391 * 2
def baseEnd_2151391 : Nat := 1104697658757097406518439

theorem tailTrace_2151391 : CollatzResearch.WordTrace tailWord_2151391 prefixEnd_2151391 1104697658757097406518439 := by
  unfold tailWord_2151391
  simp only [CollatzResearch.WordTrace]
  refine ⟨78467676148885310175446027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52311784099256873450297351 78467676148885310175446027)
  ·
    refine ⟨117701514223327965263169041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78467676148885310175446027 117701514223327965263169041)
    ·
      refine ⟨88276135667495973947376781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117701514223327965263169041 88276135667495973947376781)
      ·
        refine ⟨33103550875310990230266293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88276135667495973947376781 33103550875310990230266293)
        ·
          refine ⟨3103457894560405334087465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33103550875310990230266293 3103457894560405334087465)
          ·
            refine ⟨2327593420920304000565599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3103457894560405334087465 2327593420920304000565599)
            ·
              refine ⟨3491390131380456000848399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327593420920304000565599 3491390131380456000848399)
              ·
                refine ⟨5237085197070684001272599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3491390131380456000848399 5237085197070684001272599)
                ·
                  refine ⟨7855627795606026001908899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5237085197070684001272599 7855627795606026001908899)
                  ·
                    refine ⟨11783441693409039002863349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7855627795606026001908899 11783441693409039002863349)
                    ·
                      refine ⟨1104697658757097406518439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11783441693409039002863349 1104697658757097406518439)
                      ·
                        rfl

theorem cell23_2151391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_2151391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151391 prefixEnd_2151391 := by exact prefixLift 2151391
  have htrace : WordTrace (prefixWord ++ tailWord_2151391) baseStart_2151391 baseEnd_2151391 := by
    simpa [prefixWord, tailWord_2151391, baseEnd_2151391] using wordTrace_append hprefix tailTrace_2151391
  have hstable : (prefixWord ++ tailWord_2151391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151391).length < 2 ^ (prefixWord ++ tailWord_2151391).sum := by decide
  have hdescent : baseEnd_2151391 < baseStart_2151391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151394 : List Nat := [3, 3, 3, 1, 1, 12]
def baseStart_2151394 : Nat := 118140960795 + 2151394 * 2 ^ 59
def prefixEnd_2151394 : Nat := 4983230072969 + 3 ^ 40 * 2151394 * 2
def baseEnd_2151394 : Nat := 4546087239502308208975

theorem tailTrace_2151394 : CollatzResearch.WordTrace tailWord_2151394 prefixEnd_2151394 4546087239502308208975 := by
  unfold tailWord_2151394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19616946391968610421951309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52311857045249627791870157 19616946391968610421951309)
  ·
    refine ⟨7356354896988228908231741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19616946391968610421951309 7356354896988228908231741)
    ·
      refine ⟨2758633086370585840586903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7356354896988228908231741 2758633086370585840586903)
      ·
        refine ⟨4137949629555878760880355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2758633086370585840586903 4137949629555878760880355)
        ·
          refine ⟨6206924444333818141320533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4137949629555878760880355 6206924444333818141320533)
          ·
            refine ⟨4546087239502308208975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6206924444333818141320533 4546087239502308208975)
            ·
              rfl

theorem cell23_2151394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 12].length) (baseStart_2151394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151394 prefixEnd_2151394 := by exact prefixLift 2151394
  have htrace : WordTrace (prefixWord ++ tailWord_2151394) baseStart_2151394 baseEnd_2151394 := by
    simpa [prefixWord, tailWord_2151394, baseEnd_2151394] using wordTrace_append hprefix tailTrace_2151394
  have hstable : (prefixWord ++ tailWord_2151394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151394).length < 2 ^ (prefixWord ++ tailWord_2151394).sum := by decide
  have hdescent : baseEnd_2151394 < baseStart_2151394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151407 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 2, 7]
def baseStart_2151407 : Nat := 118140960795 + 2151407 * 2 ^ 59
def prefixEnd_2151407 : Nat := 4983230072969 + 3 ^ 40 * 2151407 * 2
def baseEnd_2151407 : Nat := 368235291482523114639455

theorem tailTrace_2151407 : CollatzResearch.WordTrace tailWord_2151407 prefixEnd_2151407 368235291482523114639455 := by
  unfold tailWord_2151407
  simp only [CollatzResearch.WordTrace]
  refine ⟨78468259716827344908028475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52312173144551563272018983 78468259716827344908028475)
  ·
    refine ⟨117702389575241017362042713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78468259716827344908028475 117702389575241017362042713)
    ·
      refine ⟨88276792181430763021532035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117702389575241017362042713 88276792181430763021532035)
      ·
        refine ⟨132415188272146144532298053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88276792181430763021532035 132415188272146144532298053)
        ·
          refine ⟨24827847801027402099805885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132415188272146144532298053 24827847801027402099805885)
          ·
            refine ⟨9310442925385275787427207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24827847801027402099805885 9310442925385275787427207)
            ·
              refine ⟨13965664388077913681140811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9310442925385275787427207 13965664388077913681140811)
              ·
                refine ⟨20948496582116870521711217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13965664388077913681140811 20948496582116870521711217)
                ·
                  refine ⟨15711372436587652891283413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20948496582116870521711217 15711372436587652891283413)
                  ·
                    refine ⟨368235291482523114639455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15711372436587652891283413 368235291482523114639455)
                    ·
                      rfl

theorem cell23_2151407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_2151407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151407 prefixEnd_2151407 := by exact prefixLift 2151407
  have htrace : WordTrace (prefixWord ++ tailWord_2151407) baseStart_2151407 baseEnd_2151407 := by
    simpa [prefixWord, tailWord_2151407, baseEnd_2151407] using wordTrace_append hprefix tailTrace_2151407
  have hstable : (prefixWord ++ tailWord_2151407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151407).length < 2 ^ (prefixWord ++ tailWord_2151407).sum := by decide
  have hdescent : baseEnd_2151407 < baseStart_2151407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151431 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 3, 3, 2]
def baseStart_2151431 : Nat := 118140960795 + 2151431 * 2 ^ 59
def prefixEnd_2151431 : Nat := 4983230072969 + 3 ^ 40 * 2151431 * 2
def baseEnd_2151431 : Nat := 1104718197983277250018255

theorem tailTrace_2151431 : CollatzResearch.WordTrace tailWord_2151431 prefixEnd_2151431 1104718197983277250018255 := by
  unfold tailWord_2151431
  simp only [CollatzResearch.WordTrace]
  refine ⟨78469135068740397006902147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52312756712493598004601431 78469135068740397006902147)
  ·
    refine ⟨117703702603110595510353221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78469135068740397006902147 117703702603110595510353221)
    ·
      refine ⟨22069444238083236658191229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117703702603110595510353221 22069444238083236658191229)
      ·
        refine ⟨8276041589281213746821711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22069444238083236658191229 8276041589281213746821711)
        ·
          refine ⟨12414062383921820620232567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8276041589281213746821711 12414062383921820620232567)
          ·
            refine ⟨18621093575882730930348851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12414062383921820620232567 18621093575882730930348851)
            ·
              refine ⟨27931640363824096395523277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18621093575882730930348851 27931640363824096395523277)
              ·
                refine ⟨10474365136434036148321229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27931640363824096395523277 10474365136434036148321229)
                ·
                  refine ⟨3927886926162763555620461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10474365136434036148321229 3927886926162763555620461)
                  ·
                    refine ⟨1472957597311036333357673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3927886926162763555620461 1472957597311036333357673)
                    ·
                      refine ⟨1104718197983277250018255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1472957597311036333357673 1104718197983277250018255)
                      ·
                        rfl

theorem cell23_2151431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_2151431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151431 prefixEnd_2151431 := by exact prefixLift 2151431
  have htrace : WordTrace (prefixWord ++ tailWord_2151431) baseStart_2151431 baseEnd_2151431 := by
    simpa [prefixWord, tailWord_2151431, baseEnd_2151431] using wordTrace_append hprefix tailTrace_2151431
  have hstable : (prefixWord ++ tailWord_2151431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151431).length < 2 ^ (prefixWord ++ tailWord_2151431).sum := by decide
  have hdescent : baseEnd_2151431 < baseStart_2151431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151442 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2151442 : Nat := 118140960795 + 2151442 * 2 ^ 59
def prefixEnd_2151442 : Nat := 4983230072969 + 3 ^ 40 * 2151442 * 2
def baseEnd_2151442 : Nat := 1104723846270476706980705

theorem tailTrace_2151442 : CollatzResearch.WordTrace tailWord_2151442 prefixEnd_2151442 1104723846270476706980705 := by
  unfold tailWord_2151442
  simp only [CollatzResearch.WordTrace]
  refine ⟨19617384067925136471388145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52313024181133697257035053 19617384067925136471388145)
  ·
    refine ⟨14713038050943852353541109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19617384067925136471388145 14713038050943852353541109)
    ·
      refine ⟨1379347317275986158144479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14713038050943852353541109 1379347317275986158144479)
      ·
        refine ⟨2069020975913979237216719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379347317275986158144479 2069020975913979237216719)
        ·
          refine ⟨3103531463870968855825079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069020975913979237216719 3103531463870968855825079)
          ·
            refine ⟨4655297195806453283737619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103531463870968855825079 4655297195806453283737619)
            ·
              refine ⟨6982945793709679925606429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4655297195806453283737619 6982945793709679925606429)
              ·
                refine ⟨2618604672641129972102411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6982945793709679925606429 2618604672641129972102411)
                ·
                  refine ⟨3927907008961694958153617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618604672641129972102411 3927907008961694958153617)
                  ·
                    refine ⟨2945930256721271218615213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3927907008961694958153617 2945930256721271218615213)
                    ·
                      refine ⟨1104723846270476706980705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2945930256721271218615213 1104723846270476706980705)
                      ·
                        rfl

theorem cell23_2151442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2151442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151442 prefixEnd_2151442 := by exact prefixLift 2151442
  have htrace : WordTrace (prefixWord ++ tailWord_2151442) baseStart_2151442 baseEnd_2151442 := by
    simpa [prefixWord, tailWord_2151442, baseEnd_2151442] using wordTrace_append hprefix tailTrace_2151442
  have hstable : (prefixWord ++ tailWord_2151442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151442).length < 2 ^ (prefixWord ++ tailWord_2151442).sum := by decide
  have hdescent : baseEnd_2151442 < baseStart_2151442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151448 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 1, 3, 2]
def baseStart_2151448 : Nat := 118140960795 + 2151448 * 2 ^ 59
def prefixEnd_2151448 : Nat := 4983230072969 + 3 ^ 40 * 2151448 * 2
def baseEnd_2151448 : Nat := 1104726927154403683505677

theorem tailTrace_2151448 : CollatzResearch.WordTrace tailWord_2151448 prefixEnd_2151448 1104726927154403683505677 := by
  unfold tailWord_2151448
  simp only [CollatzResearch.WordTrace]
  refine ⟨39234877554839404455135499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52313170073119205940180665 39234877554839404455135499)
  ·
    refine ⟨58852316332259106682703249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39234877554839404455135499 58852316332259106682703249)
    ·
      refine ⟨44139237249194330012027437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58852316332259106682703249 44139237249194330012027437)
      ·
        refine ⟨16552213968447873754510289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44139237249194330012027437 16552213968447873754510289)
        ·
          refine ⟨12414160476335905315882717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16552213968447873754510289 12414160476335905315882717)
          ·
            refine ⟨4655310178625964493456019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12414160476335905315882717 4655310178625964493456019)
            ·
              refine ⟨6982965267938946740184029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4655310178625964493456019 6982965267938946740184029)
              ·
                refine ⟨2618611975477105027569011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6982965267938946740184029 2618611975477105027569011)
                ·
                  refine ⟨3927917963215657541353517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618611975477105027569011 3927917963215657541353517)
                  ·
                    refine ⟨1472969236205871578007569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3927917963215657541353517 1472969236205871578007569)
                    ·
                      refine ⟨1104726927154403683505677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1472969236205871578007569 1104726927154403683505677)
                      ·
                        rfl

theorem cell23_2151448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_2151448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151448 prefixEnd_2151448 := by exact prefixLift 2151448
  have htrace : WordTrace (prefixWord ++ tailWord_2151448) baseStart_2151448 baseEnd_2151448 := by
    simpa [prefixWord, tailWord_2151448, baseEnd_2151448] using wordTrace_append hprefix tailTrace_2151448
  have hstable : (prefixWord ++ tailWord_2151448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151448).length < 2 ^ (prefixWord ++ tailWord_2151448).sum := by decide
  have hdescent : baseEnd_2151448 < baseStart_2151448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151474 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2151474 : Nat := 118140960795 + 2151474 * 2 ^ 59
def prefixEnd_2151474 : Nat := 4983230072969 + 3 ^ 40 * 2151474 * 2
def baseEnd_2151474 : Nat := 1104740277651420581780557

theorem tailTrace_2151474 : CollatzResearch.WordTrace tailWord_2151474 prefixEnd_2151474 1104740277651420581780557 := by
  unfold tailWord_2151474
  simp only [CollatzResearch.WordTrace]
  refine ⟨19617675851896153837679369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52313802271723076900478317 19617675851896153837679369)
  ·
    refine ⟨14713256888922115378259527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19617675851896153837679369 14713256888922115378259527)
    ·
      refine ⟨22069885333383173067389291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14713256888922115378259527 22069885333383173067389291)
      ·
        refine ⟨33104828000074759601083937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22069885333383173067389291 33104828000074759601083937)
        ·
          refine ⟨24828621000056069700812953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33104828000074759601083937 24828621000056069700812953)
          ·
            refine ⟨18621465750042052275609715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24828621000056069700812953 18621465750042052275609715)
            ·
              refine ⟨27932198625063078413414573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18621465750042052275609715 27932198625063078413414573)
              ·
                refine ⟨10474574484398654405030465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27932198625063078413414573 10474574484398654405030465)
                ·
                  refine ⟨7855930863298990803772849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10474574484398654405030465 7855930863298990803772849)
                  ·
                    refine ⟨5891948147474243102829637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7855930863298990803772849 5891948147474243102829637)
                    ·
                      refine ⟨1104740277651420581780557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5891948147474243102829637 1104740277651420581780557)
                      ·
                        rfl

theorem cell23_2151474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2151474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151474 prefixEnd_2151474 := by exact prefixLift 2151474
  have htrace : WordTrace (prefixWord ++ tailWord_2151474) baseStart_2151474 baseEnd_2151474 := by
    simpa [prefixWord, tailWord_2151474, baseEnd_2151474] using wordTrace_append hprefix tailTrace_2151474
  have hstable : (prefixWord ++ tailWord_2151474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151474).length < 2 ^ (prefixWord ++ tailWord_2151474).sum := by decide
  have hdescent : baseEnd_2151474 < baseStart_2151474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151484 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 7]
def baseStart_2151484 : Nat := 118140960795 + 2151484 * 2 ^ 59
def prefixEnd_2151484 : Nat := 4983230072969 + 3 ^ 40 * 2151484 * 2
def baseEnd_2151484 : Nat := 122749490273107282517279

theorem tailTrace_2151484 : CollatzResearch.WordTrace tailWord_2151484 prefixEnd_2151484 122749490273107282517279 := by
  unfold tailWord_2151484
  simp only [CollatzResearch.WordTrace]
  refine ⟨39235534068774193529290753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52314045425032258039054337 39235534068774193529290753)
  ·
    refine ⟨29426650551580645146968065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39235534068774193529290753 29426650551580645146968065)
    ·
      refine ⟨22069987913685483860226049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29426650551580645146968065 22069987913685483860226049)
      ·
        refine ⟨16552490935264112895169537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22069987913685483860226049 16552490935264112895169537)
        ·
          refine ⟨12414368201448084671377153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16552490935264112895169537 12414368201448084671377153)
          ·
            refine ⟨9310776151086063503532865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12414368201448084671377153 9310776151086063503532865)
            ·
              refine ⟨6983082113314547627649649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9310776151086063503532865 6983082113314547627649649)
              ·
                refine ⟨5237311584985910720737237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6983082113314547627649649 5237311584985910720737237)
                ·
                  refine ⟨122749490273107282517279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5237311584985910720737237 122749490273107282517279)
                  ·
                    rfl

theorem cell23_2151484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_2151484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151484 prefixEnd_2151484 := by exact prefixLift 2151484
  have htrace : WordTrace (prefixWord ++ tailWord_2151484) baseStart_2151484 baseEnd_2151484 := by
    simpa [prefixWord, tailWord_2151484, baseEnd_2151484] using wordTrace_append hprefix tailTrace_2151484
  have hstable : (prefixWord ++ tailWord_2151484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151484).length < 2 ^ (prefixWord ++ tailWord_2151484).sum := by decide
  have hdescent : baseEnd_2151484 < baseStart_2151484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151571 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 3]
def baseStart_2151571 : Nat := 118140960795 + 2151571 * 2 ^ 59
def prefixEnd_2151571 : Nat := 4983230072969 + 3 ^ 40 * 2151571 * 2
def baseEnd_2151571 : Nat := 1104790085274906702267611

theorem tailTrace_2151571 : CollatzResearch.WordTrace tailWord_2151571 prefixEnd_2151571 1104790085274906702267611 := by
  unfold tailWord_2151571
  simp only [CollatzResearch.WordTrace]
  refine ⟨78474241288233200916998567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52316160858822133944665711 78474241288233200916998567)
  ·
    refine ⟨117711361932349801375497851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78474241288233200916998567 117711361932349801375497851)
    ·
      refine ⟨176567042898524702063246777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117711361932349801375497851 176567042898524702063246777)
      ·
        refine ⟨132425282173893526547435083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176567042898524702063246777 132425282173893526547435083)
        ·
          refine ⟨198637923260840289821152625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132425282173893526547435083 198637923260840289821152625)
          ·
            refine ⟨148978442445630217365864469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198637923260840289821152625 148978442445630217365864469)
            ·
              refine ⟨6983364489638916439024897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 148978442445630217365864469 6983364489638916439024897)
              ·
                refine ⟨5237523367229187329268673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6983364489638916439024897 5237523367229187329268673)
                ·
                  refine ⟨3928142525421890496951505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5237523367229187329268673 3928142525421890496951505)
                  ·
                    refine ⟨2946106894066417872713629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3928142525421890496951505 2946106894066417872713629)
                    ·
                      refine ⟨1104790085274906702267611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2946106894066417872713629 1104790085274906702267611)
                      ·
                        rfl

theorem cell23_2151571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 3].length) (baseStart_2151571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151571 prefixEnd_2151571 := by exact prefixLift 2151571
  have htrace : WordTrace (prefixWord ++ tailWord_2151571) baseStart_2151571 baseEnd_2151571 := by
    simpa [prefixWord, tailWord_2151571, baseEnd_2151571] using wordTrace_append hprefix tailTrace_2151571
  have hstable : (prefixWord ++ tailWord_2151571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151571).length < 2 ^ (prefixWord ++ tailWord_2151571).sum := by decide
  have hdescent : baseEnd_2151571 < baseStart_2151571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151655 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 1, 5]
def baseStart_2151655 : Nat := 118140960795 + 2151655 * 2 ^ 59
def prefixEnd_2151655 : Nat := 4983230072969 + 3 ^ 40 * 2151655 * 2
def baseEnd_2151655 : Nat := 368277739216628124539075

theorem tailTrace_2151655 : CollatzResearch.WordTrace tailWord_2151655 prefixEnd_2151655 368277739216628124539075 := by
  unfold tailWord_2151655
  simp only [CollatzResearch.WordTrace]
  refine ⟨78477305019928883263056419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52318203346619255508704279 78477305019928883263056419)
  ·
    refine ⟨117715957529893324894584629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78477305019928883263056419 117715957529893324894584629)
    ·
      refine ⟨11035871018427499208867309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117715957529893324894584629 11035871018427499208867309)
      ·
        refine ⟨4138451631910312203325241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11035871018427499208867309 4138451631910312203325241)
        ·
          refine ⟨3103838723932734152493931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4138451631910312203325241 3103838723932734152493931)
          ·
            refine ⟨4655758085899101228740897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103838723932734152493931 4655758085899101228740897)
            ·
              refine ⟨3491818564424325921555673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4655758085899101228740897 3491818564424325921555673)
              ·
                refine ⟨2618863923318244441166755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3491818564424325921555673 2618863923318244441166755)
                ·
                  refine ⟨3928295884977366661750133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618863923318244441166755 3928295884977366661750133)
                  ·
                    refine ⟨368277739216628124539075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3928295884977366661750133 368277739216628124539075)
                    ·
                      rfl

theorem cell23_2151655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_2151655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151655 prefixEnd_2151655 := by exact prefixLift 2151655
  have htrace : WordTrace (prefixWord ++ tailWord_2151655) baseStart_2151655 baseEnd_2151655 := by
    simpa [prefixWord, tailWord_2151655, baseEnd_2151655] using wordTrace_append hprefix tailTrace_2151655
  have hstable : (prefixWord ++ tailWord_2151655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151655).length < 2 ^ (prefixWord ++ tailWord_2151655).sum := by decide
  have hdescent : baseEnd_2151655 < baseStart_2151655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151658 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_2151658 : Nat := 118140960795 + 2151658 * 2 ^ 59
def prefixEnd_2151658 : Nat := 4983230072969 + 3 ^ 40 * 2151658 * 2
def baseEnd_2151658 : Nat := 1104834758091847861879711

theorem tailTrace_2151658 : CollatzResearch.WordTrace tailWord_2151658 prefixEnd_2151658 1104834758091847861879711 := by
  unfold tailWord_2151658
  simp only [CollatzResearch.WordTrace]
  refine ⟨19619353609729503693853907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52318276292612009850277085 19619353609729503693853907)
  ·
    refine ⟨29429030414594255540780861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19619353609729503693853907 29429030414594255540780861)
    ·
      refine ⟨11035886405472845827792823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29429030414594255540780861 11035886405472845827792823)
      ·
        refine ⟨16553829608209268741689235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11035886405472845827792823 16553829608209268741689235)
        ·
          refine ⟨24830744412313903112533853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16553829608209268741689235 24830744412313903112533853)
          ·
            refine ⟨9311529154617713667200195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24830744412313903112533853 9311529154617713667200195)
            ·
              refine ⟨13967293731926570500800293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9311529154617713667200195 13967293731926570500800293)
              ·
                refine ⟨2618867574736231968900055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13967293731926570500800293 2618867574736231968900055)
                ·
                  refine ⟨3928301362104347953350083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618867574736231968900055 3928301362104347953350083)
                  ·
                    refine ⟨5892452043156521930025125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3928301362104347953350083 5892452043156521930025125)
                    ·
                      refine ⟨1104834758091847861879711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5892452043156521930025125 1104834758091847861879711)
                      ·
                        rfl

theorem cell23_2151658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_2151658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151658 prefixEnd_2151658 := by exact prefixLift 2151658
  have htrace : WordTrace (prefixWord ++ tailWord_2151658) baseStart_2151658 baseEnd_2151658 := by
    simpa [prefixWord, tailWord_2151658, baseEnd_2151658] using wordTrace_append hprefix tailTrace_2151658
  have hstable : (prefixWord ++ tailWord_2151658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151658).length < 2 ^ (prefixWord ++ tailWord_2151658).sum := by decide
  have hdescent : baseEnd_2151658 < baseStart_2151658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151678 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2151678 : Nat := 118140960795 + 2151678 * 2 ^ 59
def prefixEnd_2151678 : Nat := 4983230072969 + 3 ^ 40 * 2151678 * 2
def baseEnd_2151678 : Nat := 1104845027704937783629619

theorem tailTrace_2151678 : CollatzResearch.WordTrace tailWord_2151678 prefixEnd_2151678 1104845027704937783629619 := by
  unfold tailWord_2151678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9809767987355694773892961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52318762599230372127429125 9809767987355694773892961)
  ·
    refine ⟨7357325990516771080419721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9809767987355694773892961 7357325990516771080419721)
    ·
      refine ⟨5517994492887578310314791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7357325990516771080419721 5517994492887578310314791)
      ·
        refine ⟨8276991739331367465472187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5517994492887578310314791 8276991739331367465472187)
        ·
          refine ⟨12415487608997051198208281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8276991739331367465472187 12415487608997051198208281)
          ·
            refine ⟨9311615706747788398656211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12415487608997051198208281 9311615706747788398656211)
            ·
              refine ⟨13967423560121682597984317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9311615706747788398656211 13967423560121682597984317)
              ·
                refine ⟨5237783835045630974244119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13967423560121682597984317 5237783835045630974244119)
                ·
                  refine ⟨7856675752568446461366179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5237783835045630974244119 7856675752568446461366179)
                  ·
                    refine ⟨11785013628852669692049269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7856675752568446461366179 11785013628852669692049269)
                    ·
                      refine ⟨1104845027704937783629619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11785013628852669692049269 1104845027704937783629619)
                      ·
                        rfl

theorem cell23_2151678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2151678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151678 prefixEnd_2151678 := by exact prefixLift 2151678
  have htrace : WordTrace (prefixWord ++ tailWord_2151678) baseStart_2151678 baseEnd_2151678 := by
    simpa [prefixWord, tailWord_2151678, baseEnd_2151678] using wordTrace_append hprefix tailTrace_2151678
  have hstable : (prefixWord ++ tailWord_2151678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151678).length < 2 ^ (prefixWord ++ tailWord_2151678).sum := by decide
  have hdescent : baseEnd_2151678 < baseStart_2151678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151681 : List Nat := [1, 2, 4, 1, 1, 5, 9]
def baseStart_2151681 : Nat := 118140960795 + 2151681 * 2 ^ 59
def prefixEnd_2151681 : Nat := 4983230072969 + 3 ^ 40 * 2151681 * 2
def baseEnd_2151681 : Nat := 13640081088233349035705

theorem tailTrace_2151681 : CollatzResearch.WordTrace tailWord_2151681 prefixEnd_2151681 13640081088233349035705 := by
  unfold tailWord_2151681
  simp only [CollatzResearch.WordTrace]
  refine ⟨78478253317834689703502897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52318835545223126469001931 78478253317834689703502897)
  ·
    refine ⟨58858689988376017277627173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78478253317834689703502897 58858689988376017277627173)
    ·
      refine ⟨11036004372820503239555095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58858689988376017277627173 11036004372820503239555095)
      ·
        refine ⟨16554006559230754859332643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11036004372820503239555095 16554006559230754859332643)
        ·
          refine ⟨24831009838846132288998965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16554006559230754859332643 24831009838846132288998965)
          ·
            refine ⟨2327907172391824902093653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24831009838846132288998965 2327907172391824902093653)
            ·
              refine ⟨13640081088233349035705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2327907172391824902093653 13640081088233349035705)
              ·
                rfl

theorem cell23_2151681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 9].length) (baseStart_2151681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151681 prefixEnd_2151681 := by exact prefixLift 2151681
  have htrace : WordTrace (prefixWord ++ tailWord_2151681) baseStart_2151681 baseEnd_2151681 := by
    simpa [prefixWord, tailWord_2151681, baseEnd_2151681] using wordTrace_append hprefix tailTrace_2151681
  have hstable : (prefixWord ++ tailWord_2151681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151681).length < 2 ^ (prefixWord ++ tailWord_2151681).sum := by decide
  have hdescent : baseEnd_2151681 < baseStart_2151681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151692 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 3, 2, 2]
def baseStart_2151692 : Nat := 118140960795 + 2151692 * 2 ^ 59
def prefixEnd_2151692 : Nat := 4983230072969 + 3 ^ 40 * 2151692 * 2
def baseEnd_2151692 : Nat := 1104852216434100728854555

theorem tailTrace_2151692 : CollatzResearch.WordTrace tailWord_2151692 prefixEnd_2151692 1104852216434100728854555 := by
  unfold tailWord_2151692
  simp only [CollatzResearch.WordTrace]
  refine ⟨39239327260397419291076665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52319103013863225721435553 39239327260397419291076665)
  ·
    refine ⟨29429495445298064468307499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39239327260397419291076665 29429495445298064468307499)
    ·
      refine ⟨44144243167947096702461249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29429495445298064468307499 44144243167947096702461249)
      ·
        refine ⟨33108182375960322526845937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44144243167947096702461249 33108182375960322526845937)
        ·
          refine ⟨24831136781970241895134453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33108182375960322526845937 24831136781970241895134453)
          ·
            refine ⟨2327919073309710177668855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24831136781970241895134453 2327919073309710177668855)
            ·
              refine ⟨3491878609964565266503283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327919073309710177668855 3491878609964565266503283)
              ·
                refine ⟨5237817914946847899754925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3491878609964565266503283 5237817914946847899754925)
                ·
                  refine ⟨1964181718105067962408097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5237817914946847899754925 1964181718105067962408097)
                  ·
                    refine ⟨1473136288578800971806073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1964181718105067962408097 1473136288578800971806073)
                    ·
                      refine ⟨1104852216434100728854555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473136288578800971806073 1104852216434100728854555)
                      ·
                        rfl

theorem cell23_2151692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_2151692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151692 prefixEnd_2151692 := by exact prefixLift 2151692
  have htrace : WordTrace (prefixWord ++ tailWord_2151692) baseStart_2151692 baseEnd_2151692 := by
    simpa [prefixWord, tailWord_2151692, baseEnd_2151692] using wordTrace_append hprefix tailTrace_2151692
  have hstable : (prefixWord ++ tailWord_2151692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151692).length < 2 ^ (prefixWord ++ tailWord_2151692).sum := by decide
  have hdescent : baseEnd_2151692 < baseStart_2151692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151712 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2151712 : Nat := 118140960795 + 2151712 * 2 ^ 59
def prefixEnd_2151712 : Nat := 4983230072969 + 3 ^ 40 * 2151712 * 2
def baseEnd_2151712 : Nat := 1104862486047190650604463

theorem tailTrace_2151712 : CollatzResearch.WordTrace tailWord_2151712 prefixEnd_2151712 1104862486047190650604463 := by
  unfold tailWord_2151712
  simp only [CollatzResearch.WordTrace]
  refine ⟨39239691990361190998940695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52319589320481587998587593 39239691990361190998940695)
  ·
    refine ⟨58859537985541786498411043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39239691990361190998940695 58859537985541786498411043)
    ·
      refine ⟨88289306978312679747616565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58859537985541786498411043 88289306978312679747616565)
      ·
        refine ⟨8277122529216813726339053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88289306978312679747616565 8277122529216813726339053)
        ·
          refine ⟨3103920948456305147377145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8277122529216813726339053 3103920948456305147377145)
          ·
            refine ⟨2327940711342228860532859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3103920948456305147377145 2327940711342228860532859)
            ·
              refine ⟨3491911067013343290799289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327940711342228860532859 3491911067013343290799289)
              ·
                refine ⟨2618933300260007468099467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3491911067013343290799289 2618933300260007468099467)
                ·
                  refine ⟨3928399950390011202149201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618933300260007468099467 3928399950390011202149201)
                  ·
                    refine ⟨2946299962792508401611901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3928399950390011202149201 2946299962792508401611901)
                    ·
                      refine ⟨1104862486047190650604463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2946299962792508401611901 1104862486047190650604463)
                      ·
                        rfl

theorem cell23_2151712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2151712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151712 prefixEnd_2151712 := by exact prefixLift 2151712
  have htrace : WordTrace (prefixWord ++ tailWord_2151712) baseStart_2151712 baseEnd_2151712 := by
    simpa [prefixWord, tailWord_2151712, baseEnd_2151712] using wordTrace_append hprefix tailTrace_2151712
  have hstable : (prefixWord ++ tailWord_2151712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151712).length < 2 ^ (prefixWord ++ tailWord_2151712).sum := by decide
  have hdescent : baseEnd_2151712 < baseStart_2151712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151725 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2151725 : Nat := 118140960795 + 2151725 * 2 ^ 59
def prefixEnd_2151725 : Nat := 4983230072969 + 3 ^ 40 * 2151725 * 2
def baseEnd_2151725 : Nat := 1104869161295699099741903

theorem tailTrace_2151725 : CollatzResearch.WordTrace tailWord_2151725 prefixEnd_2151725 1104869161295699099741903 := by
  unfold tailWord_2151725
  simp only [CollatzResearch.WordTrace]
  refine ⟨78479858129675285218104629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52319905419783523478736419 78479858129675285218104629)
  ·
    refine ⟨7357486699657057989197309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78479858129675285218104629 7357486699657057989197309)
    ·
      refine ⟨2759057512371396745948991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7357486699657057989197309 2759057512371396745948991)
      ·
        refine ⟨4138586268557095118923487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2759057512371396745948991 4138586268557095118923487)
        ·
          refine ⟨6207879402835642678385231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4138586268557095118923487 6207879402835642678385231)
          ·
            refine ⟨9311819104253464017577847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6207879402835642678385231 9311819104253464017577847)
            ·
              refine ⟨13967728656380196026366771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9311819104253464017577847 13967728656380196026366771)
              ·
                refine ⟨20951592984570294039550157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13967728656380196026366771 20951592984570294039550157)
                ·
                  refine ⟨7856847369213860264831309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20951592984570294039550157 7856847369213860264831309)
                  ·
                    refine ⟨2946317763455197599311741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7856847369213860264831309 2946317763455197599311741)
                    ·
                      refine ⟨1104869161295699099741903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2946317763455197599311741 1104869161295699099741903)
                      ·
                        rfl

theorem cell23_2151725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2151725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151725 prefixEnd_2151725 := by exact prefixLift 2151725
  have htrace : WordTrace (prefixWord ++ tailWord_2151725) baseStart_2151725 baseEnd_2151725 := by
    simpa [prefixWord, tailWord_2151725, baseEnd_2151725] using wordTrace_append hprefix tailTrace_2151725
  have hstable : (prefixWord ++ tailWord_2151725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151725).length < 2 ^ (prefixWord ++ tailWord_2151725).sum := by decide
  have hdescent : baseEnd_2151725 < baseStart_2151725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151742 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2151742 : Nat := 118140960795 + 2151742 * 2 ^ 59
def prefixEnd_2151742 : Nat := 4983230072969 + 3 ^ 40 * 2151742 * 2
def baseEnd_2151742 : Nat := 1104877890466825533229325

theorem tailTrace_2151742 : CollatzResearch.WordTrace tailWord_2151742 prefixEnd_2151742 1104877890466825533229325 := by
  unfold tailWord_2151742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9810059771326712140184185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52320318780409131414315653 9810059771326712140184185)
  ·
    refine ⟨7357544828495034105138139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9810059771326712140184185 7357544828495034105138139)
    ·
      refine ⟨11036317242742551157707209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7357544828495034105138139 11036317242742551157707209)
      ·
        refine ⟨8277237932056913368280407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11036317242742551157707209 8277237932056913368280407)
        ·
          refine ⟨12415856898085370052420611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8277237932056913368280407 12415856898085370052420611)
          ·
            refine ⟨18623785347128055078630917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12415856898085370052420611 18623785347128055078630917)
            ·
              refine ⟨3491959752586510327243297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18623785347128055078630917 3491959752586510327243297)
              ·
                refine ⟨2618969814439882745432473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3491959752586510327243297 2618969814439882745432473)
                ·
                  refine ⟨1964227360829912059074355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2618969814439882745432473 1964227360829912059074355)
                  ·
                    refine ⟨2946341041244868088611533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1964227360829912059074355 2946341041244868088611533)
                    ·
                      refine ⟨1104877890466825533229325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2946341041244868088611533 1104877890466825533229325)
                      ·
                        rfl

theorem cell23_2151742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2151742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151742 prefixEnd_2151742 := by exact prefixLift 2151742
  have htrace : WordTrace (prefixWord ++ tailWord_2151742) baseStart_2151742 baseEnd_2151742 := by
    simpa [prefixWord, tailWord_2151742, baseEnd_2151742] using wordTrace_append hprefix tailTrace_2151742
  have hstable : (prefixWord ++ tailWord_2151742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151742).length < 2 ^ (prefixWord ++ tailWord_2151742).sum := by decide
  have hdescent : baseEnd_2151742 < baseStart_2151742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151765 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 1, 4, 2]
def baseStart_2151765 : Nat := 118140960795 + 2151765 * 2 ^ 59
def prefixEnd_2151765 : Nat := 4983230072969 + 3 ^ 40 * 2151765 * 2
def baseEnd_2151765 : Nat := 1104889700521878943241719

theorem tailTrace_2151765 : CollatzResearch.WordTrace tailWord_2151765 prefixEnd_2151765 1104889700521878943241719 := by
  unfold tailWord_2151765
  simp only [CollatzResearch.WordTrace]
  refine ⟨78481317049530372049560749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52320878033020248033040499 78481317049530372049560749)
  ·
    refine ⟨29430493893573889518585281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78481317049530372049560749 29430493893573889518585281)
    ·
      refine ⟨22072870420180417138938961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29430493893573889518585281 22072870420180417138938961)
      ·
        refine ⟨16554652815135312854204221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22072870420180417138938961 16554652815135312854204221)
        ·
          refine ⟨6207994805675742320326583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16554652815135312854204221 6207994805675742320326583)
          ·
            refine ⟨9311992208513613480489875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6207994805675742320326583 9311992208513613480489875)
            ·
              refine ⟨13967988312770420220734813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9311992208513613480489875 13967988312770420220734813)
              ·
                refine ⟨5237995617288907582775555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13967988312770420220734813 5237995617288907582775555)
                ·
                  refine ⟨7856993425933361374163333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5237995617288907582775555 7856993425933361374163333)
                  ·
                    refine ⟨1473186267362505257655625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7856993425933361374163333 1473186267362505257655625)
                    ·
                      refine ⟨1104889700521878943241719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473186267362505257655625 1104889700521878943241719)
                      ·
                        rfl

theorem cell23_2151765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_2151765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151765 prefixEnd_2151765 := by exact prefixLift 2151765
  have htrace : WordTrace (prefixWord ++ tailWord_2151765) baseStart_2151765 baseEnd_2151765 := by
    simpa [prefixWord, tailWord_2151765, baseEnd_2151765] using wordTrace_append hprefix tailTrace_2151765
  have hstable : (prefixWord ++ tailWord_2151765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151765).length < 2 ^ (prefixWord ++ tailWord_2151765).sum := by decide
  have hdescent : baseEnd_2151765 < baseStart_2151765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151778 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2151778 : Nat := 118140960795 + 2151778 * 2 ^ 59
def prefixEnd_2151778 : Nat := 4983230072969 + 3 ^ 40 * 2151778 * 2
def baseEnd_2151778 : Nat := 1104896375770387392379159

theorem tailTrace_2151778 : CollatzResearch.WordTrace tailWord_2151778 prefixEnd_2151778 1104896375770387392379159 := by
  unfold tailWord_2151778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19620447799620818817445997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52321194132322183513189325 19620447799620818817445997)
  ·
    refine ⟨7357667924857807056542249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19620447799620818817445997 7357667924857807056542249)
    ·
      refine ⟨5518250943643355292406687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7357667924857807056542249 5518250943643355292406687)
      ·
        refine ⟨8277376415465032938610031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5518250943643355292406687 8277376415465032938610031)
        ·
          refine ⟨12416064623197549407915047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8277376415465032938610031 12416064623197549407915047)
          ·
            refine ⟨18624096934796324111872571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12416064623197549407915047 18624096934796324111872571)
            ·
              refine ⟨27936145402194486167808857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18624096934796324111872571 27936145402194486167808857)
              ·
                refine ⟨20952109051645864625856643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27936145402194486167808857 20952109051645864625856643)
                ·
                  refine ⟨31428163577468796938784965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20952109051645864625856643 31428163577468796938784965)
                  ·
                    refine ⟨5892780670775399426022181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31428163577468796938784965 5892780670775399426022181)
                    ·
                      refine ⟨1104896375770387392379159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5892780670775399426022181 1104896375770387392379159)
                      ·
                        rfl

theorem cell23_2151778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2151778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151778 prefixEnd_2151778 := by exact prefixLift 2151778
  have htrace : WordTrace (prefixWord ++ tailWord_2151778) baseStart_2151778 baseEnd_2151778 := by
    simpa [prefixWord, tailWord_2151778, baseEnd_2151778] using wordTrace_append hprefix tailTrace_2151778
  have hstable : (prefixWord ++ tailWord_2151778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151778).length < 2 ^ (prefixWord ++ tailWord_2151778).sum := by decide
  have hdescent : baseEnd_2151778 < baseStart_2151778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151786 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_2151786 : Nat := 118140960795 + 2151786 * 2 ^ 59
def prefixEnd_2151786 : Nat := 4983230072969 + 3 ^ 40 * 2151786 * 2
def baseEnd_2151786 : Nat := 1104900483615623361079123

theorem tailTrace_2151786 : CollatzResearch.WordTrace tailWord_2151786 prefixEnd_2151786 1104900483615623361079123 := by
  unfold tailWord_2151786
  simp only [CollatzResearch.WordTrace]
  refine ⟨19620520745613573159018803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52321388654969528424050141 19620520745613573159018803)
  ·
    refine ⟨29430781118420359738528205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19620520745613573159018803 29430781118420359738528205)
    ·
      refine ⟨11036542919407634901948077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29430781118420359738528205 11036542919407634901948077)
      ·
        refine ⟨4138703594777863088230529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11036542919407634901948077 4138703594777863088230529)
        ·
          refine ⟨3104027696083397316172897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4138703594777863088230529 3104027696083397316172897)
          ·
            refine ⟨2328020772062547987129673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3104027696083397316172897 2328020772062547987129673)
            ·
              refine ⟨1746015579046910990347255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2328020772062547987129673 1746015579046910990347255)
              ·
                refine ⟨2619023368570366485520883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746015579046910990347255 2619023368570366485520883)
                ·
                  refine ⟨3928535052855549728281325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619023368570366485520883 3928535052855549728281325)
                  ·
                    refine ⟨1473200644820831148105497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3928535052855549728281325 1473200644820831148105497)
                    ·
                      refine ⟨1104900483615623361079123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473200644820831148105497 1104900483615623361079123)
                      ·
                        rfl

theorem cell23_2151786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_2151786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151786 prefixEnd_2151786 := by exact prefixLift 2151786
  have htrace : WordTrace (prefixWord ++ tailWord_2151786) baseStart_2151786 baseEnd_2151786 := by
    simpa [prefixWord, tailWord_2151786, baseEnd_2151786] using wordTrace_append hprefix tailTrace_2151786
  have hstable : (prefixWord ++ tailWord_2151786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151786).length < 2 ^ (prefixWord ++ tailWord_2151786).sum := by decide
  have hdescent : baseEnd_2151786 < baseStart_2151786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151808 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 1, 7, 2]
def baseStart_2151808 : Nat := 118140960795 + 2151808 * 2 ^ 59
def prefixEnd_2151808 : Nat := 4983230072969 + 3 ^ 40 * 2151808 * 2
def baseEnd_2151808 : Nat := 1104911780190022275004021

theorem tailTrace_2151808 : CollatzResearch.WordTrace tailWord_2151808 prefixEnd_2151808 1104911780190022275004021 := by
  unfold tailWord_2151808
  simp only [CollatzResearch.WordTrace]
  refine ⟨39241442694187295196688039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52321923592249726928917385 39241442694187295196688039)
  ·
    refine ⟨58862164041280942795032059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39241442694187295196688039 58862164041280942795032059)
    ·
      refine ⟨88293246061921414192548089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58862164041280942795032059 88293246061921414192548089)
      ·
        refine ⟨66219934546441060644411067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88293246061921414192548089 66219934546441060644411067)
        ·
          refine ⟨99329901819661590966616601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66219934546441060644411067 99329901819661590966616601)
          ·
            refine ⟨74497426364746193224962451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99329901819661590966616601 74497426364746193224962451)
            ·
              refine ⟨111746139547119289837443677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74497426364746193224962451 111746139547119289837443677)
              ·
                refine ⟨41904802330169733689041379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111746139547119289837443677 41904802330169733689041379)
                ·
                  refine ⟨62857203495254600533562069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41904802330169733689041379 62857203495254600533562069)
                  ·
                    refine ⟨1473215706920029700005361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 62857203495254600533562069 1473215706920029700005361)
                    ·
                      refine ⟨1104911780190022275004021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473215706920029700005361 1104911780190022275004021)
                      ·
                        rfl

theorem cell23_2151808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_2151808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151808 prefixEnd_2151808 := by exact prefixLift 2151808
  have htrace : WordTrace (prefixWord ++ tailWord_2151808) baseStart_2151808 baseEnd_2151808 := by
    simpa [prefixWord, tailWord_2151808, baseEnd_2151808] using wordTrace_append hprefix tailTrace_2151808
  have hstable : (prefixWord ++ tailWord_2151808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151808).length < 2 ^ (prefixWord ++ tailWord_2151808).sum := by decide
  have hdescent : baseEnd_2151808 < baseStart_2151808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151831 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 1, 10]
def baseStart_2151831 : Nat := 118140960795 + 2151831 * 2 ^ 59
def prefixEnd_2151831 : Nat := 4983230072969 + 3 ^ 40 * 2151831 * 2
def baseEnd_2151831 : Nat := 368307863415025228338805

theorem tailTrace_2151831 : CollatzResearch.WordTrace tailWord_2151831 prefixEnd_2151831 368307863415025228338805 := by
  unfold tailWord_2151831
  simp only [CollatzResearch.WordTrace]
  refine ⟨78483724267291265321463347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52322482844860843547642231 78483724267291265321463347)
  ·
    refine ⟨117725586400936897982195021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78483724267291265321463347 117725586400936897982195021)
    ·
      refine ⟨44147094900351336743323133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117725586400936897982195021 44147094900351336743323133)
      ·
        refine ⟨16555160587631751278746175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44147094900351336743323133 16555160587631751278746175)
        ·
          refine ⟨24832740881447626918119263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16555160587631751278746175 24832740881447626918119263)
          ·
            refine ⟨37249111322171440377178895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24832740881447626918119263 37249111322171440377178895)
            ·
              refine ⟨55873666983257160565768343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37249111322171440377178895 55873666983257160565768343)
              ·
                refine ⟨83810500474885740848652515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55873666983257160565768343 83810500474885740848652515)
                ·
                  refine ⟨125715750712328611272978773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83810500474885740848652515 125715750712328611272978773)
                  ·
                    refine ⟨368307863415025228338805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 125715750712328611272978773 368307863415025228338805)
                    ·
                      rfl

theorem cell23_2151831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_2151831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151831 prefixEnd_2151831 := by exact prefixLift 2151831
  have htrace : WordTrace (prefixWord ++ tailWord_2151831) baseStart_2151831 baseEnd_2151831 := by
    simpa [prefixWord, tailWord_2151831, baseEnd_2151831] using wordTrace_append hprefix tailTrace_2151831
  have hstable : (prefixWord ++ tailWord_2151831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151831).length < 2 ^ (prefixWord ++ tailWord_2151831).sum := by decide
  have hdescent : baseEnd_2151831 < baseStart_2151831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151851 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 6]
def baseStart_2151851 : Nat := 118140960795 + 2151851 * 2 ^ 59
def prefixEnd_2151851 : Nat := 4983230072969 + 3 ^ 40 * 2151851 * 2
def baseEnd_2151851 : Nat := 1104933859858165606766323

theorem tailTrace_2151851 : CollatzResearch.WordTrace tailWord_2151851 prefixEnd_2151851 1104933859858165606766323 := by
  unfold tailWord_2151851
  simp only [CollatzResearch.WordTrace]
  refine ⟨78484453727218808737191407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52322969151479205824794271 78484453727218808737191407)
  ·
    refine ⟨117726680590828213105787111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78484453727218808737191407 117726680590828213105787111)
    ·
      refine ⟨176590020886242319658680667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117726680590828213105787111 176590020886242319658680667)
      ·
        refine ⟨264885031329363479488021001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176590020886242319658680667 264885031329363479488021001)
        ·
          refine ⟨198663773497022609616015751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264885031329363479488021001 198663773497022609616015751)
          ·
            refine ⟨297995660245533914424023627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198663773497022609616015751 297995660245533914424023627)
            ·
              refine ⟨446993490368300871636035441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297995660245533914424023627 446993490368300871636035441)
              ·
                refine ⟨335245117776225653727026581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446993490368300871636035441 335245117776225653727026581)
                ·
                  refine ⟨15714614895760577518454371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 335245117776225653727026581 15714614895760577518454371)
                  ·
                    refine ⟨23571922343640866277681557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15714614895760577518454371 23571922343640866277681557)
                    ·
                      refine ⟨1104933859858165606766323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23571922343640866277681557 1104933859858165606766323)
                      ·
                        rfl

theorem cell23_2151851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_2151851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151851 prefixEnd_2151851 := by exact prefixLift 2151851
  have htrace : WordTrace (prefixWord ++ tailWord_2151851) baseStart_2151851 baseEnd_2151851 := by
    simpa [prefixWord, tailWord_2151851, baseEnd_2151851] using wordTrace_append hprefix tailTrace_2151851
  have hstable : (prefixWord ++ tailWord_2151851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151851).length < 2 ^ (prefixWord ++ tailWord_2151851).sum := by decide
  have hdescent : baseEnd_2151851 < baseStart_2151851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151858 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_2151858 : Nat := 118140960795 + 2151858 * 2 ^ 59
def prefixEnd_2151858 : Nat := 4983230072969 + 3 ^ 40 * 2151858 * 2
def baseEnd_2151858 : Nat := 1104937454222747079378791

theorem tailTrace_2151858 : CollatzResearch.WordTrace tailWord_2151858 prefixEnd_2151858 1104937454222747079378791 := by
  unfold tailWord_2151858
  simp only [CollatzResearch.WordTrace]
  refine ⟨19621177259548362233174057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52323139358795632621797485 19621177259548362233174057)
  ·
    refine ⟨14715882944661271674880543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19621177259548362233174057 14715882944661271674880543)
    ·
      refine ⟨22073824416991907512320815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14715882944661271674880543 22073824416991907512320815)
      ·
        refine ⟨33110736625487861268481223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22073824416991907512320815 33110736625487861268481223)
        ·
          refine ⟨49666104938231791902721835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33110736625487861268481223 49666104938231791902721835)
          ·
            refine ⟨74499157407347687854082753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49666104938231791902721835 74499157407347687854082753)
            ·
              refine ⟨55874368055510765890562065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74499157407347687854082753 55874368055510765890562065)
              ·
                refine ⟨41905776041633074417921549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55874368055510765890562065 41905776041633074417921549)
                ·
                  refine ⟨15714666015612402906720581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41905776041633074417921549 15714666015612402906720581)
                  ·
                    refine ⟨2946499877927325545010109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15714666015612402906720581 2946499877927325545010109)
                    ·
                      refine ⟨1104937454222747079378791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2946499877927325545010109 1104937454222747079378791)
                      ·
                        rfl

theorem cell23_2151858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_2151858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151858 prefixEnd_2151858 := by exact prefixLift 2151858
  have htrace : WordTrace (prefixWord ++ tailWord_2151858) baseStart_2151858 baseEnd_2151858 := by
    simpa [prefixWord, tailWord_2151858, baseEnd_2151858] using wordTrace_append hprefix tailTrace_2151858
  have hstable : (prefixWord ++ tailWord_2151858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151858).length < 2 ^ (prefixWord ++ tailWord_2151858).sum := by decide
  have hdescent : baseEnd_2151858 < baseStart_2151858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151915 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 4, 3, 2]
def baseStart_2151915 : Nat := 118140960795 + 2151915 * 2 ^ 59
def prefixEnd_2151915 : Nat := 4983230072969 + 3 ^ 40 * 2151915 * 2
def baseEnd_2151915 : Nat := 1104966722620053356366029

theorem tailTrace_2151915 : CollatzResearch.WordTrace tailWord_2151915 prefixEnd_2151915 1104966722620053356366029 := by
  unfold tailWord_2151915
  simp only [CollatzResearch.WordTrace]
  refine ⟨78486787998986947667521199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52324525332657965111680799 78486787998986947667521199)
  ·
    refine ⟨117730181998480421501281799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78486787998986947667521199 117730181998480421501281799)
    ·
      refine ⟨176595272997720632251922699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117730181998480421501281799 176595272997720632251922699)
      ·
        refine ⟨264892909496580948377884049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176595272997720632251922699 264892909496580948377884049)
        ·
          refine ⟨198669682122435711283413037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264892909496580948377884049 198669682122435711283413037)
          ·
            refine ⟨74501130795913391731279889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198669682122435711283413037 74501130795913391731279889)
            ·
              refine ⟨55875848096935043798459917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74501130795913391731279889 55875848096935043798459917)
              ·
                refine ⟨20953443036350641424422469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55875848096935043798459917 20953443036350641424422469)
                ·
                  refine ⟨3928770569315745267079213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20953443036350641424422469 3928770569315745267079213)
                  ·
                    refine ⟨1473288963493404475154705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3928770569315745267079213 1473288963493404475154705)
                    ·
                      refine ⟨1104966722620053356366029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473288963493404475154705 1104966722620053356366029)
                      ·
                        rfl

theorem cell23_2151915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 3, 2].length) (baseStart_2151915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151915 prefixEnd_2151915 := by exact prefixLift 2151915
  have htrace : WordTrace (prefixWord ++ tailWord_2151915) baseStart_2151915 baseEnd_2151915 := by
    simpa [prefixWord, tailWord_2151915, baseEnd_2151915] using wordTrace_append hprefix tailTrace_2151915
  have hstable : (prefixWord ++ tailWord_2151915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151915).length < 2 ^ (prefixWord ++ tailWord_2151915).sum := by decide
  have hdescent : baseEnd_2151915 < baseStart_2151915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151945 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 4]
def baseStart_2151945 : Nat := 118140960795 + 2151945 * 2 ^ 59
def prefixEnd_2151945 : Nat := 4983230072969 + 3 ^ 40 * 2151945 * 2
def baseEnd_2151945 : Nat := 1104982127039688238990891

theorem tailTrace_2151945 : CollatzResearch.WordTrace tailWord_2151945 prefixEnd_2151945 1104982127039688238990891 := by
  unfold tailWord_2151945
  simp only [CollatzResearch.WordTrace]
  refine ⟨78487882188878262791113289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52325254792585508527408859 78487882188878262791113289)
  ·
    refine ⟨58865911641658697093334967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78487882188878262791113289 58865911641658697093334967)
    ·
      refine ⟨88298867462488045640002451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58865911641658697093334967 88298867462488045640002451)
      ·
        refine ⟨132448301193732068460003677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88298867462488045640002451 132448301193732068460003677)
        ·
          refine ⟨49668112947649525672501379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132448301193732068460003677 49668112947649525672501379)
          ·
            refine ⟨74502169421474288508752069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49668112947649525672501379 74502169421474288508752069)
            ·
              refine ⟨13969156766526429095391013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74502169421474288508752069 13969156766526429095391013)
              ·
                refine ⟨2619216893723705455385815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13969156766526429095391013 2619216893723705455385815)
                ·
                  refine ⟨3928825340585558183078723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619216893723705455385815 3928825340585558183078723)
                  ·
                    refine ⟨5893238010878337274618085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3928825340585558183078723 5893238010878337274618085)
                    ·
                      refine ⟨1104982127039688238990891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5893238010878337274618085 1104982127039688238990891)
                      ·
                        rfl

theorem cell23_2151945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 4].length) (baseStart_2151945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151945 prefixEnd_2151945 := by exact prefixLift 2151945
  have htrace : WordTrace (prefixWord ++ tailWord_2151945) baseStart_2151945 baseEnd_2151945 := by
    simpa [prefixWord, tailWord_2151945, baseEnd_2151945] using wordTrace_append hprefix tailTrace_2151945
  have hstable : (prefixWord ++ tailWord_2151945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151945).length < 2 ^ (prefixWord ++ tailWord_2151945).sum := by decide
  have hdescent : baseEnd_2151945 < baseStart_2151945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151962 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2]
def baseStart_2151962 : Nat := 118140960795 + 2151962 * 2 ^ 59
def prefixEnd_2151962 : Nat := 4983230072969 + 3 ^ 40 * 2151962 * 2
def baseEnd_2151962 : Nat := 1104990856210814672478313

theorem tailTrace_2151962 : CollatzResearch.WordTrace tailWord_2151962 prefixEnd_2151962 1104990856210814672478313 := by
  unfold tailWord_2151962
  simp only [CollatzResearch.WordTrace]
  refine ⟨19622125557454168673620535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52325668153211116462988093 19622125557454168673620535)
  ·
    refine ⟨29433188336181253010430803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19622125557454168673620535 29433188336181253010430803)
    ·
      refine ⟨44149782504271879515646205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29433188336181253010430803 44149782504271879515646205)
      ·
        refine ⟨16556168439101954818367327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44149782504271879515646205 16556168439101954818367327)
        ·
          refine ⟨24834252658652932227550991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16556168439101954818367327 24834252658652932227550991)
          ·
            refine ⟨37251378987979398341326487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24834252658652932227550991 37251378987979398341326487)
            ·
              refine ⟨55877068481969097511989731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37251378987979398341326487 55877068481969097511989731)
              ·
                refine ⟨83815602722953646267984597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55877068481969097511989731 83815602722953646267984597)
                ·
                  refine ⟨1964428188819226084405889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 83815602722953646267984597 1964428188819226084405889)
                  ·
                    refine ⟨1473321141614419563304417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1964428188819226084405889 1473321141614419563304417)
                    ·
                      refine ⟨1104990856210814672478313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473321141614419563304417 1104990856210814672478313)
                      ·
                        rfl

theorem cell23_2151962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_2151962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151962 prefixEnd_2151962 := by exact prefixLift 2151962
  have htrace : WordTrace (prefixWord ++ tailWord_2151962) baseStart_2151962 baseEnd_2151962 := by
    simpa [prefixWord, tailWord_2151962, baseEnd_2151962] using wordTrace_append hprefix tailTrace_2151962
  have hstable : (prefixWord ++ tailWord_2151962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151962).length < 2 ^ (prefixWord ++ tailWord_2151962).sum := by decide
  have hdescent : baseEnd_2151962 < baseStart_2151962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151965 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2151965 : Nat := 118140960795 + 2151965 * 2 ^ 59
def prefixEnd_2151965 : Nat := 4983230072969 + 3 ^ 40 * 2151965 * 2
def baseEnd_2151965 : Nat := 1104992396652778160740799

theorem tailTrace_2151965 : CollatzResearch.WordTrace tailWord_2151965 prefixEnd_2151965 1104992396652778160740799 := by
  unfold tailWord_2151965
  simp only [CollatzResearch.WordTrace]
  refine ⟨78488611648805806206841349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52325741099203870804560899 78488611648805806206841349)
  ·
    refine ⟨14716614684151088663782753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78488611648805806206841349 14716614684151088663782753)
    ·
      refine ⟨11037461013113316497837065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14716614684151088663782753 11037461013113316497837065)
      ·
        refine ⟨8278095759834987373377799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11037461013113316497837065 8278095759834987373377799)
        ·
          refine ⟨12417143639752481060066699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8278095759834987373377799 12417143639752481060066699)
          ·
            refine ⟨18625715459628721590100049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12417143639752481060066699 18625715459628721590100049)
            ·
              refine ⟨13969286594721541192575037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18625715459628721590100049 13969286594721541192575037)
              ·
                refine ⟨5238482473020577947215639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13969286594721541192575037 5238482473020577947215639)
                ·
                  refine ⟨7857723709530866920823459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5238482473020577947215639 7857723709530866920823459)
                  ·
                    refine ⟨11786585564296300381235189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7857723709530866920823459 11786585564296300381235189)
                    ·
                      refine ⟨1104992396652778160740799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11786585564296300381235189 1104992396652778160740799)
                      ·
                        rfl

theorem cell23_2151965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2151965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151965 prefixEnd_2151965 := by exact prefixLift 2151965
  have htrace : WordTrace (prefixWord ++ tailWord_2151965) baseStart_2151965 baseEnd_2151965 := by
    simpa [prefixWord, tailWord_2151965, baseEnd_2151965] using wordTrace_append hprefix tailTrace_2151965
  have hstable : (prefixWord ++ tailWord_2151965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151965).length < 2 ^ (prefixWord ++ tailWord_2151965).sum := by decide
  have hdescent : baseEnd_2151965 < baseStart_2151965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151982 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2151982 : Nat := 118140960795 + 2151982 * 2 ^ 59
def prefixEnd_2151982 : Nat := 4983230072969 + 3 ^ 40 * 2151982 * 2
def baseEnd_2151982 : Nat := 1105001125823904594228221

theorem tailTrace_2151982 : CollatzResearch.WordTrace tailWord_2151982 prefixEnd_2151982 1105001125823904594228221 := by
  unfold tailWord_2151982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9811153961218027263776275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52326154459829478740140133 9811153961218027263776275)
  ·
    refine ⟨14716730941827040895664413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9811153961218027263776275 14716730941827040895664413)
    ·
      refine ⟨5518774103185140335874155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14716730941827040895664413 5518774103185140335874155)
      ·
        refine ⟨8278161154777710503811233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5518774103185140335874155 8278161154777710503811233)
        ·
          refine ⟨6208620866083282877858425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8278161154777710503811233 6208620866083282877858425)
          ·
            refine ⟨4656465649562462158393819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6208620866083282877858425 4656465649562462158393819)
            ·
              refine ⟨6984698474343693237590729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4656465649562462158393819 6984698474343693237590729)
              ·
                refine ⟨5238523855757769928193047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6984698474343693237590729 5238523855757769928193047)
                ·
                  refine ⟨7857785783636654892289571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5238523855757769928193047 7857785783636654892289571)
                  ·
                    refine ⟨11786678675454982338434357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7857785783636654892289571 11786678675454982338434357)
                    ·
                      refine ⟨1105001125823904594228221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11786678675454982338434357 1105001125823904594228221)
                      ·
                        rfl

theorem cell23_2151982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2151982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151982 prefixEnd_2151982 := by exact prefixLift 2151982
  have htrace : WordTrace (prefixWord ++ tailWord_2151982) baseStart_2151982 baseEnd_2151982 := by
    simpa [prefixWord, tailWord_2151982, baseEnd_2151982] using wordTrace_append hprefix tailTrace_2151982
  have hstable : (prefixWord ++ tailWord_2151982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151982).length < 2 ^ (prefixWord ++ tailWord_2151982).sum := by decide
  have hdescent : baseEnd_2151982 < baseStart_2151982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151989 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 2, 4]
def baseStart_2151989 : Nat := 118140960795 + 2151989 * 2 ^ 59
def prefixEnd_2151989 : Nat := 4983230072969 + 3 ^ 40 * 2151989 * 2
def baseEnd_2151989 : Nat := 368334906729495355613563

theorem tailTrace_2151989 : CollatzResearch.WordTrace tailWord_2151989 prefixEnd_2151989 368334906729495355613563 := by
  unfold tailWord_2151989
  simp only [CollatzResearch.WordTrace]
  refine ⟨78489487000718858305715021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52326324667145905537143347 78489487000718858305715021)
  ·
    refine ⟨29433557625269571864643133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78489487000718858305715021 29433557625269571864643133)
    ·
      refine ⟨11037584109476089449241175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29433557625269571864643133 11037584109476089449241175)
      ·
        refine ⟨16556376164214134173861763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11037584109476089449241175 16556376164214134173861763)
        ·
          refine ⟨24834564246321201260792645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16556376164214134173861763 24834564246321201260792645)
          ·
            refine ⟨4656480796185225236398621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24834564246321201260792645 4656480796185225236398621)
            ·
              refine ⟨1746180298569459463649483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4656480796185225236398621 1746180298569459463649483)
              ·
                refine ⟨2619270447854189195474225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746180298569459463649483 2619270447854189195474225)
                ·
                  refine ⟨1964452835890641896605669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2619270447854189195474225 1964452835890641896605669)
                  ·
                    refine ⟨368334906729495355613563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964452835890641896605669 368334906729495355613563)
                    ·
                      rfl

theorem cell23_2151989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_2151989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151989 prefixEnd_2151989 := by exact prefixLift 2151989
  have htrace : WordTrace (prefixWord ++ tailWord_2151989) baseStart_2151989 baseEnd_2151989 := by
    simpa [prefixWord, tailWord_2151989, baseEnd_2151989] using wordTrace_append hprefix tailTrace_2151989
  have hstable : (prefixWord ++ tailWord_2151989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151989).length < 2 ^ (prefixWord ++ tailWord_2151989).sum := by decide
  have hdescent : baseEnd_2151989 < baseStart_2151989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2151992 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 1, 2, 4]
def baseStart_2151992 : Nat := 118140960795 + 2151992 * 2 ^ 59
def prefixEnd_2151992 : Nat := 4983230072969 + 3 ^ 40 * 2151992 * 2
def baseEnd_2151992 : Nat := 1105006260630449555103175

theorem tailTrace_2151992 : CollatzResearch.WordTrace tailWord_2151992 prefixEnd_2151992 1105006260630449555103175 := by
  unfold tailWord_2151992
  simp only [CollatzResearch.WordTrace]
  refine ⟨39244798209853994909037115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52326397613138659878716153 39244798209853994909037115)
  ·
    refine ⟨58867197314780992363555673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39244798209853994909037115 58867197314780992363555673)
    ·
      refine ⟨44150397986085744272666755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58867197314780992363555673 44150397986085744272666755)
      ·
        refine ⟨66225596979128616409000133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44150397986085744272666755 66225596979128616409000133)
        ·
          refine ⟨12417299433586615576687525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66225596979128616409000133 12417299433586615576687525)
          ·
            refine ⟨2328243643797490420628911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12417299433586615576687525 2328243643797490420628911)
            ·
              refine ⟨3492365465696235630943367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328243643797490420628911 3492365465696235630943367)
              ·
                refine ⟨5238548198544353446415051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3492365465696235630943367 5238548198544353446415051)
                ·
                  refine ⟨7857822297816530169622577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5238548198544353446415051 7857822297816530169622577)
                  ·
                    refine ⟨5893366723362397627216933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7857822297816530169622577 5893366723362397627216933)
                    ·
                      refine ⟨1105006260630449555103175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5893366723362397627216933 1105006260630449555103175)
                      ·
                        rfl

theorem cell23_2151992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_2151992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2151992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2151992 prefixEnd_2151992 := by exact prefixLift 2151992
  have htrace : WordTrace (prefixWord ++ tailWord_2151992) baseStart_2151992 baseEnd_2151992 := by
    simpa [prefixWord, tailWord_2151992, baseEnd_2151992] using wordTrace_append hprefix tailTrace_2151992
  have hstable : (prefixWord ++ tailWord_2151992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2151992).length < 2 ^ (prefixWord ++ tailWord_2151992).sum := by decide
  have hdescent : baseEnd_2151992 < baseStart_2151992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2151992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152012 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 4, 1, 3]
def baseStart_2152012 : Nat := 118140960795 + 2152012 * 2 ^ 59
def prefixEnd_2152012 : Nat := 4983230072969 + 3 ^ 40 * 2152012 * 2
def baseEnd_2152012 : Nat := 1105016530243539476853083

theorem tailTrace_2152012 : CollatzResearch.WordTrace tailWord_2152012 prefixEnd_2152012 1105016530243539476853083 := by
  unfold tailWord_2152012
  simp only [CollatzResearch.WordTrace]
  refine ⟨39245162939817766616901145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52326883919757022155868193 39245162939817766616901145)
  ·
    refine ⟨29433872204863324962675859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39245162939817766616901145 29433872204863324962675859)
    ·
      refine ⟨44150808307294987444013789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29433872204863324962675859 44150808307294987444013789)
      ·
        refine ⟨16556553115235620291505171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44150808307294987444013789 16556553115235620291505171)
        ·
          refine ⟨24834829672853430437257757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16556553115235620291505171 24834829672853430437257757)
          ·
            refine ⟨9313061127320036413971659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24834829672853430437257757 9313061127320036413971659)
            ·
              refine ⟨13969591690980054620957489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9313061127320036413971659 13969591690980054620957489)
              ·
                refine ⟨10477193768235040965718117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13969591690980054620957489 10477193768235040965718117)
                ·
                  refine ⟨1964473831544070181072147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10477193768235040965718117 1964473831544070181072147)
                  ·
                    refine ⟨2946710747316105271608221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1964473831544070181072147 2946710747316105271608221)
                    ·
                      refine ⟨1105016530243539476853083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2946710747316105271608221 1105016530243539476853083)
                      ·
                        rfl

theorem cell23_2152012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_2152012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152012 prefixEnd_2152012 := by exact prefixLift 2152012
  have htrace : WordTrace (prefixWord ++ tailWord_2152012) baseStart_2152012 baseEnd_2152012 := by
    simpa [prefixWord, tailWord_2152012, baseEnd_2152012] using wordTrace_append hprefix tailTrace_2152012
  have hstable : (prefixWord ++ tailWord_2152012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152012).length < 2 ^ (prefixWord ++ tailWord_2152012).sum := by decide
  have hdescent : baseEnd_2152012 < baseStart_2152012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152046 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2152046 : Nat := 118140960795 + 2152046 * 2 ^ 59
def prefixEnd_2152046 : Nat := 4983230072969 + 3 ^ 40 * 2152046 * 2
def baseEnd_2152046 : Nat := 1105033988585792343827927

theorem tailTrace_2152046 : CollatzResearch.WordTrace tailWord_2152046 prefixEnd_2152046 1105033988585792343827927 := by
  unfold tailWord_2152046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9811445745189044630067499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52327710641008238027026661 9811445745189044630067499)
  ·
    refine ⟨14717168617783566945101249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9811445745189044630067499 14717168617783566945101249)
    ·
      refine ⟨11037876463337675208825937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14717168617783566945101249 11037876463337675208825937)
      ·
        refine ⟨8278407347503256406619453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11037876463337675208825937 8278407347503256406619453)
        ·
          refine ⟨3104402755313721152482295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8278407347503256406619453 3104402755313721152482295)
          ·
            refine ⟨4656604132970581728723443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104402755313721152482295 4656604132970581728723443)
            ·
              refine ⟨6984906199455872593085165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4656604132970581728723443 6984906199455872593085165)
              ·
                refine ⟨2619339824795952222406937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6984906199455872593085165 2619339824795952222406937)
                ·
                  refine ⟨1964504868596964166805203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2619339824795952222406937 1964504868596964166805203)
                  ·
                    refine ⟨2946757302895446250207805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1964504868596964166805203 2946757302895446250207805)
                    ·
                      refine ⟨1105033988585792343827927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2946757302895446250207805 1105033988585792343827927)
                      ·
                        rfl

theorem cell23_2152046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2152046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152046 prefixEnd_2152046 := by exact prefixLift 2152046
  have htrace : WordTrace (prefixWord ++ tailWord_2152046) baseStart_2152046 baseEnd_2152046 := by
    simpa [prefixWord, tailWord_2152046, baseEnd_2152046] using wordTrace_append hprefix tailTrace_2152046
  have hstable : (prefixWord ++ tailWord_2152046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152046).length < 2 ^ (prefixWord ++ tailWord_2152046).sum := by decide
  have hdescent : baseEnd_2152046 < baseStart_2152046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152085 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_2152085 : Nat := 118140960795 + 2152085 * 2 ^ 59
def prefixEnd_2152085 : Nat := 4983230072969 + 3 ^ 40 * 2152085 * 2
def baseEnd_2152085 : Nat := 1105054014331317691240247

theorem tailTrace_2152085 : CollatzResearch.WordTrace tailWord_2152085 prefixEnd_2152085 1105054014331317691240247 := by
  unfold tailWord_2152085
  simp only [CollatzResearch.WordTrace]
  refine ⟨78492988408371066701209709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52328658938914044467473139 78492988408371066701209709)
  ·
    refine ⟨29434870653139150012953641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78492988408371066701209709 29434870653139150012953641)
    ·
      refine ⟨22076152989854362509715231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29434870653139150012953641 22076152989854362509715231)
      ·
        refine ⟨33114229484781543764572847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22076152989854362509715231 33114229484781543764572847)
        ·
          refine ⟨49671344227172315646859271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33114229484781543764572847 49671344227172315646859271)
          ·
            refine ⟨74507016340758473470288907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49671344227172315646859271 74507016340758473470288907)
            ·
              refine ⟨111760524511137710205433361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74507016340758473470288907 111760524511137710205433361)
              ·
                refine ⟨83820393383353282654075021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111760524511137710205433361 83820393383353282654075021)
                ·
                  refine ⟨31432647518757480995278133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83820393383353282654075021 31432647518757480995278133)
                  ·
                    refine ⟨2946810704883513843307325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31432647518757480995278133 2946810704883513843307325)
                    ·
                      refine ⟨1105054014331317691240247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2946810704883513843307325 1105054014331317691240247)
                      ·
                        rfl

theorem cell23_2152085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_2152085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152085 prefixEnd_2152085 := by exact prefixLift 2152085
  have htrace : WordTrace (prefixWord ++ tailWord_2152085) baseStart_2152085 baseEnd_2152085 := by
    simpa [prefixWord, tailWord_2152085, baseEnd_2152085] using wordTrace_append hprefix tailTrace_2152085
  have hstable : (prefixWord ++ tailWord_2152085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152085).length < 2 ^ (prefixWord ++ tailWord_2152085).sum := by decide
  have hdescent : baseEnd_2152085 < baseStart_2152085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152122 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_2152122 : Nat := 118140960795 + 2152122 * 2 ^ 59
def prefixEnd_2152122 : Nat := 4983230072969 + 3 ^ 40 * 2152122 * 2
def baseEnd_2152122 : Nat := 368357671038511348825859

theorem tailTrace_2152122 : CollatzResearch.WordTrace tailWord_2152122 prefixEnd_2152122 368357671038511348825859 := by
  unfold tailWord_2152122
  simp only [CollatzResearch.WordTrace]
  refine ⟨19623584477309255505076655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52329558606158014680204413 19623584477309255505076655)
  ·
    refine ⟨29435376715963883257614983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19623584477309255505076655 29435376715963883257614983)
    ·
      refine ⟨44153065073945824886422475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29435376715963883257614983 44153065073945824886422475)
      ·
        refine ⟨66229597610918737329633713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44153065073945824886422475 66229597610918737329633713)
        ·
          refine ⟨49672198208189052997225285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66229597610918737329633713 49672198208189052997225285)
          ·
            refine ⟨9313537164035447436979741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49672198208189052997225285 9313537164035447436979741)
            ·
              refine ⟨3492576436513292788867403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9313537164035447436979741 3492576436513292788867403)
              ·
                refine ⟨5238864654769939183301105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3492576436513292788867403 5238864654769939183301105)
                ·
                  refine ⟨3929148491077454387475829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5238864654769939183301105 3929148491077454387475829)
                  ·
                    refine ⟨368357671038511348825859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3929148491077454387475829 368357671038511348825859)
                    ·
                      rfl

theorem cell23_2152122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_2152122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152122 prefixEnd_2152122 := by exact prefixLift 2152122
  have htrace : WordTrace (prefixWord ++ tailWord_2152122) baseStart_2152122 baseEnd_2152122 := by
    simpa [prefixWord, tailWord_2152122, baseEnd_2152122] using wordTrace_append hprefix tailTrace_2152122
  have hstable : (prefixWord ++ tailWord_2152122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152122).length < 2 ^ (prefixWord ++ tailWord_2152122).sum := by decide
  have hdescent : baseEnd_2152122 < baseStart_2152122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152142 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_2152142 : Nat := 118140960795 + 2152142 * 2 ^ 59
def prefixEnd_2152142 : Nat := 4983230072969 + 3 ^ 40 * 2152142 * 2
def baseEnd_2152142 : Nat := 1105083282728623968227485

theorem tailTrace_2152142 : CollatzResearch.WordTrace tailWord_2152142 prefixEnd_2152142 1105083282728623968227485 := by
  unfold tailWord_2152142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9811883421145570679504335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52330044912776376957356453 9811883421145570679504335)
  ·
    refine ⟨14717825131718356019256503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9811883421145570679504335 14717825131718356019256503)
    ·
      refine ⟨22076737697577534028884755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14717825131718356019256503 22076737697577534028884755)
      ·
        refine ⟨33115106546366301043327133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22076737697577534028884755 33115106546366301043327133)
        ·
          refine ⟨12418164954887362891247675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33115106546366301043327133 12418164954887362891247675)
          ·
            refine ⟨18627247432331044336871513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12418164954887362891247675 18627247432331044336871513)
            ·
              refine ⟨13970435574248283252653635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18627247432331044336871513 13970435574248283252653635)
              ·
                refine ⟨20955653361372424878980453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13970435574248283252653635 20955653361372424878980453)
                ·
                  refine ⟨3929185005257329664808835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20955653361372424878980453 3929185005257329664808835)
                  ·
                    refine ⟨5893777507885994497213253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3929185005257329664808835 5893777507885994497213253)
                    ·
                      refine ⟨1105083282728623968227485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5893777507885994497213253 1105083282728623968227485)
                      ·
                        rfl

theorem cell23_2152142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_2152142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152142 prefixEnd_2152142 := by exact prefixLift 2152142
  have htrace : WordTrace (prefixWord ++ tailWord_2152142) baseStart_2152142 baseEnd_2152142 := by
    simpa [prefixWord, tailWord_2152142, baseEnd_2152142] using wordTrace_append hprefix tailTrace_2152142
  have hstable : (prefixWord ++ tailWord_2152142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152142).length < 2 ^ (prefixWord ++ tailWord_2152142).sum := by decide
  have hdescent : baseEnd_2152142 < baseStart_2152142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152182 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_2152182 : Nat := 118140960795 + 2152182 * 2 ^ 59
def prefixEnd_2152182 : Nat := 4983230072969 + 3 ^ 40 * 2152182 * 2
def baseEnd_2152182 : Nat := 122789313550533756858589

theorem tailTrace_2152182 : CollatzResearch.WordTrace tailWord_2152182 prefixEnd_2152182 122789313550533756858589 := by
  unfold tailWord_2152182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4906032893063728266718175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52331017526013101511660533 4906032893063728266718175)
  ·
    refine ⟨7359049339595592400077263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4906032893063728266718175 7359049339595592400077263)
    ·
      refine ⟨11038574009393388600115895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7359049339595592400077263 11038574009393388600115895)
      ·
        refine ⟨16557861014090082900173843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11038574009393388600115895 16557861014090082900173843)
        ·
          refine ⟨24836791521135124350260765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16557861014090082900173843 24836791521135124350260765)
          ·
            refine ⟨9313796820425671631347787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24836791521135124350260765 9313796820425671631347787)
            ·
              refine ⟨13970695230638507447021681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9313796820425671631347787 13970695230638507447021681)
              ·
                refine ⟨10478021422978880585266261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13970695230638507447021681 10478021422978880585266261)
                ·
                  refine ⟨122789313550533756858589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10478021422978880585266261 122789313550533756858589)
                  ·
                    rfl

theorem cell23_2152182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_2152182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152182 prefixEnd_2152182 := by exact prefixLift 2152182
  have htrace : WordTrace (prefixWord ++ tailWord_2152182) baseStart_2152182 baseEnd_2152182 := by
    simpa [prefixWord, tailWord_2152182, baseEnd_2152182] using wordTrace_append hprefix tailTrace_2152182
  have hstable : (prefixWord ++ tailWord_2152182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152182).length < 2 ^ (prefixWord ++ tailWord_2152182).sum := by decide
  have hdescent : baseEnd_2152182 < baseStart_2152182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152229 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_2152229 : Nat := 118140960795 + 2152229 * 2 ^ 59
def prefixEnd_2152229 : Nat := 4983230072969 + 3 ^ 40 * 2152229 * 2
def baseEnd_2152229 : Nat := 368375985181855042613195

theorem tailTrace_2152229 : CollatzResearch.WordTrace tailWord_2152229 prefixEnd_2152229 368375985181855042613195 := by
  unfold tailWord_2152229
  simp only [CollatzResearch.WordTrace]
  refine ⟨78498240519849379294451741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52332160346566252862967827 78498240519849379294451741)
  ·
    refine ⟨29436840194943517235419403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78498240519849379294451741 29436840194943517235419403)
    ·
      refine ⟨44155260292415275853129105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29436840194943517235419403 44155260292415275853129105)
      ·
        refine ⟨33116445219311456889846829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44155260292415275853129105 33116445219311456889846829)
        ·
          refine ⟨12418666957241796333692561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33116445219311456889846829 12418666957241796333692561)
          ·
            refine ⟨9314000217931347250269421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12418666957241796333692561 9314000217931347250269421)
            ·
              refine ⟨3492750081724255218851033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9314000217931347250269421 3492750081724255218851033)
              ·
                refine ⟨2619562561293191414138275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3492750081724255218851033 2619562561293191414138275)
                ·
                  refine ⟨3929343841939787121207413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619562561293191414138275 3929343841939787121207413)
                  ·
                    refine ⟨368375985181855042613195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3929343841939787121207413 368375985181855042613195)
                    ·
                      rfl

theorem cell23_2152229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_2152229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152229 prefixEnd_2152229 := by exact prefixLift 2152229
  have htrace : WordTrace (prefixWord ++ tailWord_2152229) baseStart_2152229 baseEnd_2152229 := by
    simpa [prefixWord, tailWord_2152229, baseEnd_2152229] using wordTrace_append hprefix tailTrace_2152229
  have hstable : (prefixWord ++ tailWord_2152229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152229).length < 2 ^ (prefixWord ++ tailWord_2152229).sum := by decide
  have hdescent : baseEnd_2152229 < baseStart_2152229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152236 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 2, 3, 2]
def baseStart_2152236 : Nat := 118140960795 + 2152236 * 2 ^ 59
def prefixEnd_2152236 : Nat := 4983230072969 + 3 ^ 40 * 2152236 * 2
def baseEnd_2152236 : Nat := 1105131549910146600452053

theorem tailTrace_2152236 : CollatzResearch.WordTrace tailWord_2152236 prefixEnd_2152236 1105131549910146600452053 := by
  unfold tailWord_2152236
  simp only [CollatzResearch.WordTrace]
  refine ⟨39249247915412009744978281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52332330553882679659971041 39249247915412009744978281)
  ·
    refine ⟨29436935936559007308733711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39249247915412009744978281 29436935936559007308733711)
    ·
      refine ⟨44155403904838510963100567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29436935936559007308733711 44155403904838510963100567)
      ·
        refine ⟨66233105857257766444650851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44155403904838510963100567 66233105857257766444650851)
        ·
          refine ⟨99349658785886649666976277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66233105857257766444650851 99349658785886649666976277)
          ·
            refine ⟨4657015255588436703139513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99349658785886649666976277 4657015255588436703139513)
            ·
              refine ⟨3492761441691327527354635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4657015255588436703139513 3492761441691327527354635)
              ·
                refine ⟨5239142162536991291031953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3492761441691327527354635 5239142162536991291031953)
                ·
                  refine ⟨3929356621902743468273965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5239142162536991291031953 3929356621902743468273965)
                  ·
                    refine ⟨1473508733213528800602737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3929356621902743468273965 1473508733213528800602737)
                    ·
                      refine ⟨1105131549910146600452053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473508733213528800602737 1105131549910146600452053)
                      ·
                        rfl

theorem cell23_2152236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_2152236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152236 prefixEnd_2152236 := by exact prefixLift 2152236
  have htrace : WordTrace (prefixWord ++ tailWord_2152236) baseStart_2152236 baseEnd_2152236 := by
    simpa [prefixWord, tailWord_2152236, baseEnd_2152236] using wordTrace_append hprefix tailTrace_2152236
  have hstable : (prefixWord ++ tailWord_2152236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152236).length < 2 ^ (prefixWord ++ tailWord_2152236).sum := by decide
  have hdescent : baseEnd_2152236 < baseStart_2152236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152242 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_2152242 : Nat := 118140960795 + 2152242 * 2 ^ 59
def prefixEnd_2152242 : Nat := 4983230072969 + 3 ^ 40 * 2152242 * 2
def baseEnd_2152242 : Nat := 368378210264691192325675

theorem tailTrace_2152242 : CollatzResearch.WordTrace tailWord_2152242 prefixEnd_2152242 368378210264691192325675 := by
  unfold tailWord_2152242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19624678667200570628668745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52332476445868188343116653 19624678667200570628668745)
  ·
    refine ⟨14718509000400427971501559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19624678667200570628668745 14718509000400427971501559)
    ·
      refine ⟨22077763500600641957252339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14718509000400427971501559 22077763500600641957252339)
      ·
        refine ⟨33116645250900962935878509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22077763500600641957252339 33116645250900962935878509)
        ·
          refine ⟨12418741969087861100954441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33116645250900962935878509 12418741969087861100954441)
          ·
            refine ⟨9314056476815895825715831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12418741969087861100954441 9314056476815895825715831)
            ·
              refine ⟨13971084715223843738573747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9314056476815895825715831 13971084715223843738573747)
              ·
                refine ⟨20956627072835765607860621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13971084715223843738573747 20956627072835765607860621)
                ·
                  refine ⟨7858735152313412102947733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20956627072835765607860621 7858735152313412102947733)
                  ·
                    refine ⟨368378210264691192325675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7858735152313412102947733 368378210264691192325675)
                    ·
                      rfl

theorem cell23_2152242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_2152242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152242 prefixEnd_2152242 := by exact prefixLift 2152242
  have htrace : WordTrace (prefixWord ++ tailWord_2152242) baseStart_2152242 baseEnd_2152242 := by
    simpa [prefixWord, tailWord_2152242, baseEnd_2152242] using wordTrace_append hprefix tailTrace_2152242
  have hstable : (prefixWord ++ tailWord_2152242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152242).length < 2 ^ (prefixWord ++ tailWord_2152242).sum := by decide
  have hdescent : baseEnd_2152242 < baseStart_2152242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152255 : List Nat := [1, 1, 2, 2, 17]
def baseStart_2152255 : Nat := 118140960795 + 2152255 * 2 ^ 59
def prefixEnd_2152255 : Nat := 4983230072969 + 3 ^ 40 * 2152255 * 2
def baseEnd_2152255 : Nat := 1515968869742910872585

theorem tailTrace_2152255 : CollatzResearch.WordTrace tailWord_2152255 prefixEnd_2152255 1515968869742910872585 := by
  unfold tailWord_2152255
  simp only [CollatzResearch.WordTrace]
  refine ⟨78499188817755185734898219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52332792545170123823265479 78499188817755185734898219)
  ·
    refine ⟨117748783226632778602347329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78499188817755185734898219 117748783226632778602347329)
    ·
      refine ⟨88311587419974583951760497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117748783226632778602347329 88311587419974583951760497)
      ·
        refine ⟨66233690564980937963820373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88311587419974583951760497 66233690564980937963820373)
        ·
          refine ⟨1515968869742910872585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 66233690564980937963820373 1515968869742910872585)
          ·
            rfl

theorem cell23_2152255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 17].length) (baseStart_2152255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152255 prefixEnd_2152255 := by exact prefixLift 2152255
  have htrace : WordTrace (prefixWord ++ tailWord_2152255) baseStart_2152255 baseEnd_2152255 := by
    simpa [prefixWord, tailWord_2152255, baseEnd_2152255] using wordTrace_append hprefix tailTrace_2152255
  have hstable : (prefixWord ++ tailWord_2152255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152255).length < 2 ^ (prefixWord ++ tailWord_2152255).sum := by decide
  have hdescent : baseEnd_2152255 < baseStart_2152255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152259 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 2, 4]
def baseStart_2152259 : Nat := 118140960795 + 2152259 * 2 ^ 59
def prefixEnd_2152259 : Nat := 4983230072969 + 3 ^ 40 * 2152259 * 2
def baseEnd_2152259 : Nat := 368381119988400003488149

theorem tailTrace_2152259 : CollatzResearch.WordTrace tailWord_2152259 prefixEnd_2152259 368381119988400003488149 := by
  unfold tailWord_2152259
  simp only [CollatzResearch.WordTrace]
  refine ⟨78499334709740694418043831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52332889806493796278695887 78499334709740694418043831)
  ·
    refine ⟨117749002064611041627065747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78499334709740694418043831 117749002064611041627065747)
    ·
      refine ⟨176623503096916562440598621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117749002064611041627065747 176623503096916562440598621)
      ·
        refine ⟨66233813661343710915224483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176623503096916562440598621 66233813661343710915224483)
        ·
          refine ⟨99350720492015566372836725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66233813661343710915224483 99350720492015566372836725)
          ·
            refine ⟨9314130046126459347453443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99350720492015566372836725 9314130046126459347453443)
            ·
              refine ⟨13971195069189689021180165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9314130046126459347453443 13971195069189689021180165)
              ·
                refine ⟨2619599075473066691471281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13971195069189689021180165 2619599075473066691471281)
                ·
                  refine ⟨1964699306604800018603461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2619599075473066691471281 1964699306604800018603461)
                  ·
                    refine ⟨368381119988400003488149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964699306604800018603461 368381119988400003488149)
                    ·
                      rfl

theorem cell23_2152259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 4].length) (baseStart_2152259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152259 prefixEnd_2152259 := by exact prefixLift 2152259
  have htrace : WordTrace (prefixWord ++ tailWord_2152259) baseStart_2152259 baseEnd_2152259 := by
    simpa [prefixWord, tailWord_2152259, baseEnd_2152259] using wordTrace_append hprefix tailTrace_2152259
  have hstable : (prefixWord ++ tailWord_2152259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152259).length < 2 ^ (prefixWord ++ tailWord_2152259).sum := by decide
  have hdescent : baseEnd_2152259 < baseStart_2152259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152266 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2]
def baseStart_2152266 : Nat := 118140960795 + 2152266 * 2 ^ 59
def prefixEnd_2152266 : Nat := 4983230072969 + 3 ^ 40 * 2152266 * 2
def baseEnd_2152266 : Nat := 1105146954329781483076915

theorem tailTrace_2152266 : CollatzResearch.WordTrace tailWord_2152266 prefixEnd_2152266 1105146954329781483076915 := by
  unfold tailWord_2152266
  simp only [CollatzResearch.WordTrace]
  refine ⟨19624897505178833653387163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52333060013810223075699101 19624897505178833653387163)
  ·
    refine ⟨29437346257768250480080745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19624897505178833653387163 29437346257768250480080745)
    ·
      refine ⟨22078009693326187860060559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29437346257768250480080745 22078009693326187860060559)
      ·
        refine ⟨33117014539989281790090839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22078009693326187860060559 33117014539989281790090839)
        ·
          refine ⟨49675521809983922685136259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33117014539989281790090839 49675521809983922685136259)
          ·
            refine ⟨74513282714975884027704389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49675521809983922685136259 74513282714975884027704389)
            ·
              refine ⟨13971240509057978255194573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74513282714975884027704389 13971240509057978255194573)
              ·
                refine ⟨5239215190896741845697965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13971240509057978255194573 5239215190896741845697965)
                ·
                  refine ⟨1964705696586278192136737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5239215190896741845697965 1964705696586278192136737)
                  ·
                    refine ⟨1473529272439708644102553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1964705696586278192136737 1473529272439708644102553)
                    ·
                      refine ⟨1105146954329781483076915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473529272439708644102553 1105146954329781483076915)
                      ·
                        rfl

theorem cell23_2152266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_2152266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152266 prefixEnd_2152266 := by exact prefixLift 2152266
  have htrace : WordTrace (prefixWord ++ tailWord_2152266) baseStart_2152266 baseEnd_2152266 := by
    simpa [prefixWord, tailWord_2152266, baseEnd_2152266] using wordTrace_append hprefix tailTrace_2152266
  have hstable : (prefixWord ++ tailWord_2152266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152266).length < 2 ^ (prefixWord ++ tailWord_2152266).sum := by decide
  have hdescent : baseEnd_2152266 < baseStart_2152266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152276 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_2152276 : Nat := 118140960795 + 2152276 * 2 ^ 59
def prefixEnd_2152276 : Nat := 4983230072969 + 3 ^ 40 * 2152276 * 2
def baseEnd_2152276 : Nat := 368384029712108814650623

theorem tailTrace_2152276 : CollatzResearch.WordTrace tailWord_2152276 prefixEnd_2152276 368384029712108814650623 := by
  unfold tailWord_2152276
  simp only [CollatzResearch.WordTrace]
  refine ⟨39249977375339553160706341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52333303167119404214275121 39249977375339553160706341)
  ·
    refine ⟨7359370757876166217632439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39249977375339553160706341 7359370757876166217632439)
    ·
      refine ⟨11039056136814249326448659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7359370757876166217632439 11039056136814249326448659)
      ·
        refine ⟨16558584205221373989672989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11039056136814249326448659 16558584205221373989672989)
        ·
          refine ⟨6209469076958015246127371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16558584205221373989672989 6209469076958015246127371)
          ·
            refine ⟨9314203615437022869191057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6209469076958015246127371 9314203615437022869191057)
            ·
              refine ⟨6985652711577767151893293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9314203615437022869191057 6985652711577767151893293)
              ·
                refine ⟨2619619766841662681959985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6985652711577767151893293 2619619766841662681959985)
                ·
                  refine ⟨1964714825131247011469989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2619619766841662681959985 1964714825131247011469989)
                  ·
                    refine ⟨368384029712108814650623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964714825131247011469989 368384029712108814650623)
                    ·
                      rfl

theorem cell23_2152276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_2152276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152276 prefixEnd_2152276 := by exact prefixLift 2152276
  have htrace : WordTrace (prefixWord ++ tailWord_2152276) baseStart_2152276 baseEnd_2152276 := by
    simpa [prefixWord, tailWord_2152276, baseEnd_2152276] using wordTrace_append hprefix tailTrace_2152276
  have hstable : (prefixWord ++ tailWord_2152276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152276).length < 2 ^ (prefixWord ++ tailWord_2152276).sum := by decide
  have hdescent : baseEnd_2152276 < baseStart_2152276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152299 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 4, 1, 3]
def baseStart_2152299 : Nat := 118140960795 + 2152299 * 2 ^ 59
def prefixEnd_2152299 : Nat := 4983230072969 + 3 ^ 40 * 2152299 * 2
def baseEnd_2152299 : Nat := 1105163899191379853964263

theorem tailTrace_2152299 : CollatzResearch.WordTrace tailWord_2152299 prefixEnd_2152299 1105163899191379853964263 := by
  unfold tailWord_2152299
  simp only [CollatzResearch.WordTrace]
  refine ⟨78500793629595781249499951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52333862419730520832999967 78500793629595781249499951)
  ·
    refine ⟨117751190444393671874249927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78500793629595781249499951 117751190444393671874249927)
    ·
      refine ⟨176626785666590507811374891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117751190444393671874249927 176626785666590507811374891)
      ·
        refine ⟨264940178499885761717062337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176626785666590507811374891 264940178499885761717062337)
        ·
          refine ⟨198705133874914321287796753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264940178499885761717062337 198705133874914321287796753)
          ·
            refine ⟨149028850406185740965847565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198705133874914321287796753 149028850406185740965847565)
            ·
              refine ⟨55885818902319652862192837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149028850406185740965847565 55885818902319652862192837)
              ·
                refine ⟨10478591044184934911661157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55885818902319652862192837 10478591044184934911661157)
                ·
                  refine ⟨1964735820784675295936467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10478591044184934911661157 1964735820784675295936467)
                  ·
                    refine ⟨2947103731177012943904701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1964735820784675295936467 2947103731177012943904701)
                    ·
                      refine ⟨1105163899191379853964263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2947103731177012943904701 1105163899191379853964263)
                      ·
                        rfl

theorem cell23_2152299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 1, 3].length) (baseStart_2152299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152299 prefixEnd_2152299 := by exact prefixLift 2152299
  have htrace : WordTrace (prefixWord ++ tailWord_2152299) baseStart_2152299 baseEnd_2152299 := by
    simpa [prefixWord, tailWord_2152299, baseEnd_2152299] using wordTrace_append hprefix tailTrace_2152299
  have hstable : (prefixWord ++ tailWord_2152299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152299).length < 2 ^ (prefixWord ++ tailWord_2152299).sum := by decide
  have hdescent : baseEnd_2152299 < baseStart_2152299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152300 : List Nat := [2, 2, 1, 1, 4, 3, 2, 3, 1, 2, 2]
def baseStart_2152300 : Nat := 118140960795 + 2152300 * 2 ^ 59
def prefixEnd_2152300 : Nat := 4983230072969 + 3 ^ 40 * 2152300 * 2
def baseEnd_2152300 : Nat := 1105164412672034350051759

theorem tailTrace_2152300 : CollatzResearch.WordTrace tailWord_2152300 prefixEnd_2152300 1105164412672034350051759 := by
  unfold tailWord_2152300
  simp only [CollatzResearch.WordTrace]
  refine ⟨39250415051296079210143177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52333886735061438946857569 39250415051296079210143177)
  ·
    refine ⟨29437811288472059407607383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39250415051296079210143177 29437811288472059407607383)
    ·
      refine ⟨44156716932708089111411075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29437811288472059407607383 44156716932708089111411075)
      ·
        refine ⟨66235075399062133667116613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44156716932708089111411075 66235075399062133667116613)
        ·
          refine ⟨12419076637324150062584365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66235075399062133667116613 12419076637324150062584365)
          ·
            refine ⟨4657153738996556273469137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12419076637324150062584365 4657153738996556273469137)
            ·
              refine ⟨3492865304247417205101853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4657153738996556273469137 3492865304247417205101853)
              ·
                refine ⟨1309824489092781451913195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3492865304247417205101853 1309824489092781451913195)
                ·
                  refine ⟨1964736733639172177869793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309824489092781451913195 1964736733639172177869793)
                  ·
                    refine ⟨1473552550229379133402345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1964736733639172177869793 1473552550229379133402345)
                    ·
                      refine ⟨1105164412672034350051759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473552550229379133402345 1105164412672034350051759)
                      ·
                        rfl

theorem cell23_2152300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 1, 2, 2].length) (baseStart_2152300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152300 prefixEnd_2152300 := by exact prefixLift 2152300
  have htrace : WordTrace (prefixWord ++ tailWord_2152300) baseStart_2152300 baseEnd_2152300 := by
    simpa [prefixWord, tailWord_2152300, baseEnd_2152300] using wordTrace_append hprefix tailTrace_2152300
  have hstable : (prefixWord ++ tailWord_2152300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152300).length < 2 ^ (prefixWord ++ tailWord_2152300).sum := by decide
  have hdescent : baseEnd_2152300 < baseStart_2152300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152310 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_2152310 : Nat := 118140960795 + 2152310 * 2 ^ 59
def prefixEnd_2152310 : Nat := 4983230072969 + 3 ^ 40 * 2152310 * 2
def baseEnd_2152310 : Nat := 368389849159526436975571

theorem tailTrace_2152310 : CollatzResearch.WordTrace tailWord_2152310 prefixEnd_2152310 368389849159526436975571 := by
  unfold tailWord_2152310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4906324677034745633009399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52334129888370620085433589 4906324677034745633009399)
  ·
    refine ⟨7359487015552118449514099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4906324677034745633009399 7359487015552118449514099)
    ·
      refine ⟨11039230523328177674271149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7359487015552118449514099 11039230523328177674271149)
      ·
        refine ⟨4139711446248066627851681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11039230523328177674271149 4139711446248066627851681)
        ·
          refine ⟨3104783584686049970888761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4139711446248066627851681 3104783584686049970888761)
          ·
            refine ⟨2328587688514537478166571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3104783584686049970888761 2328587688514537478166571)
            ·
              refine ⟨3492881532771806217249857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328587688514537478166571 3492881532771806217249857)
              ·
                refine ⟨2619661149578854662937393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3492881532771806217249857 2619661149578854662937393)
                ·
                  refine ⟨1964745862184140997203045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2619661149578854662937393 1964745862184140997203045)
                  ·
                    refine ⟨368389849159526436975571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964745862184140997203045 368389849159526436975571)
                    ·
                      rfl

theorem cell23_2152310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_2152310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152310 prefixEnd_2152310 := by exact prefixLift 2152310
  have htrace : WordTrace (prefixWord ++ tailWord_2152310) baseStart_2152310 baseEnd_2152310 := by
    simpa [prefixWord, tailWord_2152310, baseEnd_2152310] using wordTrace_append hprefix tailTrace_2152310
  have hstable : (prefixWord ++ tailWord_2152310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152310).length < 2 ^ (prefixWord ++ tailWord_2152310).sum := by decide
  have hdescent : baseEnd_2152310 < baseStart_2152310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152343 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 1, 3, 2]
def baseStart_2152343 : Nat := 118140960795 + 2152343 * 2 ^ 59
def prefixEnd_2152343 : Nat := 4983230072969 + 3 ^ 40 * 2152343 * 2
def baseEnd_2152343 : Nat := 1105186492340177681814061

theorem tailTrace_2152343 : CollatzResearch.WordTrace tailWord_2152343 prefixEnd_2152343 1105186492340177681814061 := by
  unfold tailWord_2152343
  simp only [CollatzResearch.WordTrace]
  refine ⟨78502398441436376764101683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52334932294290917842734455 78502398441436376764101683)
  ·
    refine ⟨117753597662154565146152525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78502398441436376764101683 117753597662154565146152525)
    ·
      refine ⟨44157599123307961929807197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117753597662154565146152525 44157599123307961929807197)
      ·
        refine ⟨16559099671240485723677699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44157599123307961929807197 16559099671240485723677699)
        ·
          refine ⟨24838649506860728585516549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16559099671240485723677699 24838649506860728585516549)
          ·
            refine ⟨4657246782536386609784353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24838649506860728585516549 4657246782536386609784353)
            ·
              refine ⟨3492935086902289957338265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4657246782536386609784353 3492935086902289957338265)
              ·
                refine ⟨2619701315176717468003699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3492935086902289957338265 2619701315176717468003699)
                ·
                  refine ⟨3929551972765076202005549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619701315176717468003699 3929551972765076202005549)
                  ·
                    refine ⟨1473581989786903575752081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3929551972765076202005549 1473581989786903575752081)
                    ·
                      refine ⟨1105186492340177681814061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473581989786903575752081 1105186492340177681814061)
                      ·
                        rfl

theorem cell23_2152343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_2152343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152343 prefixEnd_2152343 := by exact prefixLift 2152343
  have htrace : WordTrace (prefixWord ++ tailWord_2152343) baseStart_2152343 baseEnd_2152343 := by
    simpa [prefixWord, tailWord_2152343, baseEnd_2152343] using wordTrace_append hprefix tailTrace_2152343
  have hstable : (prefixWord ++ tailWord_2152343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152343).length < 2 ^ (prefixWord ++ tailWord_2152343).sum := by decide
  have hdescent : baseEnd_2152343 < baseStart_2152343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152359 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2152359 : Nat := 118140960795 + 2152359 * 2 ^ 59
def prefixEnd_2152359 : Nat := 4983230072969 + 3 ^ 40 * 2152359 * 2
def baseEnd_2152359 : Nat := 1105194708030649619213987

theorem tailTrace_2152359 : CollatzResearch.WordTrace tailWord_2152359 prefixEnd_2152359 1105194708030649619213987 := by
  unfold tailWord_2152359
  simp only [CollatzResearch.WordTrace]
  refine ⟨78502982009378411496684131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52335321339585607664456087 78502982009378411496684131)
  ·
    refine ⟨117754473014067617245026197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78502982009378411496684131 117754473014067617245026197)
    ·
      refine ⟨5519740922534419558360603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 117754473014067617245026197 5519740922534419558360603)
      ·
        refine ⟨8279611383801629337540905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5519740922534419558360603 8279611383801629337540905)
        ·
          refine ⟨6209708537851222003155679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8279611383801629337540905 6209708537851222003155679)
          ·
            refine ⟨9314562806776833004733519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6209708537851222003155679 9314562806776833004733519)
            ·
              refine ⟨13971844210165249507100279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9314562806776833004733519 13971844210165249507100279)
              ·
                refine ⟨20957766315247874260650419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13971844210165249507100279 20957766315247874260650419)
                ·
                  refine ⟨31436649472871811390975629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20957766315247874260650419 31436649472871811390975629)
                  ·
                    refine ⟨11788743552326929271615861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31436649472871811390975629 11788743552326929271615861)
                    ·
                      refine ⟨1105194708030649619213987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11788743552326929271615861 1105194708030649619213987)
                      ·
                        rfl

theorem cell23_2152359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2152359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152359 prefixEnd_2152359 := by exact prefixLift 2152359
  have htrace : WordTrace (prefixWord ++ tailWord_2152359) baseStart_2152359 baseEnd_2152359 := by
    simpa [prefixWord, tailWord_2152359, baseEnd_2152359] using wordTrace_append hprefix tailTrace_2152359
  have hstable : (prefixWord ++ tailWord_2152359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152359).length < 2 ^ (prefixWord ++ tailWord_2152359).sum := by decide
  have hdescent : baseEnd_2152359 < baseStart_2152359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152373 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_2152373 : Nat := 118140960795 + 2152373 * 2 ^ 59
def prefixEnd_2152373 : Nat := 4983230072969 + 3 ^ 40 * 2152373 * 2
def baseEnd_2152373 : Nat := 1105201896759812564438923

theorem tailTrace_2152373 : CollatzResearch.WordTrace tailWord_2152373 prefixEnd_2152373 1105201896759812564438923 := by
  unfold tailWord_2152373
  simp only [CollatzResearch.WordTrace]
  refine ⟨78503492631327691887693773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52335661754218461258462515 78503492631327691887693773)
  ·
    refine ⟨29438809736747884457885165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78503492631327691887693773 29438809736747884457885165)
    ·
      refine ⟨11039553651280456671706937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29438809736747884457885165 11039553651280456671706937)
      ·
        refine ⟨8279665238460342503780203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11039553651280456671706937 8279665238460342503780203)
        ·
          refine ⟨12419497857690513755670305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8279665238460342503780203 12419497857690513755670305)
          ·
            refine ⟨9314623393267885316752729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12419497857690513755670305 9314623393267885316752729)
            ·
              refine ⟨6985967544950913987564547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9314623393267885316752729 6985967544950913987564547)
              ·
                refine ⟨10478951317426370981346821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6985967544950913987564547 10478951317426370981346821)
                ·
                  refine ⟨1964803372017444559002529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10478951317426370981346821 1964803372017444559002529)
                  ·
                    refine ⟨1473602529013083419251897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1964803372017444559002529 1473602529013083419251897)
                    ·
                      refine ⟨1105201896759812564438923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473602529013083419251897 1105201896759812564438923)
                      ·
                        rfl

theorem cell23_2152373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_2152373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152373 prefixEnd_2152373 := by exact prefixLift 2152373
  have htrace : WordTrace (prefixWord ++ tailWord_2152373) baseStart_2152373 baseEnd_2152373 := by
    simpa [prefixWord, tailWord_2152373, baseEnd_2152373] using wordTrace_append hprefix tailTrace_2152373
  have hstable : (prefixWord ++ tailWord_2152373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152373).length < 2 ^ (prefixWord ++ tailWord_2152373).sum := by decide
  have hdescent : baseEnd_2152373 < baseStart_2152373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152419 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2152419 : Nat := 118140960795 + 2152419 * 2 ^ 59
def prefixEnd_2152419 : Nat := 4983230072969 + 3 ^ 40 * 2152419 * 2
def baseEnd_2152419 : Nat := 1105225516869919384463711

theorem tailTrace_2152419 : CollatzResearch.WordTrace tailWord_2152419 prefixEnd_2152419 1105225516869919384463711 := by
  unfold tailWord_2152419
  simp only [CollatzResearch.WordTrace]
  refine ⟨78505170389161041743868311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52336780259440694495912207 78505170389161041743868311)
  ·
    refine ⟨117757755583741562615802467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78505170389161041743868311 117757755583741562615802467)
    ·
      refine ⟨176636633375612343923703701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117757755583741562615802467 176636633375612343923703701)
      ·
        refine ⟨8279842189481828621423611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 176636633375612343923703701 8279842189481828621423611)
        ·
          refine ⟨12419763284222742932135417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8279842189481828621423611 12419763284222742932135417)
          ·
            refine ⟨9314822463167057199101563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12419763284222742932135417 9314822463167057199101563)
            ·
              refine ⟨13972233694750585798652345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9314822463167057199101563 13972233694750585798652345)
              ·
                refine ⟨10479175271062939348989259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13972233694750585798652345 10479175271062939348989259)
                ·
                  refine ⟨15718762906594409023483889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10479175271062939348989259 15718762906594409023483889)
                  ·
                    refine ⟨11789072179945806767612917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15718762906594409023483889 11789072179945806767612917)
                    ·
                      refine ⟨1105225516869919384463711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11789072179945806767612917 1105225516869919384463711)
                      ·
                        rfl

theorem cell23_2152419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2152419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152419 prefixEnd_2152419 := by exact prefixLift 2152419
  have htrace : WordTrace (prefixWord ++ tailWord_2152419) baseStart_2152419 baseEnd_2152419 := by
    simpa [prefixWord, tailWord_2152419, baseEnd_2152419] using wordTrace_append hprefix tailTrace_2152419
  have hstable : (prefixWord ++ tailWord_2152419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152419).length < 2 ^ (prefixWord ++ tailWord_2152419).sum := by decide
  have hdescent : baseEnd_2152419 < baseStart_2152419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152430 : List Nat := [4, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_2152430 : Nat := 118140960795 + 2152430 * 2 ^ 59
def prefixEnd_2152430 : Nat := 4983230072969 + 3 ^ 40 * 2152430 * 2
def baseEnd_2152430 : Nat := 122803462795235426825129

theorem tailTrace_2152430 : CollatzResearch.WordTrace tailWord_2152430 prefixEnd_2152430 122803462795235426825129 := by
  unfold tailWord_2152430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9813196449015148827814843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52337047728080793748345829 9813196449015148827814843)
  ·
    refine ⟨14719794673522723241722265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9813196449015148827814843 14719794673522723241722265)
    ·
      refine ⟨11039846005142042431291699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14719794673522723241722265 11039846005142042431291699)
      ·
        refine ⟨16559769007713063646937549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11039846005142042431291699 16559769007713063646937549)
        ·
          refine ⟨6209913377892398867601581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16559769007713063646937549 6209913377892398867601581)
          ·
            refine ⟨2328717516709649575350593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6209913377892398867601581 2328717516709649575350593)
            ·
              refine ⟨1746538137532237181512945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2328717516709649575350593 1746538137532237181512945)
              ·
                refine ⟨1309903603149177886134709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1746538137532237181512945 1309903603149177886134709)
                ·
                  refine ⟨122803462795235426825129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1309903603149177886134709 122803462795235426825129)
                  ·
                    rfl

theorem cell23_2152430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_2152430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152430 prefixEnd_2152430 := by exact prefixLift 2152430
  have htrace : WordTrace (prefixWord ++ tailWord_2152430) baseStart_2152430 baseEnd_2152430 := by
    simpa [prefixWord, tailWord_2152430, baseEnd_2152430] using wordTrace_append hprefix tailTrace_2152430
  have hstable : (prefixWord ++ tailWord_2152430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152430).length < 2 ^ (prefixWord ++ tailWord_2152430).sum := by decide
  have hdescent : baseEnd_2152430 < baseStart_2152430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152439 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 9, 4]
def baseStart_2152439 : Nat := 118140960795 + 2152439 * 2 ^ 59
def prefixEnd_2152439 : Nat := 4983230072969 + 3 ^ 40 * 2152439 * 2
def baseEnd_2152439 : Nat := 368411928827669768737873

theorem tailTrace_2152439 : CollatzResearch.WordTrace tailWord_2152439 prefixEnd_2152439 368411928827669768737873 := by
  unfold tailWord_2152439
  simp only [CollatzResearch.WordTrace]
  refine ⟨78505899849088585159596371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52337266566059056773064247 78505899849088585159596371)
  ·
    refine ⟨117758849773632877739394557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78505899849088585159596371 117758849773632877739394557)
    ·
      refine ⟨44159568665112329152272959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117758849773632877739394557 44159568665112329152272959)
      ·
        refine ⟨66239352997668493728409439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44159568665112329152272959 66239352997668493728409439)
        ·
          refine ⟨99359029496502740592614159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66239352997668493728409439 99359029496502740592614159)
          ·
            refine ⟨149038544244754110888921239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99359029496502740592614159 149038544244754110888921239)
            ·
              refine ⟨223557816367131166333381859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149038544244754110888921239 223557816367131166333381859)
              ·
                refine ⟨335336724550696749500072789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223557816367131166333381859 335336724550696749500072789)
                ·
                  refine ⟨1964863620414238766601989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 335336724550696749500072789 1964863620414238766601989)
                  ·
                    refine ⟨368411928827669768737873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964863620414238766601989 368411928827669768737873)
                    ·
                      rfl

theorem cell23_2152439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_2152439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152439 prefixEnd_2152439 := by exact prefixLift 2152439
  have htrace : WordTrace (prefixWord ++ tailWord_2152439) baseStart_2152439 baseEnd_2152439 := by
    simpa [prefixWord, tailWord_2152439, baseEnd_2152439] using wordTrace_append hprefix tailTrace_2152439
  have hstable : (prefixWord ++ tailWord_2152439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152439).length < 2 ^ (prefixWord ++ tailWord_2152439).sum := by decide
  have hdescent : baseEnd_2152439 < baseStart_2152439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152456 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 3, 4]
def baseStart_2152456 : Nat := 118140960795 + 2152456 * 2 ^ 59
def prefixEnd_2152456 : Nat := 4983230072969 + 3 ^ 40 * 2152456 * 2
def baseEnd_2152456 : Nat := 368414838551378579900347

theorem tailTrace_2152456 : CollatzResearch.WordTrace tailWord_2152456 prefixEnd_2152456 368414838551378579900347 := by
  unfold tailWord_2152456
  simp only [CollatzResearch.WordTrace]
  refine ⟨39253259945013498531482611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52337679926684664708643481 39253259945013498531482611)
  ·
    refine ⟨58879889917520247797223917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39253259945013498531482611 58879889917520247797223917)
    ·
      refine ⟨22079958719070092923958969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58879889917520247797223917 22079958719070092923958969)
      ·
        refine ⟨16559969039302569692969227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22079958719070092923958969 16559969039302569692969227)
        ·
          refine ⟨24839953558953854539453841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16559969039302569692969227 24839953558953854539453841)
          ·
            refine ⟨18629965169215390904590381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24839953558953854539453841 18629965169215390904590381)
            ·
              refine ⟨6986236938455771589221393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18629965169215390904590381 6986236938455771589221393)
              ·
                refine ⟨5239677703841828691916045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6986236938455771589221393 5239677703841828691916045)
                ·
                  refine ⟨1964879138940685759468517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5239677703841828691916045 1964879138940685759468517)
                  ·
                    refine ⟨368414838551378579900347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964879138940685759468517 368414838551378579900347)
                    ·
                      rfl

theorem cell23_2152456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_2152456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152456 prefixEnd_2152456 := by exact prefixLift 2152456
  have htrace : WordTrace (prefixWord ++ tailWord_2152456) baseStart_2152456 baseEnd_2152456 := by
    simpa [prefixWord, tailWord_2152456, baseEnd_2152456] using wordTrace_append hprefix tailTrace_2152456
  have hstable : (prefixWord ++ tailWord_2152456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152456).length < 2 ^ (prefixWord ++ tailWord_2152456).sum := by decide
  have hdescent : baseEnd_2152456 < baseStart_2152456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152490 : List Nat := [3, 1, 4, 1, 2, 1, 2, 4, 1, 4]
def baseStart_2152490 : Nat := 118140960795 + 2152490 * 2 ^ 59
def prefixEnd_2152490 : Nat := 4983230072969 + 3 ^ 40 * 2152490 * 2
def baseEnd_2152490 : Nat := 368420657998796202225295

theorem tailTrace_2152490 : CollatzResearch.WordTrace tailWord_2152490 prefixEnd_2152490 368420657998796202225295 := by
  unfold tailWord_2152490
  simp only [CollatzResearch.WordTrace]
  refine ⟨19626939992975955217425731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52338506647935880579801949 19626939992975955217425731)
  ·
    refine ⟨29440409989463932826138597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19626939992975955217425731 29440409989463932826138597)
    ·
      refine ⟨5520076873024487404900987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29440409989463932826138597 5520076873024487404900987)
      ·
        refine ⟨8280115309536731107351481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5520076873024487404900987 8280115309536731107351481)
        ·
          refine ⟨6210086482152548330513611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8280115309536731107351481 6210086482152548330513611)
          ·
            refine ⟨9315129723228822495770417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6210086482152548330513611 9315129723228822495770417)
            ·
              refine ⟨6986347292421616871827813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9315129723228822495770417 6986347292421616871827813)
              ·
                refine ⟨1309940117329053163467715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6986347292421616871827813 1309940117329053163467715)
                ·
                  refine ⟨1964910175993579745201573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309940117329053163467715 1964910175993579745201573)
                  ·
                    refine ⟨368420657998796202225295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964910175993579745201573 368420657998796202225295)
                    ·
                      rfl

theorem cell23_2152490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_2152490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152490 prefixEnd_2152490 := by exact prefixLift 2152490
  have htrace : WordTrace (prefixWord ++ tailWord_2152490) baseStart_2152490 baseEnd_2152490 := by
    simpa [prefixWord, tailWord_2152490, baseEnd_2152490] using wordTrace_append hprefix tailTrace_2152490
  have hstable : (prefixWord ++ tailWord_2152490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152490).length < 2 ^ (prefixWord ++ tailWord_2152490).sum := by decide
  have hdescent : baseEnd_2152490 < baseStart_2152490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152499 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 5, 5]
def baseStart_2152499 : Nat := 118140960795 + 2152499 * 2 ^ 59
def prefixEnd_2152499 : Nat := 4983230072969 + 3 ^ 40 * 2152499 * 2
def baseEnd_2152499 : Nat := 368422198440759690487781

theorem tailTrace_2152499 : CollatzResearch.WordTrace tailWord_2152499 prefixEnd_2152499 368422198440759690487781 := by
  unfold tailWord_2152499
  simp only [CollatzResearch.WordTrace]
  refine ⟨78508088228871215406780551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52338725485914143604520367 78508088228871215406780551)
  ·
    refine ⟨117762132343306823110170827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78508088228871215406780551 117762132343306823110170827)
    ·
      refine ⟨176643198514960234665256241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117762132343306823110170827 176643198514960234665256241)
      ·
        refine ⟨132482398886220175998942181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176643198514960234665256241 132482398886220175998942181)
        ·
          refine ⟨24840449791166282999801659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132482398886220175998942181 24840449791166282999801659)
          ·
            refine ⟨37260674686749424499702489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24840449791166282999801659 37260674686749424499702489)
            ·
              refine ⟨27945506015062068374776867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37260674686749424499702489 27945506015062068374776867)
              ·
                refine ⟨41918259022593102562165301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27945506015062068374776867 41918259022593102562165301)
                ·
                  refine ⟨3929836783368103365202997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41918259022593102562165301 3929836783368103365202997)
                  ·
                    refine ⟨368422198440759690487781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3929836783368103365202997 368422198440759690487781)
                    ·
                      rfl

theorem cell23_2152499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 5].length) (baseStart_2152499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152499 prefixEnd_2152499 := by exact prefixLift 2152499
  have htrace : WordTrace (prefixWord ++ tailWord_2152499) baseStart_2152499 baseEnd_2152499 := by
    simpa [prefixWord, tailWord_2152499, baseEnd_2152499] using wordTrace_append hprefix tailTrace_2152499
  have hstable : (prefixWord ++ tailWord_2152499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152499).length < 2 ^ (prefixWord ++ tailWord_2152499).sum := by decide
  have hdescent : baseEnd_2152499 < baseStart_2152499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152529 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 3, 6]
def baseStart_2152529 : Nat := 118140960795 + 2152529 * 2 ^ 59
def prefixEnd_2152529 : Nat := 4983230072969 + 3 ^ 40 * 2152529 * 2
def baseEnd_2152529 : Nat := 368427333247304651362735

theorem tailTrace_2152529 : CollatzResearch.WordTrace tailWord_2152529 prefixEnd_2152529 368427333247304651362735 := by
  unfold tailWord_2152529
  simp only [CollatzResearch.WordTrace]
  refine ⟨78509182418762530530372641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52339454945841687020248427 78509182418762530530372641)
  ·
    refine ⟨58881886814071897897779481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78509182418762530530372641 58881886814071897897779481)
    ·
      refine ⟨44161415110553923423334611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58881886814071897897779481 44161415110553923423334611)
      ·
        refine ⟨66242122665830885135001917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44161415110553923423334611 66242122665830885135001917)
        ·
          refine ⟨24840795999686581925625719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66242122665830885135001917 24840795999686581925625719)
          ·
            refine ⟨37261193999529872888438579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24840795999686581925625719 37261193999529872888438579)
            ·
              refine ⟨55891790999294809332657869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37261193999529872888438579 55891790999294809332657869)
              ·
                refine ⟨20959421624735553499746701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55891790999294809332657869 20959421624735553499746701)
                ·
                  refine ⟨7859783109275832562405013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20959421624735553499746701 7859783109275832562405013)
                  ·
                    refine ⟨368427333247304651362735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7859783109275832562405013 368427333247304651362735)
                    ·
                      rfl

theorem cell23_2152529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_2152529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152529 prefixEnd_2152529 := by exact prefixLift 2152529
  have htrace : WordTrace (prefixWord ++ tailWord_2152529) baseStart_2152529 baseEnd_2152529 := by
    simpa [prefixWord, tailWord_2152529, baseEnd_2152529] using wordTrace_append hprefix tailTrace_2152529
  have hstable : (prefixWord ++ tailWord_2152529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152529).length < 2 ^ (prefixWord ++ tailWord_2152529).sum := by decide
  have hdescent : baseEnd_2152529 < baseStart_2152529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152540 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_2152540 : Nat := 118140960795 + 2152540 * 2 ^ 59
def prefixEnd_2152540 : Nat := 4983230072969 + 3 ^ 40 * 2152540 * 2
def baseEnd_2152540 : Nat := 1105287648029113411050655

theorem tailTrace_2152540 : CollatzResearch.WordTrace tailWord_2152540 prefixEnd_2152540 1105287648029113411050655 := by
  unfold tailWord_2152540
  simp only [CollatzResearch.WordTrace]
  refine ⟨39254791810861339704511537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52339722414481786272682049 39254791810861339704511537)
  ·
    refine ⟨29441093858146004778383653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39254791810861339704511537 29441093858146004778383653)
    ·
      refine ⟨5520205098402375895946935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29441093858146004778383653 5520205098402375895946935)
      ·
        refine ⟨8280307647603563843920403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5520205098402375895946935 8280307647603563843920403)
        ·
          refine ⟨12420461471405345765880605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8280307647603563843920403 12420461471405345765880605)
          ·
            refine ⟨4657673051777004662205227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12420461471405345765880605 4657673051777004662205227)
            ·
              refine ⟨6986509577665506993307841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4657673051777004662205227 6986509577665506993307841)
              ·
                refine ⟨5239882183249130244980881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6986509577665506993307841 5239882183249130244980881)
                ·
                  refine ⟨3929911637436847683735661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5239882183249130244980881 3929911637436847683735661)
                  ·
                    refine ⟨1473716864038817881400873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3929911637436847683735661 1473716864038817881400873)
                    ·
                      refine ⟨1105287648029113411050655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473716864038817881400873 1105287648029113411050655)
                      ·
                        rfl

theorem cell23_2152540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_2152540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152540 prefixEnd_2152540 := by exact prefixLift 2152540
  have htrace : WordTrace (prefixWord ++ tailWord_2152540) baseStart_2152540 baseEnd_2152540 := by
    simpa [prefixWord, tailWord_2152540, baseEnd_2152540] using wordTrace_append hprefix tailTrace_2152540
  have hstable : (prefixWord ++ tailWord_2152540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152540).length < 2 ^ (prefixWord ++ tailWord_2152540).sum := by decide
  have hdescent : baseEnd_2152540 < baseStart_2152540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152556 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_2152556 : Nat := 118140960795 + 2152556 * 2 ^ 59
def prefixEnd_2152556 : Nat := 4983230072969 + 3 ^ 40 * 2152556 * 2
def baseEnd_2152556 : Nat := 1105295863719585348450581

theorem tailTrace_2152556 : CollatzResearch.WordTrace tailWord_2152556 prefixEnd_2152556 1105295863719585348450581 := by
  unfold tailWord_2152556
  simp only [CollatzResearch.WordTrace]
  refine ⟨39255083594832357070802761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52340111459776476094403681 39255083594832357070802761)
  ·
    refine ⟨29441312696124267803102071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39255083594832357070802761 29441312696124267803102071)
    ·
      refine ⟨44161969044186401704653107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29441312696124267803102071 44161969044186401704653107)
      ·
        refine ⟨66242953566279602556979661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44161969044186401704653107 66242953566279602556979661)
        ·
          refine ⟨24841107587354850958867373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66242953566279602556979661 24841107587354850958867373)
          ·
            refine ⟨9315415345258069109575265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24841107587354850958867373 9315415345258069109575265)
            ·
              refine ⟨6986561508943551832181449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9315415345258069109575265 6986561508943551832181449)
              ·
                refine ⟨5239921131707663874136087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6986561508943551832181449 5239921131707663874136087)
                ·
                  refine ⟨7859881697561495811204131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5239921131707663874136087 7859881697561495811204131)
                  ·
                    refine ⟨11789822546342243716806197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7859881697561495811204131 11789822546342243716806197)
                    ·
                      refine ⟨1105295863719585348450581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11789822546342243716806197 1105295863719585348450581)
                      ·
                        rfl

theorem cell23_2152556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_2152556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152556 prefixEnd_2152556 := by exact prefixLift 2152556
  have htrace : WordTrace (prefixWord ++ tailWord_2152556) baseStart_2152556 baseEnd_2152556 := by
    simpa [prefixWord, tailWord_2152556, baseEnd_2152556] using wordTrace_append hprefix tailTrace_2152556
  have hstable : (prefixWord ++ tailWord_2152556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152556).length < 2 ^ (prefixWord ++ tailWord_2152556).sum := by decide
  have hdescent : baseEnd_2152556 < baseStart_2152556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152559 : List Nat := [1, 1, 2, 1, 3, 4, 1, 10]
def baseStart_2152559 : Nat := 118140960795 + 2152559 * 2 ^ 59
def prefixEnd_2152559 : Nat := 4983230072969 + 3 ^ 40 * 2152559 * 2
def baseEnd_2152559 : Nat := 40936940894872179137521

theorem tailTrace_2152559 : CollatzResearch.WordTrace tailWord_2152559 prefixEnd_2152559 40936940894872179137521 := by
  unfold tailWord_2152559
  simp only [CollatzResearch.WordTrace]
  refine ⟨78510276608653845653964731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52340184405769230435976487 78510276608653845653964731)
  ·
    refine ⟨117765414912980768480947097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78510276608653845653964731 117765414912980768480947097)
    ·
      refine ⟨88324061184735576360710323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117765414912980768480947097 88324061184735576360710323)
      ·
        refine ⟨132486091777103364541065485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88324061184735576360710323 132486091777103364541065485)
        ·
          refine ⟨49682284416413761702899557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132486091777103364541065485 49682284416413761702899557)
          ·
            refine ⟨9315428328077580319293667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49682284416413761702899557 9315428328077580319293667)
            ·
              refine ⟨13973142492116370478940501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9315428328077580319293667 13973142492116370478940501)
              ·
                refine ⟨40936940894872179137521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13973142492116370478940501 40936940894872179137521)
                ·
                  rfl

theorem cell23_2152559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 10].length) (baseStart_2152559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152559 prefixEnd_2152559 := by exact prefixLift 2152559
  have htrace : WordTrace (prefixWord ++ tailWord_2152559) baseStart_2152559 baseEnd_2152559 := by
    simpa [prefixWord, tailWord_2152559, baseEnd_2152559] using wordTrace_append hprefix tailTrace_2152559
  have hstable : (prefixWord ++ tailWord_2152559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152559).length < 2 ^ (prefixWord ++ tailWord_2152559).sum := by decide
  have hdescent : baseEnd_2152559 < baseStart_2152559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152573 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_2152573 : Nat := 118140960795 + 2152573 * 2 ^ 59
def prefixEnd_2152573 : Nat := 4983230072969 + 3 ^ 40 * 2152573 * 2
def baseEnd_2152573 : Nat := 1105304592890711781938003

theorem tailTrace_2152573 : CollatzResearch.WordTrace tailWord_2152573 prefixEnd_2152573 1105304592890711781938003 := by
  unfold tailWord_2152573
  simp only [CollatzResearch.WordTrace]
  refine ⟨78510787230603126044974373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52340524820402084029982915 78510787230603126044974373)
  ·
    refine ⟨14720772605738086133432695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78510787230603126044974373 14720772605738086133432695)
    ·
      refine ⟨22081158908607129200149043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14720772605738086133432695 22081158908607129200149043)
      ·
        refine ⟨33121738362910693800223565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22081158908607129200149043 33121738362910693800223565)
        ·
          refine ⟨12420651886091510175083837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33121738362910693800223565 12420651886091510175083837)
          ·
            refine ⟨4657744457284316315656439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12420651886091510175083837 4657744457284316315656439)
            ·
              refine ⟨6986616685926474473484659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4657744457284316315656439 6986616685926474473484659)
              ·
                refine ⟨10479925028889711710226989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6986616685926474473484659 10479925028889711710226989)
                ·
                  refine ⟨3929971885833641891335121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10479925028889711710226989 3929971885833641891335121)
                  ·
                    refine ⟨2947478914375231418501341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3929971885833641891335121 2947478914375231418501341)
                    ·
                      refine ⟨1105304592890711781938003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2947478914375231418501341 1105304592890711781938003)
                      ·
                        rfl

theorem cell23_2152573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_2152573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152573 prefixEnd_2152573 := by exact prefixLift 2152573
  have htrace : WordTrace (prefixWord ++ tailWord_2152573) baseStart_2152573 baseEnd_2152573 := by
    simpa [prefixWord, tailWord_2152573, baseEnd_2152573] using wordTrace_append hprefix tailTrace_2152573
  have hstable : (prefixWord ++ tailWord_2152573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152573).length < 2 ^ (prefixWord ++ tailWord_2152573).sum := by decide
  have hdescent : baseEnd_2152573 < baseStart_2152573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152590 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2152590 : Nat := 118140960795 + 2152590 * 2 ^ 59
def prefixEnd_2152590 : Nat := 4983230072969 + 3 ^ 40 * 2152590 * 2
def baseEnd_2152590 : Nat := 1105313322061838215425425

theorem tailTrace_2152590 : CollatzResearch.WordTrace tailWord_2152590 prefixEnd_2152590 1105313322061838215425425 := by
  unfold tailWord_2152590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9813925908942692243542903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52340938181027691965562149 9813925908942692243542903)
  ·
    refine ⟨14720888863414038365314355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9813925908942692243542903 14720888863414038365314355)
    ·
      refine ⟨22081333295121057547971533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14720888863414038365314355 22081333295121057547971533)
      ·
        refine ⟨8280499985670396580489325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22081333295121057547971533 8280499985670396580489325)
        ·
          refine ⟨3105187494626398717683497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8280499985670396580489325 3105187494626398717683497)
          ·
            refine ⟨2328890620969799038262623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3105187494626398717683497 2328890620969799038262623)
            ·
              refine ⟨3493335931454698557393935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328890620969799038262623 3493335931454698557393935)
              ·
                refine ⟨5240003897182047836090903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493335931454698557393935 5240003897182047836090903)
                ·
                  refine ⟨7860005845773071754136355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5240003897182047836090903 7860005845773071754136355)
                  ·
                    refine ⟨11790008768659607631204533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7860005845773071754136355 11790008768659607631204533)
                    ·
                      refine ⟨1105313322061838215425425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11790008768659607631204533 1105313322061838215425425)
                      ·
                        rfl

theorem cell23_2152590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2152590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152590 prefixEnd_2152590 := by exact prefixLift 2152590
  have htrace : WordTrace (prefixWord ++ tailWord_2152590) baseStart_2152590 baseEnd_2152590 := by
    simpa [prefixWord, tailWord_2152590, baseEnd_2152590] using wordTrace_append hprefix tailTrace_2152590
  have hstable : (prefixWord ++ tailWord_2152590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152590).length < 2 ^ (prefixWord ++ tailWord_2152590).sum := by decide
  have hdescent : baseEnd_2152590 < baseStart_2152590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
