import V185TrunkScan23Chunk0136

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_810903 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 2, 4, 2]
def baseStart_810903 : Nat := 118140960795 + 810903 * 2 ^ 59
def prefixEnd_810903 : Nat := 4983230072969 + 3 ^ 40 * 810903 * 2
def baseEnd_810903 : Nat := 416383003172946071983231

theorem tailTrace_810903 : CollatzResearch.WordTrace tailWord_810903 prefixEnd_810903 416383003172946071983231 := by
  unfold tailWord_810903
  simp only [CollatzResearch.WordTrace]
  refine ⟨29576062181244397051661363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19717374787496264701107575 29576062181244397051661363)
  ·
    refine ⟨44364093271866595577492045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29576062181244397051661363 44364093271866595577492045)
    ·
      refine ⟨16636534976949973341559517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44364093271866595577492045 16636534976949973341559517)
      ·
        refine ⟨6238700616356240003084819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16636534976949973341559517 6238700616356240003084819)
        ·
          refine ⟨9358050924534360004627229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6238700616356240003084819 9358050924534360004627229)
          ·
            refine ⟨3509269096700385001735211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9358050924534360004627229 3509269096700385001735211)
            ·
              refine ⟨5263903645050577502602817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3509269096700385001735211 5263903645050577502602817)
              ·
                refine ⟨3947927733787933126952113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5263903645050577502602817 3947927733787933126952113)
                ·
                  refine ⟨2960945800340949845214085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3947927733787933126952113 2960945800340949845214085)
                  ·
                    refine ⟨555177337563928095977641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2960945800340949845214085 555177337563928095977641)
                    ·
                      refine ⟨416383003172946071983231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 555177337563928095977641 416383003172946071983231)
                      ·
                        rfl

theorem cell23_810903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_810903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810903 prefixEnd_810903 := by exact prefixLift 810903
  have htrace : WordTrace (prefixWord ++ tailWord_810903) baseStart_810903 baseEnd_810903 := by
    simpa [prefixWord, tailWord_810903, baseEnd_810903] using wordTrace_append hprefix tailTrace_810903
  have hstable : (prefixWord ++ tailWord_810903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810903).length < 2 ^ (prefixWord ++ tailWord_810903).sum := by decide
  have hdescent : baseEnd_810903 < baseStart_810903 := by decide
  rcases family_descends (prefixWord ++ tailWord_810903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810936 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 2, 5, 3]
def baseStart_810936 : Nat := 118140960795 + 810936 * 2 ^ 59
def prefixEnd_810936 : Nat := 4983230072969 + 3 ^ 40 * 810936 * 2
def baseEnd_810936 : Nat := 416399948034544442870579

theorem tailTrace_810936 : CollatzResearch.WordTrace tailWord_810936 prefixEnd_810936 416399948034544442870579 := by
  unfold tailWord_810936
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788632895062421843806331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19718177193416562458408441 14788632895062421843806331)
  ·
    refine ⟨22182949342593632765709497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14788632895062421843806331 22182949342593632765709497)
    ·
      refine ⟨16637212006945224574282123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22182949342593632765709497 16637212006945224574282123)
      ·
        refine ⟨24955818010417836861423185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16637212006945224574282123 24955818010417836861423185)
        ·
          refine ⟨18716863507813377646067389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24955818010417836861423185 18716863507813377646067389)
          ·
            refine ⟨7018823815430016617275271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18716863507813377646067389 7018823815430016617275271)
            ·
              refine ⟨10528235723145024925912907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018823815430016617275271 10528235723145024925912907)
              ·
                refine ⟨15792353584717537388869361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10528235723145024925912907 15792353584717537388869361)
                ·
                  refine ⟨11844265188538153041652021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15792353584717537388869361 11844265188538153041652021)
                  ·
                    refine ⟨1110399861425451847654877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11844265188538153041652021 1110399861425451847654877)
                    ·
                      refine ⟨416399948034544442870579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1110399861425451847654877 416399948034544442870579)
                      ·
                        rfl

theorem cell23_810936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_810936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810936 prefixEnd_810936 := by exact prefixLift 810936
  have htrace : WordTrace (prefixWord ++ tailWord_810936) baseStart_810936 baseEnd_810936 := by
    simpa [prefixWord, tailWord_810936, baseEnd_810936] using wordTrace_append hprefix tailTrace_810936
  have hstable : (prefixWord ++ tailWord_810936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810936).length < 2 ^ (prefixWord ++ tailWord_810936).sum := by decide
  have hdescent : baseEnd_810936 < baseStart_810936 := by decide
  rcases family_descends (prefixWord ++ tailWord_810936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810990 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_810990 : Nat := 118140960795 + 810990 * 2 ^ 59
def prefixEnd_810990 : Nat := 4983230072969 + 3 ^ 40 * 810990 * 2
def baseEnd_810990 : Nat := 138809225329962410531777

theorem tailTrace_810990 : CollatzResearch.WordTrace tailWord_810990 prefixEnd_810990 138809225329962410531777 := by
  unfold tailWord_810990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697404416491151363759803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19719490221286140606718949 3697404416491151363759803)
  ·
    refine ⟨5546106624736727045639705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3697404416491151363759803 5546106624736727045639705)
    ·
      refine ⟨4159579968552545284229779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5546106624736727045639705 4159579968552545284229779)
      ·
        refine ⟨6239369952828817926344669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4159579968552545284229779 6239369952828817926344669)
        ·
          refine ⟨2339763732310806722379251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6239369952828817926344669 2339763732310806722379251)
          ·
            refine ⟨3509645598466210083568877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339763732310806722379251 3509645598466210083568877)
            ·
              refine ⟨1316117099424828781338329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3509645598466210083568877 1316117099424828781338329)
              ·
                refine ⟨987087824568621586003747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316117099424828781338329 987087824568621586003747)
                ·
                  refine ⟨1480631736852932379005621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987087824568621586003747 1480631736852932379005621)
                  ·
                    refine ⟨138809225329962410531777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1480631736852932379005621 138809225329962410531777)
                    ·
                      rfl

theorem cell23_810990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_810990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_810990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_810990 prefixEnd_810990 := by exact prefixLift 810990
  have htrace : WordTrace (prefixWord ++ tailWord_810990) baseStart_810990 baseEnd_810990 := by
    simpa [prefixWord, tailWord_810990, baseEnd_810990] using wordTrace_append hprefix tailTrace_810990
  have hstable : (prefixWord ++ tailWord_810990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810990).length < 2 ^ (prefixWord ++ tailWord_810990).sum := by decide
  have hdescent : baseEnd_810990 < baseStart_810990 := by decide
  rcases family_descends (prefixWord ++ tailWord_810990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811013 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 5]
def baseStart_811013 : Nat := 118140960795 + 811013 * 2 ^ 59
def prefixEnd_811013 : Nat := 4983230072969 + 3 ^ 40 * 811013 * 2
def baseEnd_811013 : Nat := 416439486044940641607725

theorem tailTrace_811013 : CollatzResearch.WordTrace tailWord_811013 prefixEnd_811013 416439486044940641607725 := by
  unfold tailWord_811013
  simp only [CollatzResearch.WordTrace]
  refine ⟨29580074210845885838165693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19720049473897257225443795 29580074210845885838165693)
  ·
    refine ⟨11092527829067207189312135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29580074210845885838165693 11092527829067207189312135)
    ·
      refine ⟨16638791743600810783968203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11092527829067207189312135 16638791743600810783968203)
      ·
        refine ⟨24958187615401216175952305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16638791743600810783968203 24958187615401216175952305)
        ·
          refine ⟨18718640711550912131964229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24958187615401216175952305 18718640711550912131964229)
          ·
            refine ⟨3509745133415796024743293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18718640711550912131964229 3509745133415796024743293)
            ·
              refine ⟨1316154425030923509278735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3509745133415796024743293 1316154425030923509278735)
              ·
                refine ⟨1974231637546385263918103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316154425030923509278735 1974231637546385263918103)
                ·
                  refine ⟨2961347456319577895877155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974231637546385263918103 2961347456319577895877155)
                  ·
                    refine ⟨4442021184479366843815733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2961347456319577895877155 4442021184479366843815733)
                    ·
                      refine ⟨416439486044940641607725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4442021184479366843815733 416439486044940641607725)
                      ·
                        rfl

theorem cell23_811013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_811013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811013 prefixEnd_811013 := by exact prefixLift 811013
  have htrace : WordTrace (prefixWord ++ tailWord_811013) baseStart_811013 baseEnd_811013 := by
    simpa [prefixWord, tailWord_811013, baseEnd_811013] using wordTrace_append hprefix tailTrace_811013
  have hstable : (prefixWord ++ tailWord_811013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811013).length < 2 ^ (prefixWord ++ tailWord_811013).sum := by decide
  have hdescent : baseEnd_811013 < baseStart_811013 := by decide
  rcases family_descends (prefixWord ++ tailWord_811013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811020 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_811020 : Nat := 118140960795 + 811020 * 2 ^ 59
def prefixEnd_811020 : Nat := 4983230072969 + 3 ^ 40 * 811020 * 2
def baseEnd_811020 : Nat := 138814360136507371406731

theorem tailTrace_811020 : CollatzResearch.WordTrace tailWord_811020 prefixEnd_811020 138814360136507371406731 := by
  unfold tailWord_811020
  simp only [CollatzResearch.WordTrace]
  refine ⟨14790164760910263016835257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19720219681213684022447009 14790164760910263016835257)
  ·
    refine ⟨11092623570682697262626443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14790164760910263016835257 11092623570682697262626443)
    ·
      refine ⟨16638935356024045893939665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11092623570682697262626443 16638935356024045893939665)
      ·
        refine ⟨12479201517018034420454749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16638935356024045893939665 12479201517018034420454749)
        ·
          refine ⟨4679700568881762907670531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12479201517018034420454749 4679700568881762907670531)
          ·
            refine ⟨7019550853322644361505797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679700568881762907670531 7019550853322644361505797)
            ·
              refine ⟨1316165784997995817782337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7019550853322644361505797 1316165784997995817782337)
              ·
                refine ⟨987124338748496863336753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316165784997995817782337 987124338748496863336753)
                ·
                  refine ⟨740343254061372647502565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 987124338748496863336753 740343254061372647502565)
                  ·
                    refine ⟨138814360136507371406731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 740343254061372647502565 138814360136507371406731)
                    ·
                      rfl

theorem cell23_811020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_811020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811020 prefixEnd_811020 := by exact prefixLift 811020
  have htrace : WordTrace (prefixWord ++ tailWord_811020) baseStart_811020 baseEnd_811020 := by
    simpa [prefixWord, tailWord_811020, baseEnd_811020] using wordTrace_append hprefix tailTrace_811020
  have hstable : (prefixWord ++ tailWord_811020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811020).length < 2 ^ (prefixWord ++ tailWord_811020).sum := by decide
  have hdescent : baseEnd_811020 < baseStart_811020 := by decide
  rcases family_descends (prefixWord ++ tailWord_811020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811044 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 3, 2, 2]
def baseStart_811044 : Nat := 118140960795 + 811044 * 2 ^ 59
def prefixEnd_811044 : Nat := 4983230072969 + 3 ^ 40 * 811044 * 2
def baseEnd_811044 : Nat := 416455403945230020320083

theorem tailTrace_811044 : CollatzResearch.WordTrace tailWord_811044 prefixEnd_811044 416455403945230020320083 := by
  unfold tailWord_811044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14790602436866789066272093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19720803249155718755029457 14790602436866789066272093)
  ·
    refine ⟨5546475913825045899852035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14790602436866789066272093 5546475913825045899852035)
    ·
      refine ⟨8319713870737568849778053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5546475913825045899852035 8319713870737568849778053)
      ·
        refine ⟨1559946350763294159333385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8319713870737568849778053 1559946350763294159333385)
        ·
          refine ⟨1169959763072470619500039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559946350763294159333385 1169959763072470619500039)
          ·
            refine ⟨1754939644608705929250059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169959763072470619500039 1754939644608705929250059)
            ·
              refine ⟨2632409466913058893875089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754939644608705929250059 2632409466913058893875089)
              ·
                refine ⟨1974307100184794170406317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632409466913058893875089 1974307100184794170406317)
                ·
                  refine ⟨740365162569297813902369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1974307100184794170406317 740365162569297813902369)
                  ·
                    refine ⟨555273871926973360426777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 740365162569297813902369 555273871926973360426777)
                    ·
                      refine ⟨416455403945230020320083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 555273871926973360426777 416455403945230020320083)
                      ·
                        rfl

theorem cell23_811044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_811044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811044 prefixEnd_811044 := by exact prefixLift 811044
  have htrace : WordTrace (prefixWord ++ tailWord_811044) baseStart_811044 baseEnd_811044 := by
    simpa [prefixWord, tailWord_811044, baseEnd_811044] using wordTrace_append hprefix tailTrace_811044
  have hstable : (prefixWord ++ tailWord_811044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811044).length < 2 ^ (prefixWord ++ tailWord_811044).sum := by decide
  have hdescent : baseEnd_811044 < baseStart_811044 := by decide
  rcases family_descends (prefixWord ++ tailWord_811044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811050 : List Nat := [3, 1, 4, 1, 2, 2, 3, 7]
def baseStart_811050 : Nat := 118140960795 + 811050 * 2 ^ 59
def prefixEnd_811050 : Nat := 4983230072969 + 3 ^ 40 * 811050 * 2
def baseEnd_811050 : Nat := 15424388327005814697965

theorem tailTrace_811050 : CollatzResearch.WordTrace tailWord_811050 prefixEnd_811050 15424388327005814697965 := by
  unfold tailWord_811050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7395355927927960289315651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19720949141141227438175069 7395355927927960289315651)
  ·
    refine ⟨11093033891891940433973477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7395355927927960289315651 11093033891891940433973477)
    ·
      refine ⟨2079943854729738831370027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11093033891891940433973477 2079943854729738831370027)
      ·
        refine ⟨3119915782094608247055041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079943854729738831370027 3119915782094608247055041)
        ·
          refine ⟨2339936836570956185291281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3119915782094608247055041 2339936836570956185291281)
          ·
            refine ⟨1754952627428217138968461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2339936836570956185291281 1754952627428217138968461)
            ·
              refine ⟨658107235285581427113173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1754952627428217138968461 658107235285581427113173)
              ·
                refine ⟨15424388327005814697965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 658107235285581427113173 15424388327005814697965)
                ·
                  rfl

theorem cell23_811050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 7].length) (baseStart_811050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811050 prefixEnd_811050 := by exact prefixLift 811050
  have htrace : WordTrace (prefixWord ++ tailWord_811050) baseStart_811050 baseEnd_811050 := by
    simpa [prefixWord, tailWord_811050, baseEnd_811050] using wordTrace_append hprefix tailTrace_811050
  have hstable : (prefixWord ++ tailWord_811050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811050).length < 2 ^ (prefixWord ++ tailWord_811050).sum := by decide
  have hdescent : baseEnd_811050 < baseStart_811050 := by decide
  rcases family_descends (prefixWord ++ tailWord_811050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811064 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 1, 2, 3]
def baseStart_811064 : Nat := 118140960795 + 811064 * 2 ^ 59
def prefixEnd_811064 : Nat := 4983230072969 + 3 ^ 40 * 811064 * 2
def baseEnd_811064 : Nat := 416465673558319942069991

theorem tailTrace_811064 : CollatzResearch.WordTrace tailWord_811064 prefixEnd_811064 416465673558319942069991 := by
  unfold tailWord_811064
  simp only [CollatzResearch.WordTrace]
  refine ⟨14790967166830560774136123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19721289555774081032181497 14790967166830560774136123)
  ·
    refine ⟨22186450750245841161204185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14790967166830560774136123 22186450750245841161204185)
    ·
      refine ⟨16639838062684380870903139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22186450750245841161204185 16639838062684380870903139)
      ·
        refine ⟨24959757094026571306354709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16639838062684380870903139 24959757094026571306354709)
        ·
          refine ⟨1169988613782495529985377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24959757094026571306354709 1169988613782495529985377)
          ·
            refine ⟨877491460336871647489033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169988613782495529985377 877491460336871647489033)
            ·
              refine ⟨658118595252653735616775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877491460336871647489033 658118595252653735616775)
              ·
                refine ⟨987177892878980603425163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658118595252653735616775 987177892878980603425163)
                ·
                  refine ⟨1480766839318470905137745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987177892878980603425163 1480766839318470905137745)
                  ·
                    refine ⟨1110575129488853178853309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1480766839318470905137745 1110575129488853178853309)
                    ·
                      refine ⟨416465673558319942069991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1110575129488853178853309 416465673558319942069991)
                      ·
                        rfl

theorem cell23_811064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_811064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811064 prefixEnd_811064 := by exact prefixLift 811064
  have htrace : WordTrace (prefixWord ++ tailWord_811064) baseStart_811064 baseEnd_811064 := by
    simpa [prefixWord, tailWord_811064, baseEnd_811064] using wordTrace_append hprefix tailTrace_811064
  have hstable : (prefixWord ++ tailWord_811064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811064).length < 2 ^ (prefixWord ++ tailWord_811064).sum := by decide
  have hdescent : baseEnd_811064 < baseStart_811064 := by decide
  rcases family_descends (prefixWord ++ tailWord_811064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811093 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_811093 : Nat := 118140960795 + 811093 * 2 ^ 59
def prefixEnd_811093 : Nat := 4983230072969 + 3 ^ 40 * 811093 * 2
def baseEnd_811093 : Nat := 138826854832433442869119

theorem tailTrace_811093 : CollatzResearch.WordTrace tailWord_811093 prefixEnd_811093 138826854832433442869119 := by
  unfold tailWord_811093
  simp only [CollatzResearch.WordTrace]
  refine ⟨29582992050556059501077933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19721994700370706334051955 29582992050556059501077933)
  ·
    refine ⟨11093622018958522312904225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29582992050556059501077933 11093622018958522312904225)
    ·
      refine ⟨8320216514218891734678169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11093622018958522312904225 8320216514218891734678169)
      ·
        refine ⟨6240162385664168801008627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8320216514218891734678169 6240162385664168801008627)
        ·
          refine ⟨9360243578496253201512941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6240162385664168801008627 9360243578496253201512941)
          ·
            refine ⟨3510091341936094950567353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9360243578496253201512941 3510091341936094950567353)
            ·
              refine ⟨2632568506452071212925515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3510091341936094950567353 2632568506452071212925515)
              ·
                refine ⟨3948852759678106819388273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632568506452071212925515 3948852759678106819388273)
                ·
                  refine ⟨2961639569758580114541205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3948852759678106819388273 2961639569758580114541205)
                  ·
                    refine ⟨138826854832433442869119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2961639569758580114541205 138826854832433442869119)
                    ·
                      rfl

theorem cell23_811093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_811093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811093 prefixEnd_811093 := by exact prefixLift 811093
  have htrace : WordTrace (prefixWord ++ tailWord_811093) baseStart_811093 baseEnd_811093 := by
    simpa [prefixWord, tailWord_811093, baseEnd_811093] using wordTrace_append hprefix tailTrace_811093
  have hstable : (prefixWord ++ tailWord_811093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811093).length < 2 ^ (prefixWord ++ tailWord_811093).sum := by decide
  have hdescent : baseEnd_811093 < baseStart_811093 := by decide
  rcases family_descends (prefixWord ++ tailWord_811093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811094 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_811094 : Nat := 118140960795 + 811094 * 2 ^ 59
def prefixEnd_811094 : Nat := 4983230072969 + 3 ^ 40 * 811094 * 2
def baseEnd_811094 : Nat := 416481077977954824694853

theorem tailTrace_811094 : CollatzResearch.WordTrace tailWord_811094 prefixEnd_811094 416481077977954824694853 := by
  unfold tailWord_811094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848939282722027291991521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19722019015701624447909557 1848939282722027291991521)
  ·
    refine ⟨1386704462041520468993641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1848939282722027291991521 1386704462041520468993641)
    ·
      refine ⟨1040028346531140351745231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1386704462041520468993641 1040028346531140351745231)
      ·
        refine ⟨1560042519796710527617847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040028346531140351745231 1560042519796710527617847)
        ·
          refine ⟨2340063779695065791426771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560042519796710527617847 2340063779695065791426771)
          ·
            refine ⟨3510095669542598687140157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340063779695065791426771 3510095669542598687140157)
            ·
              refine ⟨1316285876078474507677559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3510095669542598687140157 1316285876078474507677559)
              ·
                refine ⟨1974428814117711761516339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316285876078474507677559 1974428814117711761516339)
                ·
                  refine ⟨2961643221176567642274509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974428814117711761516339 2961643221176567642274509)
                  ·
                    refine ⟨1110616207941212865852941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2961643221176567642274509 1110616207941212865852941)
                    ·
                      refine ⟨416481077977954824694853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1110616207941212865852941 416481077977954824694853)
                      ·
                        rfl

theorem cell23_811094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_811094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811094 prefixEnd_811094 := by exact prefixLift 811094
  have htrace : WordTrace (prefixWord ++ tailWord_811094) baseStart_811094 baseEnd_811094 := by
    simpa [prefixWord, tailWord_811094, baseEnd_811094] using wordTrace_append hprefix tailTrace_811094
  have hstable : (prefixWord ++ tailWord_811094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811094).length < 2 ^ (prefixWord ++ tailWord_811094).sum := by decide
  have hdescent : baseEnd_811094 < baseStart_811094 := by decide
  rcases family_descends (prefixWord ++ tailWord_811094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811117 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_811117 : Nat := 118140960795 + 811117 * 2 ^ 59
def prefixEnd_811117 : Nat := 4983230072969 + 3 ^ 40 * 811117 * 2
def baseEnd_811117 : Nat := 416492888033008234707247

theorem tailTrace_811117 : CollatzResearch.WordTrace tailWord_811117 prefixEnd_811117 416492888033008234707247 := by
  unfold tailWord_811117
  simp only [CollatzResearch.WordTrace]
  refine ⟨29583867402469111599951605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19722578268312741066634403 29583867402469111599951605)
  ·
    refine ⟨2773487568981479212495463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29583867402469111599951605 2773487568981479212495463)
    ·
      refine ⟨4160231353472218818743195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2773487568981479212495463 4160231353472218818743195)
      ·
        refine ⟨6240347030208328228114793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4160231353472218818743195 6240347030208328228114793)
        ·
          refine ⟨4680260272656246171086095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6240347030208328228114793 4680260272656246171086095)
          ·
            refine ⟨7020390408984369256629143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680260272656246171086095 7020390408984369256629143)
            ·
              refine ⟨10530585613476553884943715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7020390408984369256629143 10530585613476553884943715)
              ·
                refine ⟨15795878420214830827415573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10530585613476553884943715 15795878420214830827415573)
                ·
                  refine ⟨740431800947570195035105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15795878420214830827415573 740431800947570195035105)
                  ·
                    refine ⟨555323850710677646276329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 740431800947570195035105 555323850710677646276329)
                    ·
                      refine ⟨416492888033008234707247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 555323850710677646276329 416492888033008234707247)
                      ·
                        rfl

theorem cell23_811117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_811117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811117 prefixEnd_811117 := by exact prefixLift 811117
  have htrace : WordTrace (prefixWord ++ tailWord_811117) baseStart_811117 baseEnd_811117 := by
    simpa [prefixWord, tailWord_811117, baseEnd_811117] using wordTrace_append hprefix tailTrace_811117
  have hstable : (prefixWord ++ tailWord_811117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811117).length < 2 ^ (prefixWord ++ tailWord_811117).sum := by decide
  have hdescent : baseEnd_811117 < baseStart_811117 := by decide
  rcases family_descends (prefixWord ++ tailWord_811117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811193 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_811193 : Nat := 118140960795 + 811193 * 2 ^ 59
def prefixEnd_811193 : Nat := 4983230072969 + 3 ^ 40 * 811193 * 2
def baseEnd_811193 : Nat := 416531912562749937356897

theorem tailTrace_811193 : CollatzResearch.WordTrace tailWord_811193 prefixEnd_811193 416531912562749937356897 := by
  unfold tailWord_811193
  simp only [CollatzResearch.WordTrace]
  refine ⟨29586639350193776579718233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19724426233462517719812155 29586639350193776579718233)
  ·
    refine ⟨22189979512645332434788675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29586639350193776579718233 22189979512645332434788675)
    ·
      refine ⟨33284969268967998652183013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22189979512645332434788675 33284969268967998652183013)
      ·
        refine ⟨6240931737931499747284315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33284969268967998652183013 6240931737931499747284315)
        ·
          refine ⟨9361397606897249620926473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6240931737931499747284315 9361397606897249620926473)
          ·
            refine ⟨7021048205172937215694855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9361397606897249620926473 7021048205172937215694855)
            ·
              refine ⟨10531572307759405823542283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021048205172937215694855 10531572307759405823542283)
              ·
                refine ⟨15797358461639108735313425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10531572307759405823542283 15797358461639108735313425)
                ·
                  refine ⟨11848018846229331551485069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15797358461639108735313425 11848018846229331551485069)
                  ·
                    refine ⟨4443007067335999331806901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11848018846229331551485069 4443007067335999331806901)
                    ·
                      refine ⟨416531912562749937356897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4443007067335999331806901 416531912562749937356897)
                      ·
                        rfl

theorem cell23_811193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_811193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811193 prefixEnd_811193 := by exact prefixLift 811193
  have htrace : WordTrace (prefixWord ++ tailWord_811193) baseStart_811193 baseEnd_811193 := by
    simpa [prefixWord, tailWord_811193, baseEnd_811193] using wordTrace_append hprefix tailTrace_811193
  have hstable : (prefixWord ++ tailWord_811193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811193).length < 2 ^ (prefixWord ++ tailWord_811193).sum := by decide
  have hdescent : baseEnd_811193 < baseStart_811193 := by decide
  rcases family_descends (prefixWord ++ tailWord_811193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811210 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_811210 : Nat := 118140960795 + 811210 * 2 ^ 59
def prefixEnd_811210 : Nat := 4983230072969 + 3 ^ 40 * 811210 * 2
def baseEnd_811210 : Nat := 416540641733876370844319

theorem tailTrace_811210 : CollatzResearch.WordTrace tailWord_811210 prefixEnd_811210 416540641733876370844319 := by
  unfold tailWord_811210
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396814847783047120771771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19724839594088125655391389 7396814847783047120771771)
  ·
    refine ⟨11095222271674570681157657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7396814847783047120771771 11095222271674570681157657)
    ·
      refine ⟨8321416703755928010868243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11095222271674570681157657 8321416703755928010868243)
      ·
        refine ⟨12482125055633892016302365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8321416703755928010868243 12482125055633892016302365)
        ·
          refine ⟨4680796895862709506113387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12482125055633892016302365 4680796895862709506113387)
          ·
            refine ⟨7021195343794064259170081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680796895862709506113387 7021195343794064259170081)
            ·
              refine ⟨5265896507845548194377561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7021195343794064259170081 5265896507845548194377561)
              ·
                refine ⟨3949422380884161145783171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5265896507845548194377561 3949422380884161145783171)
                ·
                  refine ⟨5924133571326241718674757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3949422380884161145783171 5924133571326241718674757)
                  ·
                    refine ⟨1110775044623670322251517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5924133571326241718674757 1110775044623670322251517)
                    ·
                      refine ⟨416540641733876370844319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1110775044623670322251517 416540641733876370844319)
                      ·
                        rfl

theorem cell23_811210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_811210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811210 prefixEnd_811210 := by exact prefixLift 811210
  have htrace : WordTrace (prefixWord ++ tailWord_811210) baseStart_811210 baseEnd_811210 := by
    simpa [prefixWord, tailWord_811210, baseEnd_811210] using wordTrace_append hprefix tailTrace_811210
  have hstable : (prefixWord ++ tailWord_811210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811210).length < 2 ^ (prefixWord ++ tailWord_811210).sum := by decide
  have hdescent : baseEnd_811210 < baseStart_811210 := by decide
  rcases family_descends (prefixWord ++ tailWord_811210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811247 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 6]
def baseStart_811247 : Nat := 118140960795 + 811247 * 2 ^ 59
def prefixEnd_811247 : Nat := 4983230072969 + 3 ^ 40 * 811247 * 2
def baseEnd_811247 : Nat := 46284404502010302897961

theorem tailTrace_811247 : CollatzResearch.WordTrace tailWord_811247 prefixEnd_811247 46284404502010302897961 := by
  unfold tailWord_811247
  simp only [CollatzResearch.WordTrace]
  refine ⟨29588608891998143802183995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19725739261332095868122663 29588608891998143802183995)
  ·
    refine ⟨44382913337997215703275993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29588608891998143802183995 44382913337997215703275993)
    ·
      refine ⟨33287185003497911777456995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44382913337997215703275993 33287185003497911777456995)
      ·
        refine ⟨49930777505246867666185493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33287185003497911777456995 49930777505246867666185493)
        ·
          refine ⟨2340505195558446921852445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49930777505246867666185493 2340505195558446921852445)
          ·
            refine ⟨877689448334417595694667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2340505195558446921852445 877689448334417595694667)
            ·
              refine ⟨1316534172501626393542001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877689448334417595694667 1316534172501626393542001)
              ·
                refine ⟨987400629376219795156501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316534172501626393542001 987400629376219795156501)
                ·
                  refine ⟨46284404502010302897961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 987400629376219795156501 46284404502010302897961)
                  ·
                    rfl

theorem cell23_811247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 6].length) (baseStart_811247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811247 prefixEnd_811247 := by exact prefixLift 811247
  have htrace : WordTrace (prefixWord ++ tailWord_811247) baseStart_811247 baseEnd_811247 := by
    simpa [prefixWord, tailWord_811247, baseEnd_811247] using wordTrace_append hprefix tailTrace_811247
  have hstable : (prefixWord ++ tailWord_811247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811247).length < 2 ^ (prefixWord ++ tailWord_811247).sum := by decide
  have hdescent : baseEnd_811247 < baseStart_811247 := by decide
  rcases family_descends (prefixWord ++ tailWord_811247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811250 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_811250 : Nat := 118140960795 + 811250 * 2 ^ 59
def prefixEnd_811250 : Nat := 4983230072969 + 3 ^ 40 * 811250 * 2
def baseEnd_811250 : Nat := 416561180960056214344135

theorem tailTrace_811250 : CollatzResearch.WordTrace tailWord_811250 prefixEnd_811250 416561180960056214344135 := by
  unfold tailWord_811250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7397179577746818828635801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19725812207324850209695469 7397179577746818828635801)
  ·
    refine ⟨5547884683310114121476851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7397179577746818828635801 5547884683310114121476851)
    ·
      refine ⟨8321827024965171182215277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5547884683310114121476851 8321827024965171182215277)
      ·
        refine ⟨3120685134361939193330729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8321827024965171182215277 3120685134361939193330729)
        ·
          refine ⟨2340513850771454394998047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3120685134361939193330729 2340513850771454394998047)
          ·
            refine ⟨3510770776157181592497071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340513850771454394998047 3510770776157181592497071)
            ·
              refine ⟨5266156164235772388745607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3510770776157181592497071 5266156164235772388745607)
              ·
                refine ⟨7899234246353658583118411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5266156164235772388745607 7899234246353658583118411)
                ·
                  refine ⟨11848851369530487874677617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7899234246353658583118411 11848851369530487874677617)
                  ·
                    refine ⟨8886638527147865906008213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11848851369530487874677617 8886638527147865906008213)
                    ·
                      refine ⟨416561180960056214344135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8886638527147865906008213 416561180960056214344135)
                      ·
                        rfl

theorem cell23_811250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_811250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811250 prefixEnd_811250 := by exact prefixLift 811250
  have htrace : WordTrace (prefixWord ++ tailWord_811250) baseStart_811250 baseEnd_811250 := by
    simpa [prefixWord, tailWord_811250, baseEnd_811250] using wordTrace_append hprefix tailTrace_811250
  have hstable : (prefixWord ++ tailWord_811250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811250).length < 2 ^ (prefixWord ++ tailWord_811250).sum := by decide
  have hdescent : baseEnd_811250 < baseStart_811250 := by decide
  rcases family_descends (prefixWord ++ tailWord_811250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811297 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_811297 : Nat := 118140960795 + 811297 * 2 ^ 59
def prefixEnd_811297 : Nat := 4983230072969 + 3 ^ 40 * 811297 * 2
def baseEnd_811297 : Nat := 416585314550817530456419

theorem tailTrace_811297 : CollatzResearch.WordTrace tailWord_811297 prefixEnd_811297 416585314550817530456419 := by
  unfold tailWord_811297
  simp only [CollatzResearch.WordTrace]
  refine ⟨29590432541817002341504145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19726955027878001561002763 29590432541817002341504145)
  ·
    refine ⟨22192824406362751756128109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29590432541817002341504145 22192824406362751756128109)
    ·
      refine ⟨8322309152386031908548041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22192824406362751756128109 8322309152386031908548041)
      ·
        refine ⟨6241731864289523931411031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8322309152386031908548041 6241731864289523931411031)
        ·
          refine ⟨9362597796434285897116547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6241731864289523931411031 9362597796434285897116547)
          ·
            refine ⟨14043896694651428845674821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9362597796434285897116547 14043896694651428845674821)
            ·
              refine ⟨2633230630247142908564029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14043896694651428845674821 2633230630247142908564029)
              ·
                refine ⟨987461486342678590711511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2633230630247142908564029 987461486342678590711511)
                ·
                  refine ⟨1481192229514017886067267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987461486342678590711511 1481192229514017886067267)
                  ·
                    refine ⟨2221788344271026829100901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1481192229514017886067267 2221788344271026829100901)
                    ·
                      refine ⟨416585314550817530456419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2221788344271026829100901 416585314550817530456419)
                      ·
                        rfl

theorem cell23_811297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_811297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811297 prefixEnd_811297 := by exact prefixLift 811297
  have htrace : WordTrace (prefixWord ++ tailWord_811297) baseStart_811297 baseEnd_811297 := by
    simpa [prefixWord, tailWord_811297, baseEnd_811297] using wordTrace_append hprefix tailTrace_811297
  have hstable : (prefixWord ++ tailWord_811297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811297).length < 2 ^ (prefixWord ++ tailWord_811297).sum := by decide
  have hdescent : baseEnd_811297 < baseStart_811297 := by decide
  rcases family_descends (prefixWord ++ tailWord_811297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811317 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_811317 : Nat := 118140960795 + 811317 * 2 ^ 59
def prefixEnd_811317 : Nat := 4983230072969 + 3 ^ 40 * 811317 * 2
def baseEnd_811317 : Nat := 416595584163907452206327

theorem tailTrace_811317 : CollatzResearch.WordTrace tailWord_811317 prefixEnd_811317 416595584163907452206327 := by
  unfold tailWord_811317
  simp only [CollatzResearch.WordTrace]
  refine ⟨29591162001744545757232205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19727441334496363838154803 29591162001744545757232205)
  ·
    refine ⟨11096685750654204658962077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29591162001744545757232205 11096685750654204658962077)
    ·
      refine ⟨4161257156495326747110779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11096685750654204658962077 4161257156495326747110779)
      ·
        refine ⟨6241885734742990120666169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4161257156495326747110779 6241885734742990120666169)
        ·
          refine ⟨4681414301057242590499627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6241885734742990120666169 4681414301057242590499627)
          ·
            refine ⟨7022121451585863885749441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681414301057242590499627 7022121451585863885749441)
            ·
              refine ⟨5266591088689397914312081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7022121451585863885749441 5266591088689397914312081)
              ·
                refine ⟨3949943316517048435734061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5266591088689397914312081 3949943316517048435734061)
                ·
                  refine ⟨1481228743693893163400273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3949943316517048435734061 1481228743693893163400273)
                  ·
                    refine ⟨1110921557770419872550205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1481228743693893163400273 1110921557770419872550205)
                    ·
                      refine ⟨416595584163907452206327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1110921557770419872550205 416595584163907452206327)
                      ·
                        rfl

theorem cell23_811317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_811317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811317 prefixEnd_811317 := by exact prefixLift 811317
  have htrace : WordTrace (prefixWord ++ tailWord_811317) baseStart_811317 baseEnd_811317 := by
    simpa [prefixWord, tailWord_811317, baseEnd_811317] using wordTrace_append hprefix tailTrace_811317
  have hstable : (prefixWord ++ tailWord_811317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811317).length < 2 ^ (prefixWord ++ tailWord_811317).sum := by decide
  have hdescent : baseEnd_811317 < baseStart_811317 := by decide
  rcases family_descends (prefixWord ++ tailWord_811317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811347 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 4, 1, 3]
def baseStart_811347 : Nat := 118140960795 + 811347 * 2 ^ 59
def prefixEnd_811347 : Nat := 4983230072969 + 3 ^ 40 * 811347 * 2
def baseEnd_811347 : Nat := 416610988583542334831189

theorem tailTrace_811347 : CollatzResearch.WordTrace tailWord_811347 prefixEnd_811347 416610988583542334831189 := by
  unfold tailWord_811347
  simp only [CollatzResearch.WordTrace]
  refine ⟨29592256191635860880824295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19728170794423907253882863 29592256191635860880824295)
  ·
    refine ⟨44388384287453791321236443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29592256191635860880824295 44388384287453791321236443)
    ·
      refine ⟨66582576431180686981854665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44388384287453791321236443 66582576431180686981854665)
      ·
        refine ⟨49936932323385515236390999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66582576431180686981854665 49936932323385515236390999)
        ·
          refine ⟨74905398485078272854586499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49936932323385515236390999 74905398485078272854586499)
          ·
            refine ⟨112358097727617409281879749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74905398485078272854586499 112358097727617409281879749)
            ·
              refine ⟨21067143323928264240352453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112358097727617409281879749 21067143323928264240352453)
              ·
                refine ⟨3950089373236549545066085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21067143323928264240352453 3950089373236549545066085)
                ·
                  refine ⟨740641757481853039699891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3950089373236549545066085 740641757481853039699891)
                  ·
                    refine ⟨1110962636222779559549837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 740641757481853039699891 1110962636222779559549837)
                    ·
                      refine ⟨416610988583542334831189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1110962636222779559549837 416610988583542334831189)
                      ·
                        rfl

theorem cell23_811347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 1, 3].length) (baseStart_811347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811347 prefixEnd_811347 := by exact prefixLift 811347
  have htrace : WordTrace (prefixWord ++ tailWord_811347) baseStart_811347 baseEnd_811347 := by
    simpa [prefixWord, tailWord_811347, baseEnd_811347] using wordTrace_append hprefix tailTrace_811347
  have hstable : (prefixWord ++ tailWord_811347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811347).length < 2 ^ (prefixWord ++ tailWord_811347).sum := by decide
  have hdescent : baseEnd_811347 < baseStart_811347 := by decide
  rcases family_descends (prefixWord ++ tailWord_811347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811365 : List Nat := [1, 3, 1, 3, 1, 5, 2, 2, 1, 2, 2]
def baseStart_811365 : Nat := 118140960795 + 811365 * 2 ^ 59
def prefixEnd_811365 : Nat := 4983230072969 + 3 ^ 40 * 811365 * 2
def baseEnd_811365 : Nat := 416620231235323264406107

theorem tailTrace_811365 : CollatzResearch.WordTrace tailWord_811365 prefixEnd_811365 416620231235323264406107 := by
  unfold tailWord_811365
  simp only [CollatzResearch.WordTrace]
  refine ⟨29592912705570649954979549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19728608470380433303319699 29592912705570649954979549)
  ·
    refine ⟨11097342264588993733117331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29592912705570649954979549 11097342264588993733117331)
    ·
      refine ⟨16646013396883490599675997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11097342264588993733117331 16646013396883490599675997)
      ·
        refine ⟨6242255023831308974878499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16646013396883490599675997 6242255023831308974878499)
        ·
          refine ⟨9363382535746963462317749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6242255023831308974878499 9363382535746963462317749)
          ·
            refine ⟨877817112726277824592289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9363382535746963462317749 877817112726277824592289)
            ·
              refine ⟨658362834544708368444217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877817112726277824592289 658362834544708368444217)
              ·
                refine ⟨493772125908531276333163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658362834544708368444217 493772125908531276333163)
                ·
                  refine ⟨740658188862796914499745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493772125908531276333163 740658188862796914499745)
                  ·
                    refine ⟨555493641647097685874809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 740658188862796914499745 555493641647097685874809)
                    ·
                      refine ⟨416620231235323264406107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 555493641647097685874809 416620231235323264406107)
                      ·
                        rfl

theorem cell23_811365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_811365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811365 prefixEnd_811365 := by exact prefixLift 811365
  have htrace : WordTrace (prefixWord ++ tailWord_811365) baseStart_811365 baseEnd_811365 := by
    simpa [prefixWord, tailWord_811365, baseEnd_811365] using wordTrace_append hprefix tailTrace_811365
  have hstable : (prefixWord ++ tailWord_811365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811365).length < 2 ^ (prefixWord ++ tailWord_811365).sum := by decide
  have hdescent : baseEnd_811365 < baseStart_811365 := by decide
  rcases family_descends (prefixWord ++ tailWord_811365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811381 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_811381 : Nat := 118140960795 + 811381 * 2 ^ 59
def prefixEnd_811381 : Nat := 4983230072969 + 3 ^ 40 * 811381 * 2
def baseEnd_811381 : Nat := 416628446925795201806033

theorem tailTrace_811381 : CollatzResearch.WordTrace tailWord_811381 prefixEnd_811381 416628446925795201806033 := by
  unfold tailWord_811381
  simp only [CollatzResearch.WordTrace]
  refine ⟨29593496273512684687561997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19728997515675123125041331 29593496273512684687561997)
  ·
    refine ⟨11097561102567256757835749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29593496273512684687561997 11097561102567256757835749)
    ·
      refine ⟨2080792706731360642094203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11097561102567256757835749 2080792706731360642094203)
      ·
        refine ⟨3121189060097040963141305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2080792706731360642094203 3121189060097040963141305)
        ·
          refine ⟨2340891795072780722355979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3121189060097040963141305 2340891795072780722355979)
          ·
            refine ⟨3511337692609171083533969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340891795072780722355979 3511337692609171083533969)
            ·
              refine ⟨2633503269456878312650477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511337692609171083533969 2633503269456878312650477)
              ·
                refine ⟨987563726046329367243929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2633503269456878312650477 987563726046329367243929)
                ·
                  refine ⟨740672794534747025432947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 987563726046329367243929 740672794534747025432947)
                  ·
                    refine ⟨1111009191802120538149421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 740672794534747025432947 1111009191802120538149421)
                    ·
                      refine ⟨416628446925795201806033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1111009191802120538149421 416628446925795201806033)
                      ·
                        rfl

theorem cell23_811381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_811381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811381 prefixEnd_811381 := by exact prefixLift 811381
  have htrace : WordTrace (prefixWord ++ tailWord_811381) baseStart_811381 baseEnd_811381 := by
    simpa [prefixWord, tailWord_811381, baseEnd_811381] using wordTrace_append hprefix tailTrace_811381
  have hstable : (prefixWord ++ tailWord_811381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811381).length < 2 ^ (prefixWord ++ tailWord_811381).sum := by decide
  have hdescent : baseEnd_811381 < baseStart_811381 := by decide
  rcases family_descends (prefixWord ++ tailWord_811381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811404 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 1, 4, 2]
def baseStart_811404 : Nat := 118140960795 + 811404 * 2 ^ 59
def prefixEnd_811404 : Nat := 4983230072969 + 3 ^ 40 * 811404 * 2
def baseEnd_811404 : Nat := 416640256980848611818427

theorem tailTrace_811404 : CollatzResearch.WordTrace tailWord_811404 prefixEnd_811404 416640256980848611818427 := by
  unfold tailWord_811404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14797167576214679807824633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19729556768286239743766177 14797167576214679807824633)
  ·
    refine ⟨11097875682161009855868475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14797167576214679807824633 11097875682161009855868475)
    ·
      refine ⟨16646813523241514783802713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11097875682161009855868475 16646813523241514783802713)
      ·
        refine ⟨12485110142431136087852035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16646813523241514783802713 12485110142431136087852035)
        ·
          refine ⟨18727665213646704131778053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12485110142431136087852035 18727665213646704131778053)
          ·
            refine ⟨3511437227558757024708385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18727665213646704131778053 3511437227558757024708385)
            ·
              refine ⟨2633577920669067768531289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511437227558757024708385 2633577920669067768531289)
              ·
                refine ⟨1975183440501800826398467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633577920669067768531289 1975183440501800826398467)
                ·
                  refine ⟨2962775160752701239597701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975183440501800826398467 2962775160752701239597701)
                  ·
                    refine ⟨555520342641131482424569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2962775160752701239597701 555520342641131482424569)
                    ·
                      refine ⟨416640256980848611818427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 555520342641131482424569 416640256980848611818427)
                      ·
                        rfl

theorem cell23_811404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_811404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811404 prefixEnd_811404 := by exact prefixLift 811404
  have htrace : WordTrace (prefixWord ++ tailWord_811404) baseStart_811404 baseEnd_811404 := by
    simpa [prefixWord, tailWord_811404, baseEnd_811404] using wordTrace_append hprefix tailTrace_811404
  have hstable : (prefixWord ++ tailWord_811404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811404).length < 2 ^ (prefixWord ++ tailWord_811404).sum := by decide
  have hdescent : baseEnd_811404 < baseStart_811404 := by decide
  rcases family_descends (prefixWord ++ tailWord_811404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811427 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 7]
def baseStart_811427 : Nat := 118140960795 + 811427 * 2 ^ 59
def prefixEnd_811427 : Nat := 4983230072969 + 3 ^ 40 * 811427 * 2
def baseEnd_811427 : Nat := 46294674115100224647869

theorem tailTrace_811427 : CollatzResearch.WordTrace tailWord_811427 prefixEnd_811427 46294674115100224647869 := by
  unfold tailWord_811427
  simp only [CollatzResearch.WordTrace]
  refine ⟨29595174031346034543736535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19730116020897356362491023 29595174031346034543736535)
  ·
    refine ⟨44392761047019051815604803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29595174031346034543736535 44392761047019051815604803)
    ·
      refine ⟨66589141570528577723407205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44392761047019051815604803 66589141570528577723407205)
      ·
        refine ⟨12485464044474108323138851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66589141570528577723407205 12485464044474108323138851)
        ·
          refine ⟨18728196066711162484708277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12485464044474108323138851 18728196066711162484708277)
          ·
            refine ⟨1755768381254171482941401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18728196066711162484708277 1755768381254171482941401)
            ·
              refine ⟨1316826285940628612206051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1755768381254171482941401 1316826285940628612206051)
              ·
                refine ⟨1975239428910942918309077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316826285940628612206051 1975239428910942918309077)
                ·
                  refine ⟨46294674115100224647869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1975239428910942918309077 46294674115100224647869)
                  ·
                    rfl

theorem cell23_811427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 7].length) (baseStart_811427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811427 prefixEnd_811427 := by exact prefixLift 811427
  have htrace : WordTrace (prefixWord ++ tailWord_811427) baseStart_811427 baseEnd_811427 := by
    simpa [prefixWord, tailWord_811427, baseEnd_811427] using wordTrace_append hprefix tailTrace_811427
  have hstable : (prefixWord ++ tailWord_811427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811427).length < 2 ^ (prefixWord ++ tailWord_811427).sum := by decide
  have hdescent : baseEnd_811427 < baseStart_811427 := by decide
  rcases family_descends (prefixWord ++ tailWord_811427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811478 : List Nat := [5, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_811478 : Nat := 118140960795 + 811478 * 2 ^ 59
def prefixEnd_811478 : Nat := 4983230072969 + 3 ^ 40 * 811478 * 2
def baseEnd_811478 : Nat := 46297583838809035810343

theorem tailTrace_811478 : CollatzResearch.WordTrace tailWord_811478 prefixEnd_811478 46297583838809035810343 := by
  unfold tailWord_811478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1849814634635079390865193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19731356102774180169228725 1849814634635079390865193)
  ·
    refine ⟨1387360975976309543148895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1849814634635079390865193 1387360975976309543148895)
    ·
      refine ⟨2081041463964464314723343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387360975976309543148895 2081041463964464314723343)
      ·
        refine ⟨3121562195946696472085015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081041463964464314723343 3121562195946696472085015)
        ·
          refine ⟨4682343293920044708127523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121562195946696472085015 4682343293920044708127523)
          ·
            refine ⟨7023514940880067062191285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682343293920044708127523 7023514940880067062191285)
            ·
              refine ⟨658454525707506287080433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7023514940880067062191285 658454525707506287080433)
              ·
                refine ⟨493840894280629715310325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658454525707506287080433 493840894280629715310325)
                ·
                  refine ⟨46297583838809035810343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 493840894280629715310325 46297583838809035810343)
                  ·
                    rfl

theorem cell23_811478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_811478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811478 prefixEnd_811478 := by exact prefixLift 811478
  have htrace : WordTrace (prefixWord ++ tailWord_811478) baseStart_811478 baseEnd_811478 := by
    simpa [prefixWord, tailWord_811478, baseEnd_811478] using wordTrace_append hprefix tailTrace_811478
  have hstable : (prefixWord ++ tailWord_811478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811478).length < 2 ^ (prefixWord ++ tailWord_811478).sum := by decide
  have hdescent : baseEnd_811478 < baseStart_811478 := by decide
  rcases family_descends (prefixWord ++ tailWord_811478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811497 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 1, 4, 3]
def baseStart_811497 : Nat := 118140960795 + 811497 * 2 ^ 59
def prefixEnd_811497 : Nat := 4983230072969 + 3 ^ 40 * 811497 * 2
def baseEnd_811497 : Nat := 416688010681716747955499

theorem tailTrace_811497 : CollatzResearch.WordTrace tailWord_811497 prefixEnd_811497 416688010681716747955499 := by
  unfold tailWord_811497
  simp only [CollatzResearch.WordTrace]
  refine ⟨29597727141092436498784745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19731818094061624332523163 29597727141092436498784745)
  ·
    refine ⟨22198295355819327374088559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29597727141092436498784745 22198295355819327374088559)
    ·
      refine ⟨33297443033728991061132839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22198295355819327374088559 33297443033728991061132839)
      ·
        refine ⟨49946164550593486591699259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33297443033728991061132839 49946164550593486591699259)
        ·
          refine ⟨74919246825890229887548889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49946164550593486591699259 74919246825890229887548889)
          ·
            refine ⟨56189435119417672415661667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74919246825890229887548889 56189435119417672415661667)
            ·
              refine ⟨84284152679126508623492501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56189435119417672415661667 84284152679126508623492501)
              ·
                refine ⟨3950819656834055091726211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84284152679126508623492501 3950819656834055091726211)
                ·
                  refine ⟨5926229485251082637589317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950819656834055091726211 5926229485251082637589317)
                  ·
                    refine ⟨1111168028484577994547997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5926229485251082637589317 1111168028484577994547997)
                    ·
                      refine ⟨416688010681716747955499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1111168028484577994547997 416688010681716747955499)
                      ·
                        rfl

theorem cell23_811497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4, 3].length) (baseStart_811497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811497 prefixEnd_811497 := by exact prefixLift 811497
  have htrace : WordTrace (prefixWord ++ tailWord_811497) baseStart_811497 baseEnd_811497 := by
    simpa [prefixWord, tailWord_811497, baseEnd_811497] using wordTrace_append hprefix tailTrace_811497
  have hstable : (prefixWord ++ tailWord_811497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811497).length < 2 ^ (prefixWord ++ tailWord_811497).sum := by decide
  have hdescent : baseEnd_811497 < baseStart_811497 := by decide
  rcases family_descends (prefixWord ++ tailWord_811497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811534 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_811534 : Nat := 118140960795 + 811534 * 2 ^ 59
def prefixEnd_811534 : Nat := 4983230072969 + 3 ^ 40 * 811534 * 2
def baseEnd_811534 : Nat := 46300778829548122576981

theorem tailTrace_811534 : CollatzResearch.WordTrace tailWord_811534 prefixEnd_811534 46300778829548122576981 := by
  unfold tailWord_811534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3699884580244798977235207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19732717761305594545254437 3699884580244798977235207)
  ·
    refine ⟨5549826870367198465852811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3699884580244798977235207 5549826870367198465852811)
    ·
      refine ⟨8324740305550797698779217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5549826870367198465852811 8324740305550797698779217)
      ·
        refine ⟨6243555229163098274084413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8324740305550797698779217 6243555229163098274084413)
        ·
          refine ⟨2341333210936161852781655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6243555229163098274084413 2341333210936161852781655)
          ·
            refine ⟨3511999816404242779172483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341333210936161852781655 3511999816404242779172483)
            ·
              refine ⟨5267999724606364168758725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3511999816404242779172483 5267999724606364168758725)
              ·
                refine ⟨987749948363693281642261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5267999724606364168758725 987749948363693281642261)
                ·
                  refine ⟨46300778829548122576981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 987749948363693281642261 46300778829548122576981)
                  ·
                    rfl

theorem cell23_811534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_811534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811534 prefixEnd_811534 := by exact prefixLift 811534
  have htrace : WordTrace (prefixWord ++ tailWord_811534) baseStart_811534 baseEnd_811534 := by
    simpa [prefixWord, tailWord_811534, baseEnd_811534] using wordTrace_append hprefix tailTrace_811534
  have hstable : (prefixWord ++ tailWord_811534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811534).length < 2 ^ (prefixWord ++ tailWord_811534).sum := by decide
  have hdescent : baseEnd_811534 < baseStart_811534 := by decide
  rcases family_descends (prefixWord ++ tailWord_811534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811565 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_811565 : Nat := 118140960795 + 811565 * 2 ^ 59
def prefixEnd_811565 : Nat := 4983230072969 + 3 ^ 40 * 811565 * 2
def baseEnd_811565 : Nat := 416722927366222481905187

theorem tailTrace_811565 : CollatzResearch.WordTrace tailWord_811565 prefixEnd_811565 416722927366222481905187 := by
  unfold tailWord_811565
  simp only [CollatzResearch.WordTrace]
  refine ⟨29600207304846084112260149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19733471536564056074840099 29600207304846084112260149)
  ·
    refine ⟨2775019434829320385524389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29600207304846084112260149 2775019434829320385524389)
    ·
      refine ⟨520316144030497572285823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2775019434829320385524389 520316144030497572285823)
      ·
        refine ⟨780474216045746358428735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520316144030497572285823 780474216045746358428735)
        ·
          refine ⟨1170711324068619537643103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780474216045746358428735 1170711324068619537643103)
          ·
            refine ⟨1756066986102929306464655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170711324068619537643103 1756066986102929306464655)
            ·
              refine ⟨2634100479154393959696983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756066986102929306464655 2634100479154393959696983)
              ·
                refine ⟨3951150718731590939545475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634100479154393959696983 3951150718731590939545475)
                ·
                  refine ⟨5926726078097386409318213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3951150718731590939545475 5926726078097386409318213)
                  ·
                    refine ⟨1111261139643259951747165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5926726078097386409318213 1111261139643259951747165)
                    ·
                      refine ⟨416722927366222481905187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1111261139643259951747165 416722927366222481905187)
                      ·
                        rfl

theorem cell23_811565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_811565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811565 prefixEnd_811565 := by exact prefixLift 811565
  have htrace : WordTrace (prefixWord ++ tailWord_811565) baseStart_811565 baseEnd_811565 := by
    simpa [prefixWord, tailWord_811565, baseEnd_811565] using wordTrace_append hprefix tailTrace_811565
  have hstable : (prefixWord ++ tailWord_811565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811565).length < 2 ^ (prefixWord ++ tailWord_811565).sum := by decide
  have hdescent : baseEnd_811565 < baseStart_811565 := by decide
  rcases family_descends (prefixWord ++ tailWord_811565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811572 : List Nat := [2, 5, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_811572 : Nat := 118140960795 + 811572 * 2 ^ 59
def prefixEnd_811572 : Nat := 4983230072969 + 3 ^ 40 * 811572 * 2
def baseEnd_811572 : Nat := 138908840576934651505885

theorem tailTrace_811572 : CollatzResearch.WordTrace tailWord_811572 prefixEnd_811572 138908840576934651505885 := by
  unfold tailWord_811572
  simp only [CollatzResearch.WordTrace]
  refine ⟨14800231307910362153882485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19733641743880482871843313 14800231307910362153882485)
  ·
    refine ⟨1387521685116596451926483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14800231307910362153882485 1387521685116596451926483)
    ·
      refine ⟨2081282527674894677889725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387521685116596451926483 2081282527674894677889725)
      ·
        refine ⟨780480947878085504208647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2081282527674894677889725 780480947878085504208647)
        ·
          refine ⟨1170721421817128256312971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780480947878085504208647 1170721421817128256312971)
          ·
            refine ⟨1756082132725692384469457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170721421817128256312971 1756082132725692384469457)
            ·
              refine ⟨1317061599544269288352093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1756082132725692384469457 1317061599544269288352093)
              ·
                refine ⟨493898099829100983132035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1317061599544269288352093 493898099829100983132035)
                ·
                  refine ⟨740847149743651474698053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493898099829100983132035 740847149743651474698053)
                  ·
                    refine ⟨138908840576934651505885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 740847149743651474698053 138908840576934651505885)
                    ·
                      rfl

theorem cell23_811572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_811572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811572 prefixEnd_811572 := by exact prefixLift 811572
  have htrace : WordTrace (prefixWord ++ tailWord_811572) baseStart_811572 baseEnd_811572 := by
    simpa [prefixWord, tailWord_811572, baseEnd_811572] using wordTrace_append hprefix tailTrace_811572
  have hstable : (prefixWord ++ tailWord_811572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811572).length < 2 ^ (prefixWord ++ tailWord_811572).sum := by decide
  have hdescent : baseEnd_811572 < baseStart_811572 := by decide
  rcases family_descends (prefixWord ++ tailWord_811572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811578 : List Nat := [3, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3]
def baseStart_811578 : Nat := 118140960795 + 811578 * 2 ^ 59
def prefixEnd_811578 : Nat := 4983230072969 + 3 ^ 40 * 811578 * 2
def baseEnd_811578 : Nat := 416729602614730931042627

theorem tailTrace_811578 : CollatzResearch.WordTrace tailWord_811578 prefixEnd_811578 416729602614730931042627 := by
  unfold tailWord_811578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7400170363449746833120847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19733787635865991554988925 7400170363449746833120847)
  ·
    refine ⟨11100255545174620249681271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7400170363449746833120847 11100255545174620249681271)
    ·
      refine ⟨16650383317761930374521907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11100255545174620249681271 16650383317761930374521907)
      ·
        refine ⟨24975574976642895561782861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16650383317761930374521907 24975574976642895561782861)
        ·
          refine ⟨9365840616241085835668573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24975574976642895561782861 9365840616241085835668573)
          ·
            refine ⟨3512190231090407188375715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9365840616241085835668573 3512190231090407188375715)
            ·
              refine ⟨5268285346635610782563573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512190231090407188375715 5268285346635610782563573)
              ·
                refine ⟨493901751247088510865335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5268285346635610782563573 493901751247088510865335)
                ·
                  refine ⟨740852626870632766298003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493901751247088510865335 740852626870632766298003)
                  ·
                    refine ⟨1111278940305949149447005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 740852626870632766298003 1111278940305949149447005)
                    ·
                      refine ⟨416729602614730931042627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1111278940305949149447005 416729602614730931042627)
                      ·
                        rfl

theorem cell23_811578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3].length) (baseStart_811578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811578 prefixEnd_811578 := by exact prefixLift 811578
  have htrace : WordTrace (prefixWord ++ tailWord_811578) baseStart_811578 baseEnd_811578 := by
    simpa [prefixWord, tailWord_811578, baseEnd_811578] using wordTrace_append hprefix tailTrace_811578
  have hstable : (prefixWord ++ tailWord_811578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811578).length < 2 ^ (prefixWord ++ tailWord_811578).sum := by decide
  have hdescent : baseEnd_811578 < baseStart_811578 := by decide
  rcases family_descends (prefixWord ++ tailWord_811578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811581 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_811581 : Nat := 118140960795 + 811581 * 2 ^ 59
def prefixEnd_811581 : Nat := 4983230072969 + 3 ^ 40 * 811581 * 2
def baseEnd_811581 : Nat := 138910381018898139768371

theorem tailTrace_811581 : CollatzResearch.WordTrace tailWord_811581 prefixEnd_811581 138910381018898139768371 := by
  unfold tailWord_811581
  simp only [CollatzResearch.WordTrace]
  refine ⟨29600790872788118844842597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19733860581858745896561731 29600790872788118844842597)
  ·
    refine ⟨5550148288647772283407987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29600790872788118844842597 5550148288647772283407987)
    ·
      refine ⟨8325222432971658425111981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5550148288647772283407987 8325222432971658425111981)
      ·
        refine ⟨3121958412364371909416993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8325222432971658425111981 3121958412364371909416993)
        ·
          refine ⟨2341468809273278932062745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3121958412364371909416993 2341468809273278932062745)
          ·
            refine ⟨1756101606954959199047059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2341468809273278932062745 1756101606954959199047059)
            ·
              refine ⟨2634152410432438798570589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756101606954959199047059 2634152410432438798570589)
              ·
                refine ⟨987807153912164549463971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2634152410432438798570589 987807153912164549463971)
                ·
                  refine ⟨1481710730868246824195957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987807153912164549463971 1481710730868246824195957)
                  ·
                    refine ⟨138910381018898139768371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1481710730868246824195957 138910381018898139768371)
                    ·
                      rfl

theorem cell23_811581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_811581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811581 prefixEnd_811581 := by exact prefixLift 811581
  have htrace : WordTrace (prefixWord ++ tailWord_811581) baseStart_811581 baseEnd_811581 := by
    simpa [prefixWord, tailWord_811581, baseEnd_811581] using wordTrace_append hprefix tailTrace_811581
  have hstable : (prefixWord ++ tailWord_811581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811581).length < 2 ^ (prefixWord ++ tailWord_811581).sum := by decide
  have hdescent : baseEnd_811581 < baseStart_811581 := by decide
  rcases family_descends (prefixWord ++ tailWord_811581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811587 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 5]
def baseStart_811587 : Nat := 118140960795 + 811587 * 2 ^ 59
def prefixEnd_811587 : Nat := 4983230072969 + 3 ^ 40 * 811587 * 2
def baseEnd_811587 : Nat := 416734223940621395830085

theorem tailTrace_811587 : CollatzResearch.WordTrace tailWord_811587 prefixEnd_811587 416734223940621395830085 := by
  unfold tailWord_811587
  simp only [CollatzResearch.WordTrace]
  refine ⟨29601009710766381869561015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19734006473844254579707343 29601009710766381869561015)
  ·
    refine ⟨44401514566149572804341523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29601009710766381869561015 44401514566149572804341523)
    ·
      refine ⟨66602271849224359206512285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44401514566149572804341523 66602271849224359206512285)
      ·
        refine ⟨24975851943459134702442107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66602271849224359206512285 24975851943459134702442107)
        ·
          refine ⟨37463777915188702053663161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24975851943459134702442107 37463777915188702053663161)
          ·
            refine ⟨28097833436391526540247371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37463777915188702053663161 28097833436391526540247371)
            ·
              refine ⟨42146750154587289810371057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28097833436391526540247371 42146750154587289810371057)
              ·
                refine ⟨31610062615940467357778293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42146750154587289810371057 31610062615940467357778293)
                ·
                  refine ⟨2963443370244418814791715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31610062615940467357778293 2963443370244418814791715)
                  ·
                    refine ⟨4445165055366628222187573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2963443370244418814791715 4445165055366628222187573)
                    ·
                      refine ⟨416734223940621395830085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4445165055366628222187573 416734223940621395830085)
                      ·
                        rfl

theorem cell23_811587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_811587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811587 prefixEnd_811587 := by exact prefixLift 811587
  have htrace : WordTrace (prefixWord ++ tailWord_811587) baseStart_811587 baseEnd_811587 := by
    simpa [prefixWord, tailWord_811587, baseEnd_811587] using wordTrace_append hprefix tailTrace_811587
  have hstable : (prefixWord ++ tailWord_811587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811587).length < 2 ^ (prefixWord ++ tailWord_811587).sum := by decide
  have hdescent : baseEnd_811587 < baseStart_811587 := by decide
  rcases family_descends (prefixWord ++ tailWord_811587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811604 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_811604 : Nat := 118140960795 + 811604 * 2 ^ 59
def prefixEnd_811604 : Nat := 4983230072969 + 3 ^ 40 * 811604 * 2
def baseEnd_811604 : Nat := 416742953111747829317507

theorem tailTrace_811604 : CollatzResearch.WordTrace tailWord_811604 prefixEnd_811604 416742953111747829317507 := by
  unfold tailWord_811604
  simp only [CollatzResearch.WordTrace]
  refine ⟨14800814875852396886464933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19734419834469862515286577 14800814875852396886464933)
  ·
    refine ⟨2775152789222324416212175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14800814875852396886464933 2775152789222324416212175)
    ·
      refine ⟨4162729183833486624318263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2775152789222324416212175 4162729183833486624318263)
      ·
        refine ⟨6244093775750229936477395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4162729183833486624318263 6244093775750229936477395)
        ·
          refine ⟨9366140663625344904716093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6244093775750229936477395 9366140663625344904716093)
          ·
            refine ⟨3512302748859504339268535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9366140663625344904716093 3512302748859504339268535)
            ·
              refine ⟨5268454123289256508902803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512302748859504339268535 5268454123289256508902803)
              ·
                refine ⟨7902681184933884763354205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268454123289256508902803 7902681184933884763354205)
                ·
                  refine ⟨2963505444350206786257827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7902681184933884763354205 2963505444350206786257827)
                  ·
                    refine ⟨4445258166525310179386741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2963505444350206786257827 4445258166525310179386741)
                    ·
                      refine ⟨416742953111747829317507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4445258166525310179386741 416742953111747829317507)
                      ·
                        rfl

theorem cell23_811604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_811604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811604 prefixEnd_811604 := by exact prefixLift 811604
  have htrace : WordTrace (prefixWord ++ tailWord_811604) baseStart_811604 baseEnd_811604 := by
    simpa [prefixWord, tailWord_811604, baseEnd_811604] using wordTrace_append hprefix tailTrace_811604
  have hstable : (prefixWord ++ tailWord_811604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811604).length < 2 ^ (prefixWord ++ tailWord_811604).sum := by decide
  have hdescent : baseEnd_811604 < baseStart_811604 := by decide
  rcases family_descends (prefixWord ++ tailWord_811604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811607 : List Nat := [1, 1, 3, 2, 2, 2, 2, 10]
def baseStart_811607 : Nat := 118140960795 + 811607 * 2 ^ 59
def prefixEnd_811607 : Nat := 4983230072969 + 3 ^ 40 * 811607 * 2
def baseEnd_811607 : Nat := 15434981242730048799259

theorem tailTrace_811607 : CollatzResearch.WordTrace tailWord_811607 prefixEnd_811607 15434981242730048799259 := by
  unfold tailWord_811607
  simp only [CollatzResearch.WordTrace]
  refine ⟨29601739170693925285289075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19734492780462616856859383 29601739170693925285289075)
  ·
    refine ⟨44402608756040887927933613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29601739170693925285289075 44402608756040887927933613)
    ·
      refine ⟨16650978283515332972975105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44402608756040887927933613 16650978283515332972975105)
      ·
        refine ⟨12488233712636499729731329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16650978283515332972975105 12488233712636499729731329)
        ·
          refine ⟨9366175284477374797298497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12488233712636499729731329 9366175284477374797298497)
          ·
            refine ⟨7024631463358031097973873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9366175284477374797298497 7024631463358031097973873)
            ·
              refine ⟨5268473597518523323480405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7024631463358031097973873 5268473597518523323480405)
              ·
                refine ⟨15434981242730048799259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5268473597518523323480405 15434981242730048799259)
                ·
                  rfl

theorem cell23_811607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 10].length) (baseStart_811607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811607 prefixEnd_811607 := by exact prefixLift 811607
  have htrace : WordTrace (prefixWord ++ tailWord_811607) baseStart_811607 baseEnd_811607 := by
    simpa [prefixWord, tailWord_811607, baseEnd_811607] using wordTrace_append hprefix tailTrace_811607
  have hstable : (prefixWord ++ tailWord_811607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811607).length < 2 ^ (prefixWord ++ tailWord_811607).sum := by decide
  have hdescent : baseEnd_811607 < baseStart_811607 := by decide
  rcases family_descends (prefixWord ++ tailWord_811607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811638 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_811638 : Nat := 118140960795 + 811638 * 2 ^ 59
def prefixEnd_811638 : Nat := 4983230072969 + 3 ^ 40 * 811638 * 2
def baseEnd_811638 : Nat := 416760411454000696292351

theorem tailTrace_811638 : CollatzResearch.WordTrace tailWord_811638 prefixEnd_811638 416760411454000696292351 := by
  unfold tailWord_811638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850179364598851098729223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19735246555721078386445045 1850179364598851098729223)
  ·
    refine ⟨2775269046898276648093835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1850179364598851098729223 2775269046898276648093835)
    ·
      refine ⟨4162903570347414972140753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2775269046898276648093835 4162903570347414972140753)
      ·
        refine ⟨3122177677760561229105565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4162903570347414972140753 3122177677760561229105565)
        ·
          refine ⟨1170816629160210460914587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3122177677760561229105565 1170816629160210460914587)
          ·
            refine ⟨1756224943740315691371881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170816629160210460914587 1756224943740315691371881)
            ·
              refine ⟨1317168707805236768528911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1756224943740315691371881 1317168707805236768528911)
              ·
                refine ⟨1975753061707855152793367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317168707805236768528911 1975753061707855152793367)
                ·
                  refine ⟨2963629592561782729190051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975753061707855152793367 2963629592561782729190051)
                  ·
                    refine ⟨4445444388842674093785077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2963629592561782729190051 4445444388842674093785077)
                    ·
                      refine ⟨416760411454000696292351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4445444388842674093785077 416760411454000696292351)
                      ·
                        rfl

theorem cell23_811638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_811638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811638 prefixEnd_811638 := by exact prefixLift 811638
  have htrace : WordTrace (prefixWord ++ tailWord_811638) baseStart_811638 baseEnd_811638 := by
    simpa [prefixWord, tailWord_811638, baseEnd_811638] using wordTrace_append hprefix tailTrace_811638
  have hstable : (prefixWord ++ tailWord_811638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811638).length < 2 ^ (prefixWord ++ tailWord_811638).sum := by decide
  have hdescent : baseEnd_811638 < baseStart_811638 := by decide
  rcases family_descends (prefixWord ++ tailWord_811638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811651 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 4, 1, 3]
def baseStart_811651 : Nat := 118140960795 + 811651 * 2 ^ 59
def prefixEnd_811651 : Nat := 4983230072969 + 3 ^ 40 * 811651 * 2
def baseEnd_811651 : Nat := 416767086702509145429791

theorem tailTrace_811651 : CollatzResearch.WordTrace tailWord_811651 prefixEnd_811651 416767086702509145429791 := by
  unfold tailWord_811651
  simp only [CollatzResearch.WordTrace]
  refine ⟨29603343982534520799890807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19735562655023013866593871 29603343982534520799890807)
  ·
    refine ⟨44405015973801781199836211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29603343982534520799890807 44405015973801781199836211)
    ·
      refine ⟨66607523960702671799754317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44405015973801781199836211 66607523960702671799754317)
      ·
        refine ⟨24977821485263501924907869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66607523960702671799754317 24977821485263501924907869)
        ·
          refine ⟨9366683056973813221840451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24977821485263501924907869 9366683056973813221840451)
          ·
            refine ⟨14050024585460719832760677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9366683056973813221840451 14050024585460719832760677)
            ·
              refine ⟨2634379609773884968642627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14050024585460719832760677 2634379609773884968642627)
              ·
                refine ⟨3951569414660827452963941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634379609773884968642627 3951569414660827452963941)
                ·
                  refine ⟨740919265248905147430739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3951569414660827452963941 740919265248905147430739)
                  ·
                    refine ⟨1111378897873357721146109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 740919265248905147430739 1111378897873357721146109)
                    ·
                      refine ⟨416767086702509145429791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1111378897873357721146109 416767086702509145429791)
                      ·
                        rfl

theorem cell23_811651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_811651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811651 prefixEnd_811651 := by exact prefixLift 811651
  have htrace : WordTrace (prefixWord ++ tailWord_811651) baseStart_811651 baseEnd_811651 := by
    simpa [prefixWord, tailWord_811651, baseEnd_811651] using wordTrace_append hprefix tailTrace_811651
  have hstable : (prefixWord ++ tailWord_811651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811651).length < 2 ^ (prefixWord ++ tailWord_811651).sum := by decide
  have hdescent : baseEnd_811651 < baseStart_811651 := by decide
  rcases family_descends (prefixWord ++ tailWord_811651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811695 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 1, 3, 2]
def baseStart_811695 : Nat := 118140960795 + 811695 * 2 ^ 59
def prefixEnd_811695 : Nat := 4983230072969 + 3 ^ 40 * 811695 * 2
def baseEnd_811695 : Nat := 416789679851306973279589

theorem tailTrace_811695 : CollatzResearch.WordTrace tailWord_811695 prefixEnd_811695 416789679851306973279589 := by
  unfold tailWord_811695
  simp only [CollatzResearch.WordTrace]
  refine ⟨29604948794375116314492539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19736632529583410876328359 29604948794375116314492539)
  ·
    refine ⟨44407423191562674471738809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29604948794375116314492539 44407423191562674471738809)
    ·
      refine ⟨33305567393672005853804107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44407423191562674471738809 33305567393672005853804107)
      ·
        refine ⟨49958351090508008780706161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33305567393672005853804107 49958351090508008780706161)
        ·
          refine ⟨37468763317881006585529621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49958351090508008780706161 37468763317881006585529621)
          ·
            refine ⟨1756348280525672183696701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37468763317881006585529621 1756348280525672183696701)
            ·
              refine ⟨658630605197127068886263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1756348280525672183696701 658630605197127068886263)
              ·
                refine ⟨987945907795690603329395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658630605197127068886263 987945907795690603329395)
                ·
                  refine ⟨1481918861693535904994093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987945907795690603329395 1481918861693535904994093)
                  ·
                    refine ⟨555719573135075964372785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481918861693535904994093 555719573135075964372785)
                    ·
                      refine ⟨416789679851306973279589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 555719573135075964372785 416789679851306973279589)
                      ·
                        rfl

theorem cell23_811695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 3, 2].length) (baseStart_811695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811695 prefixEnd_811695 := by exact prefixLift 811695
  have htrace : WordTrace (prefixWord ++ tailWord_811695) baseStart_811695 baseEnd_811695 := by
    simpa [prefixWord, tailWord_811695, baseEnd_811695] using wordTrace_append hprefix tailTrace_811695
  have hstable : (prefixWord ++ tailWord_811695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811695).length < 2 ^ (prefixWord ++ tailWord_811695).sum := by decide
  have hdescent : baseEnd_811695 < baseStart_811695 := by decide
  rcases family_descends (prefixWord ++ tailWord_811695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811748 : List Nat := [2, 3, 1, 1, 1, 5, 2, 3, 5]
def baseStart_811748 : Nat := 118140960795 + 811748 * 2 ^ 59
def prefixEnd_811748 : Nat := 4983230072969 + 3 ^ 40 * 811748 * 2
def baseEnd_811748 : Nat := 46312988258443918435205

theorem tailTrace_811748 : CollatzResearch.WordTrace tailWord_811748 prefixEnd_811748 46312988258443918435205 := by
  unfold tailWord_811748
  simp only [CollatzResearch.WordTrace]
  refine ⟨14803440931591553183085949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19737921242122070910781265 14803440931591553183085949)
  ·
    refine ⟨5551290349346832443657231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14803440931591553183085949 5551290349346832443657231)
    ·
      refine ⟨8326935524020248665485847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5551290349346832443657231 8326935524020248665485847)
      ·
        refine ⟨12490403286030372998228771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8326935524020248665485847 12490403286030372998228771)
        ·
          refine ⟨18735604929045559497343157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12490403286030372998228771 18735604929045559497343157)
          ·
            refine ⟨1756462962098021202875921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18735604929045559497343157 1756462962098021202875921)
            ·
              refine ⟨1317347221573515902156941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1756462962098021202875921 1317347221573515902156941)
              ·
                refine ⟨494005208090068463308853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1317347221573515902156941 494005208090068463308853)
                ·
                  refine ⟨46312988258443918435205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 494005208090068463308853 46312988258443918435205)
                  ·
                    rfl

theorem cell23_811748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_811748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811748 prefixEnd_811748 := by exact prefixLift 811748
  have htrace : WordTrace (prefixWord ++ tailWord_811748) baseStart_811748 baseEnd_811748 := by
    simpa [prefixWord, tailWord_811748, baseEnd_811748] using wordTrace_append hprefix tailTrace_811748
  have hstable : (prefixWord ++ tailWord_811748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811748).length < 2 ^ (prefixWord ++ tailWord_811748).sum := by decide
  have hdescent : baseEnd_811748 < baseStart_811748 := by decide
  rcases family_descends (prefixWord ++ tailWord_811748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811791 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 3, 4]
def baseStart_811791 : Nat := 118140960795 + 811791 * 2 ^ 59
def prefixEnd_811791 : Nat := 4983230072969 + 3 ^ 40 * 811791 * 2
def baseEnd_811791 : Nat := 138946324664712865893049

theorem tailTrace_811791 : CollatzResearch.WordTrace tailWord_811791 prefixEnd_811791 138946324664712865893049 := by
  unfold tailWord_811791
  simp only [CollatzResearch.WordTrace]
  refine ⟨29608450202027324709987227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19738966801351549806658151 29608450202027324709987227)
  ·
    refine ⟨44412675303040987064980841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29608450202027324709987227 44412675303040987064980841)
    ·
      refine ⟨33309506477280740298735631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44412675303040987064980841 33309506477280740298735631)
      ·
        refine ⟨49964259715921110448103447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33309506477280740298735631 49964259715921110448103447)
        ·
          refine ⟨74946389573881665672155171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49964259715921110448103447 74946389573881665672155171)
          ·
            refine ⟨112419584360822498508232757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74946389573881665672155171 112419584360822498508232757)
            ·
              refine ⟨10539336033827109235146821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112419584360822498508232757 10539336033827109235146821)
              ·
                refine ⟨1976125506342582981590029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10539336033827109235146821 1976125506342582981590029)
                ·
                  refine ⟨741047064878468618096261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1976125506342582981590029 741047064878468618096261)
                  ·
                    refine ⟨138946324664712865893049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 741047064878468618096261 138946324664712865893049)
                    ·
                      rfl

theorem cell23_811791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 4].length) (baseStart_811791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811791 prefixEnd_811791 := by exact prefixLift 811791
  have htrace : WordTrace (prefixWord ++ tailWord_811791) baseStart_811791 baseEnd_811791 := by
    simpa [prefixWord, tailWord_811791, baseEnd_811791] using wordTrace_append hprefix tailTrace_811791
  have hstable : (prefixWord ++ tailWord_811791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811791).length < 2 ^ (prefixWord ++ tailWord_811791).sum := by decide
  have hdescent : baseEnd_811791 < baseStart_811791 := by decide
  rcases family_descends (prefixWord ++ tailWord_811791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811824 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_811824 : Nat := 118140960795 + 811824 * 2 ^ 59
def prefixEnd_811824 : Nat := 4983230072969 + 3 ^ 40 * 811824 * 2
def baseEnd_811824 : Nat := 416855918855736968566495

theorem tailTrace_811824 : CollatzResearch.WordTrace tailWord_811824 prefixEnd_811824 416855918855736968566495 := by
  unfold tailWord_811824
  simp only [CollatzResearch.WordTrace]
  refine ⟨14804826905453885672969263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19739769207271847563959017 14804826905453885672969263)
  ·
    refine ⟨22207240358180828509453895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14804826905453885672969263 22207240358180828509453895)
    ·
      refine ⟨33310860537271242764180843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22207240358180828509453895 33310860537271242764180843)
      ·
        refine ⟨49966290805906864146271265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33310860537271242764180843 49966290805906864146271265)
        ·
          refine ⟨37474718104430148109703449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49966290805906864146271265 37474718104430148109703449)
          ·
            refine ⟨28106038578322611082277587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37474718104430148109703449 28106038578322611082277587)
            ·
              refine ⟨42159057867483916623416381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28106038578322611082277587 42159057867483916623416381)
              ·
                refine ⟨15809646700306468733781143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42159057867483916623416381 15809646700306468733781143)
                ·
                  refine ⟨23714470050459703100671715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15809646700306468733781143 23714470050459703100671715)
                  ·
                    refine ⟨35571705075689554651007573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23714470050459703100671715 35571705075689554651007573)
                    ·
                      refine ⟨416855918855736968566495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 35571705075689554651007573 416855918855736968566495)
                      ·
                        rfl

theorem cell23_811824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_811824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811824 prefixEnd_811824 := by exact prefixLift 811824
  have htrace : WordTrace (prefixWord ++ tailWord_811824) baseStart_811824 baseEnd_811824 := by
    simpa [prefixWord, tailWord_811824, baseEnd_811824] using wordTrace_append hprefix tailTrace_811824
  have hstable : (prefixWord ++ tailWord_811824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811824).length < 2 ^ (prefixWord ++ tailWord_811824).sum := by decide
  have hdescent : baseEnd_811824 < baseStart_811824 := by decide
  rcases family_descends (prefixWord ++ tailWord_811824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811848 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_811848 : Nat := 118140960795 + 811848 * 2 ^ 59
def prefixEnd_811848 : Nat := 4983230072969 + 3 ^ 40 * 811848 * 2
def baseEnd_811848 : Nat := 416868242391444874666385

theorem tailTrace_811848 : CollatzResearch.WordTrace tailWord_811848 prefixEnd_811848 416868242391444874666385 := by
  unfold tailWord_811848
  simp only [CollatzResearch.WordTrace]
  refine ⟨14805264581410411722406099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19740352775213882296541465 14805264581410411722406099)
  ·
    refine ⟨22207896872115617583609149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14805264581410411722406099 22207896872115617583609149)
    ·
      refine ⟨8327961327043356593853431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22207896872115617583609149 8327961327043356593853431)
      ·
        refine ⟨12491941990565034890780147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8327961327043356593853431 12491941990565034890780147)
        ·
          refine ⟨18737912985847552336170221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12491941990565034890780147 18737912985847552336170221)
          ·
            refine ⟨7026717369692832126063833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18737912985847552336170221 7026717369692832126063833)
            ·
              refine ⟨5270038027269624094547875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7026717369692832126063833 5270038027269624094547875)
              ·
                refine ⟨7905057040904436141821813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5270038027269624094547875 7905057040904436141821813)
                ·
                  refine ⟨741099097584790888295795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7905057040904436141821813 741099097584790888295795)
                  ·
                    refine ⟨1111648646377186332443693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 741099097584790888295795 1111648646377186332443693)
                    ·
                      refine ⟨416868242391444874666385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1111648646377186332443693 416868242391444874666385)
                      ·
                        rfl

theorem cell23_811848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_811848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811848 prefixEnd_811848 := by exact prefixLift 811848
  have htrace : WordTrace (prefixWord ++ tailWord_811848) baseStart_811848 baseEnd_811848 := by
    simpa [prefixWord, tailWord_811848, baseEnd_811848] using wordTrace_append hprefix tailTrace_811848
  have hstable : (prefixWord ++ tailWord_811848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811848).length < 2 ^ (prefixWord ++ tailWord_811848).sum := by decide
  have hdescent : baseEnd_811848 < baseStart_811848 := by decide
  rcases family_descends (prefixWord ++ tailWord_811848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811875 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 2, 3, 2]
def baseStart_811875 : Nat := 118140960795 + 811875 * 2 ^ 59
def prefixEnd_811875 : Nat := 4983230072969 + 3 ^ 40 * 811875 * 2
def baseEnd_811875 : Nat := 416882106369116269028761

theorem tailTrace_811875 : CollatzResearch.WordTrace tailWord_811875 prefixEnd_811875 416882106369116269028761 := by
  unfold tailWord_811875
  simp only [CollatzResearch.WordTrace]
  refine ⟨29611513933723007056045079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19741009289148671370696719 29611513933723007056045079)
  ·
    refine ⟨44417270900584510584067619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29611513933723007056045079 44417270900584510584067619)
    ·
      refine ⟨66625906350876765876101429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44417270900584510584067619 66625906350876765876101429)
      ·
        refine ⟨6246178720394696800884509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66625906350876765876101429 6246178720394696800884509)
        ·
          refine ⟨2342317020148011300331691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6246178720394696800884509 2342317020148011300331691)
          ·
            refine ⟨3513475530222016950497537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342317020148011300331691 3513475530222016950497537)
            ·
              refine ⟨2635106647666512712873153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3513475530222016950497537 2635106647666512712873153)
              ·
                refine ⟨1976329985749884534654865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2635106647666512712873153 1976329985749884534654865)
                ·
                  refine ⟨1482247489312413400991149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1976329985749884534654865 1482247489312413400991149)
                  ·
                    refine ⟨555842808492155025371681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1482247489312413400991149 555842808492155025371681)
                    ·
                      refine ⟨416882106369116269028761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 555842808492155025371681 416882106369116269028761)
                      ·
                        rfl

theorem cell23_811875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_811875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811875 prefixEnd_811875 := by exact prefixLift 811875
  have htrace : WordTrace (prefixWord ++ tailWord_811875) baseStart_811875 baseEnd_811875 := by
    simpa [prefixWord, tailWord_811875, baseEnd_811875] using wordTrace_append hprefix tailTrace_811875
  have hstable : (prefixWord ++ tailWord_811875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811875).length < 2 ^ (prefixWord ++ tailWord_811875).sum := by decide
  have hdescent : baseEnd_811875 < baseStart_811875 := by decide
  rcases family_descends (prefixWord ++ tailWord_811875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811891 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 5]
def baseStart_811891 : Nat := 118140960795 + 811891 * 2 ^ 59
def prefixEnd_811891 : Nat := 4983230072969 + 3 ^ 40 * 811891 * 2
def baseEnd_811891 : Nat := 416890322059588206428687

theorem tailTrace_811891 : CollatzResearch.WordTrace tailWord_811891 prefixEnd_811891 416890322059588206428687 := by
  unfold tailWord_811891
  simp only [CollatzResearch.WordTrace]
  refine ⟨29612097501665041788627527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19741398334443361192418351 29612097501665041788627527)
  ·
    refine ⟨44418146252497562682941291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29612097501665041788627527 44418146252497562682941291)
    ·
      refine ⟨66627219378746344024411937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44418146252497562682941291 66627219378746344024411937)
      ·
        refine ⟨49970414534059758018308953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66627219378746344024411937 49970414534059758018308953)
        ·
          refine ⟨37477810900544818513731715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49970414534059758018308953 37477810900544818513731715)
          ·
            refine ⟨56216716350817227770597573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37477810900544818513731715 56216716350817227770597573)
            ·
              refine ⟨10540634315778230206987045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56216716350817227770597573 10540634315778230206987045)
              ·
                refine ⟨1976368934208418163810071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10540634315778230206987045 1976368934208418163810071)
                ·
                  refine ⟨2964553401312627245715107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976368934208418163810071 2964553401312627245715107)
                  ·
                    refine ⟨4446830101968940868572661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2964553401312627245715107 4446830101968940868572661)
                    ·
                      refine ⟨416890322059588206428687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4446830101968940868572661 416890322059588206428687)
                      ·
                        rfl

theorem cell23_811891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_811891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811891 prefixEnd_811891 := by exact prefixLift 811891
  have htrace : WordTrace (prefixWord ++ tailWord_811891) baseStart_811891 baseEnd_811891 := by
    simpa [prefixWord, tailWord_811891, baseEnd_811891] using wordTrace_append hprefix tailTrace_811891
  have hstable : (prefixWord ++ tailWord_811891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811891).length < 2 ^ (prefixWord ++ tailWord_811891).sum := by decide
  have hdescent : baseEnd_811891 < baseStart_811891 := by decide
  rcases family_descends (prefixWord ++ tailWord_811891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811901 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_811901 : Nat := 118140960795 + 811901 * 2 ^ 59
def prefixEnd_811901 : Nat := 4983230072969 + 3 ^ 40 * 811901 * 2
def baseEnd_811901 : Nat := 416895456866133167303641

theorem tailTrace_811901 : CollatzResearch.WordTrace tailWord_811901 prefixEnd_811901 416895456866133167303641 := by
  unfold tailWord_811901
  simp only [CollatzResearch.WordTrace]
  refine ⟨29612462231628813496491557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19741641487752542330994371 29612462231628813496491557)
  ·
    refine ⟨5552336668430402530592167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29612462231628813496491557 5552336668430402530592167)
    ·
      refine ⟨8328505002645603795888251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5552336668430402530592167 8328505002645603795888251)
      ·
        refine ⟨12492757503968405693832377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8328505002645603795888251 12492757503968405693832377)
        ·
          refine ⟨9369568127976304270374283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12492757503968405693832377 9369568127976304270374283)
          ·
            refine ⟨14054352191964456405561425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9369568127976304270374283 14054352191964456405561425)
            ·
              refine ⟨10540764143973342304171069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14054352191964456405561425 10540764143973342304171069)
              ·
                refine ⟨3952786553990003364064151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10540764143973342304171069 3952786553990003364064151)
                ·
                  refine ⟨5929179830985005046096227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3952786553990003364064151 5929179830985005046096227)
                  ·
                    refine ⟨8893769746477507569144341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5929179830985005046096227 8893769746477507569144341)
                    ·
                      refine ⟨416895456866133167303641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8893769746477507569144341 416895456866133167303641)
                      ·
                        rfl

theorem cell23_811901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_811901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811901 prefixEnd_811901 := by exact prefixLift 811901
  have htrace : WordTrace (prefixWord ++ tailWord_811901) baseStart_811901 baseEnd_811901 := by
    simpa [prefixWord, tailWord_811901, baseEnd_811901] using wordTrace_append hprefix tailTrace_811901
  have hstable : (prefixWord ++ tailWord_811901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811901).length < 2 ^ (prefixWord ++ tailWord_811901).sum := by decide
  have hdescent : baseEnd_811901 < baseStart_811901 := by decide
  rcases family_descends (prefixWord ++ tailWord_811901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811922 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_811922 : Nat := 118140960795 + 811922 * 2 ^ 59
def prefixEnd_811922 : Nat := 4983230072969 + 3 ^ 40 * 811922 * 2
def baseEnd_811922 : Nat := 416906239959877585141045

theorem tailTrace_811922 : CollatzResearch.WordTrace tailWord_811922 prefixEnd_811922 416906239959877585141045 := by
  unfold tailWord_811922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7403307041138183520751505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19742152109701822722004013 7403307041138183520751505)
  ·
    refine ⟨5552480280853637640563629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7403307041138183520751505 5552480280853637640563629)
    ·
      refine ⟨2082180105320114115211361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5552480280853637640563629 2082180105320114115211361)
      ·
        refine ⟨1561635078990085586408521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2082180105320114115211361 1561635078990085586408521)
        ·
          refine ⟨1171226309242564189806391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1561635078990085586408521 1171226309242564189806391)
          ·
            refine ⟨1756839463863846284709587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171226309242564189806391 1756839463863846284709587)
            ·
              refine ⟨2635259195795769427064381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756839463863846284709587 2635259195795769427064381)
              ·
                refine ⟨988222198423413535149143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2635259195795769427064381 988222198423413535149143)
                ·
                  refine ⟨1482333297635120302723715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988222198423413535149143 1482333297635120302723715)
                  ·
                    refine ⟨2223499946452680454085573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1482333297635120302723715 2223499946452680454085573)
                    ·
                      refine ⟨416906239959877585141045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2223499946452680454085573 416906239959877585141045)
                      ·
                        rfl

theorem cell23_811922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_811922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811922 prefixEnd_811922 := by exact prefixLift 811922
  have htrace : WordTrace (prefixWord ++ tailWord_811922) baseStart_811922 baseEnd_811922 := by
    simpa [prefixWord, tailWord_811922, baseEnd_811922] using wordTrace_append hprefix tailTrace_811922
  have hstable : (prefixWord ++ tailWord_811922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811922).length < 2 ^ (prefixWord ++ tailWord_811922).sum := by decide
  have hdescent : baseEnd_811922 < baseStart_811922 := by decide
  rcases family_descends (prefixWord ++ tailWord_811922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811925 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_811925 : Nat := 118140960795 + 811925 * 2 ^ 59
def prefixEnd_811925 : Nat := 4983230072969 + 3 ^ 40 * 811925 * 2
def baseEnd_811925 : Nat := 416907780401841073403531

theorem tailTrace_811925 : CollatzResearch.WordTrace tailWord_811925 prefixEnd_811925 416907780401841073403531 := by
  unfold tailWord_811925
  simp only [CollatzResearch.WordTrace]
  refine ⟨29613337583541865595365229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19742225055694577063576819 29613337583541865595365229)
  ·
    refine ⟨11105001593828199598261961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29613337583541865595365229 11105001593828199598261961)
    ·
      refine ⟨8328751195371149698696471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11105001593828199598261961 8328751195371149698696471)
      ·
        refine ⟨12493126793056724548044707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8328751195371149698696471 12493126793056724548044707)
        ·
          refine ⟨18739690189585086822067061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12493126793056724548044707 18739690189585086822067061)
          ·
            refine ⟨1756845955273601889568787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18739690189585086822067061 1756845955273601889568787)
            ·
              refine ⟨2635268932910402834353181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756845955273601889568787 2635268932910402834353181)
              ·
                refine ⟨988225849841401062882443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2635268932910402834353181 988225849841401062882443)
                ·
                  refine ⟨1482338774762101594323665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988225849841401062882443 1482338774762101594323665)
                  ·
                    refine ⟨1111754081071576195742749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1482338774762101594323665 1111754081071576195742749)
                    ·
                      refine ⟨416907780401841073403531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1111754081071576195742749 416907780401841073403531)
                      ·
                        rfl

theorem cell23_811925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_811925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811925 prefixEnd_811925 := by exact prefixLift 811925
  have htrace : WordTrace (prefixWord ++ tailWord_811925) baseStart_811925 baseEnd_811925 := by
    simpa [prefixWord, tailWord_811925, baseEnd_811925] using wordTrace_append hprefix tailTrace_811925
  have hstable : (prefixWord ++ tailWord_811925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811925).length < 2 ^ (prefixWord ++ tailWord_811925).sum := by decide
  have hdescent : baseEnd_811925 < baseStart_811925 := by decide
  rcases family_descends (prefixWord ++ tailWord_811925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811949 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_811949 : Nat := 118140960795 + 811949 * 2 ^ 59
def prefixEnd_811949 : Nat := 4983230072969 + 3 ^ 40 * 811949 * 2
def baseEnd_811949 : Nat := 138973367979182993167807

theorem tailTrace_811949 : CollatzResearch.WordTrace tailWord_811949 prefixEnd_811949 138973367979182993167807 := by
  unfold tailWord_811949
  simp only [CollatzResearch.WordTrace]
  refine ⟨29614212935454917694238901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19742808623636611796159267 29614212935454917694238901)
  ·
    refine ⟨2776332462698898533834897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29614212935454917694238901 2776332462698898533834897)
    ·
      refine ⟨2082249347024173900376173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2776332462698898533834897 2082249347024173900376173)
      ·
        refine ⟨780843505134065212641065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2082249347024173900376173 780843505134065212641065)
        ·
          refine ⟨585632628850548909480799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780843505134065212641065 585632628850548909480799)
          ·
            refine ⟨878448943275823364221199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585632628850548909480799 878448943275823364221199)
            ·
              refine ⟨1317673414913735046331799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878448943275823364221199 1317673414913735046331799)
              ·
                refine ⟨1976510122370602569497699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317673414913735046331799 1976510122370602569497699)
                ·
                  refine ⟨2964765183555903854246549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976510122370602569497699 2964765183555903854246549)
                  ·
                    refine ⟨138973367979182993167807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2964765183555903854246549 138973367979182993167807)
                    ·
                      rfl

theorem cell23_811949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_811949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811949 prefixEnd_811949 := by exact prefixLift 811949
  have htrace : WordTrace (prefixWord ++ tailWord_811949) baseStart_811949 baseEnd_811949 := by
    simpa [prefixWord, tailWord_811949, baseEnd_811949] using wordTrace_append hprefix tailTrace_811949
  have hstable : (prefixWord ++ tailWord_811949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811949).length < 2 ^ (prefixWord ++ tailWord_811949).sum := by decide
  have hdescent : baseEnd_811949 < baseStart_811949 := by decide
  rcases family_descends (prefixWord ++ tailWord_811949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811982 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2]
def baseStart_811982 : Nat := 118140960795 + 811982 * 2 ^ 59
def prefixEnd_811982 : Nat := 4983230072969 + 3 ^ 40 * 811982 * 2
def baseEnd_811982 : Nat := 416937048799147350390769

theorem tailTrace_811982 : CollatzResearch.WordTrace tailWord_811982 prefixEnd_811982 416937048799147350390769 := by
  unfold tailWord_811982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701927068041920541273775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19743611029556909553460133 3701927068041920541273775)
  ·
    refine ⟨5552890602062880811910663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3701927068041920541273775 5552890602062880811910663)
    ·
      refine ⟨8329335903094321217865995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5552890602062880811910663 8329335903094321217865995)
      ·
        refine ⟨12494003854641481826798993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8329335903094321217865995 12494003854641481826798993)
        ·
          refine ⟨9370502890981111370099245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12494003854641481826798993 9370502890981111370099245)
          ·
            refine ⟨3513938584117916763787217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9370502890981111370099245 3513938584117916763787217)
            ·
              refine ⟨2635453938088437572840413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3513938584117916763787217 2635453938088437572840413)
              ·
                refine ⟨988295226783164089815155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2635453938088437572840413 988295226783164089815155)
                ·
                  refine ⟨1482442840174746134722733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988295226783164089815155 1482442840174746134722733)
                  ·
                    refine ⟨555916065065529800521025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1482442840174746134722733 555916065065529800521025)
                    ·
                      refine ⟨416937048799147350390769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 555916065065529800521025 416937048799147350390769)
                      ·
                        rfl

theorem cell23_811982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_811982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811982 prefixEnd_811982 := by exact prefixLift 811982
  have htrace : WordTrace (prefixWord ++ tailWord_811982) baseStart_811982 baseEnd_811982 := by
    simpa [prefixWord, tailWord_811982, baseEnd_811982] using wordTrace_append hprefix tailTrace_811982
  have hstable : (prefixWord ++ tailWord_811982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811982).length < 2 ^ (prefixWord ++ tailWord_811982).sum := by decide
  have hdescent : baseEnd_811982 < baseStart_811982 := by decide
  rcases family_descends (prefixWord ++ tailWord_811982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811991 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_811991 : Nat := 118140960795 + 811991 * 2 ^ 59
def prefixEnd_811991 : Nat := 4983230072969 + 3 ^ 40 * 811991 * 2
def baseEnd_811991 : Nat := 416941670125037815178227

theorem tailTrace_811991 : CollatzResearch.WordTrace tailWord_811991 prefixEnd_811991 416941670125037815178227 := by
  unfold tailWord_811991
  simp only [CollatzResearch.WordTrace]
  refine ⟨29615744801302758867267827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19743829867535172578178551 29615744801302758867267827)
  ·
    refine ⟨44423617201954138300901741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29615744801302758867267827 44423617201954138300901741)
    ·
      refine ⟨16658856450732801862838153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44423617201954138300901741 16658856450732801862838153)
      ·
        refine ⟨12494142338049601397128615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16658856450732801862838153 12494142338049601397128615)
        ·
          refine ⟨18741213507074402095692923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12494142338049601397128615 18741213507074402095692923)
          ·
            refine ⟨28111820260611603143539385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18741213507074402095692923 28111820260611603143539385)
            ·
              refine ⟨21083865195458702357654539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28111820260611603143539385 21083865195458702357654539)
              ·
                refine ⟨31625797793188053536481809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21083865195458702357654539 31625797793188053536481809)
                ·
                  refine ⟨23719348344891040152361357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31625797793188053536481809 23719348344891040152361357)
                  ·
                    refine ⟨8894755629334140057135509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23719348344891040152361357 8894755629334140057135509)
                    ·
                      refine ⟨416941670125037815178227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8894755629334140057135509 416941670125037815178227)
                      ·
                        rfl

theorem cell23_811991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_811991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_811991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_811991 prefixEnd_811991 := by exact prefixLift 811991
  have htrace : WordTrace (prefixWord ++ tailWord_811991) baseStart_811991 baseEnd_811991 := by
    simpa [prefixWord, tailWord_811991, baseEnd_811991] using wordTrace_append hprefix tailTrace_811991
  have hstable : (prefixWord ++ tailWord_811991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811991).length < 2 ^ (prefixWord ++ tailWord_811991).sum := by decide
  have hdescent : baseEnd_811991 < baseStart_811991 := by decide
  rcases family_descends (prefixWord ++ tailWord_811991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812008 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_812008 : Nat := 118140960795 + 812008 * 2 ^ 59
def prefixEnd_812008 : Nat := 4983230072969 + 3 ^ 40 * 812008 * 2
def baseEnd_812008 : Nat := 416950399296164248665649

theorem tailTrace_812008 : CollatzResearch.WordTrace tailWord_812008 prefixEnd_812008 416950399296164248665649 := by
  unfold tailWord_812008
  simp only [CollatzResearch.WordTrace]
  refine ⟨14808182421120585385318339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19744243228160780513757785 14808182421120585385318339)
  ·
    refine ⟨22212273631680878077977509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14808182421120585385318339 22212273631680878077977509)
    ·
      refine ⟨4164801305940164639620783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22212273631680878077977509 4164801305940164639620783)
      ·
        refine ⟨6247201958910246959431175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4164801305940164639620783 6247201958910246959431175)
        ·
          refine ⟨9370802938365370439146763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247201958910246959431175 9370802938365370439146763)
          ·
            refine ⟨14056204407548055658720145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9370802938365370439146763 14056204407548055658720145)
            ·
              refine ⟨10542153305661041744040109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14056204407548055658720145 10542153305661041744040109)
              ·
                refine ⟨3953307489622890654015041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10542153305661041744040109 3953307489622890654015041)
                ·
                  refine ⟨2964980617217167990511281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3953307489622890654015041 2964980617217167990511281)
                  ·
                    refine ⟨2223735462912875992883461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2964980617217167990511281 2223735462912875992883461)
                    ·
                      refine ⟨416950399296164248665649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2223735462912875992883461 416950399296164248665649)
                      ·
                        rfl

theorem cell23_812008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_812008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812008 prefixEnd_812008 := by exact prefixLift 812008
  have htrace : WordTrace (prefixWord ++ tailWord_812008) baseStart_812008 baseEnd_812008 := by
    simpa [prefixWord, tailWord_812008, baseEnd_812008] using wordTrace_append hprefix tailTrace_812008
  have hstable : (prefixWord ++ tailWord_812008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812008).length < 2 ^ (prefixWord ++ tailWord_812008).sum := by decide
  have hdescent : baseEnd_812008 < baseStart_812008 := by decide
  rcases family_descends (prefixWord ++ tailWord_812008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812058 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_812058 : Nat := 118140960795 + 812058 * 2 ^ 59
def prefixEnd_812058 : Nat := 4983230072969 + 3 ^ 40 * 812058 * 2
def baseEnd_812058 : Nat := 416976073328889053040419

theorem tailTrace_812058 : CollatzResearch.WordTrace tailWord_812058 prefixEnd_812058 416976073328889053040419 := by
  unfold tailWord_812058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7404547123015007327489207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19745458994706686206637885 7404547123015007327489207)
  ·
    refine ⟨11106820684522510991233811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7404547123015007327489207 11106820684522510991233811)
    ·
      refine ⟨16660231026783766486850717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11106820684522510991233811 16660231026783766486850717)
      ·
        refine ⟨6247586635043912432569019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16660231026783766486850717 6247586635043912432569019)
        ·
          refine ⟨9371379952565868648853529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247586635043912432569019 9371379952565868648853529)
          ·
            refine ⟨7028534964424401486640147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9371379952565868648853529 7028534964424401486640147)
            ·
              refine ⟨10542802446636602229960221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7028534964424401486640147 10542802446636602229960221)
              ·
                refine ⟨3953550917488725836235083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10542802446636602229960221 3953550917488725836235083)
                ·
                  refine ⟨5930326376233088754352625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953550917488725836235083 5930326376233088754352625)
                  ·
                    refine ⟨4447744782174816565764469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5930326376233088754352625 4447744782174816565764469)
                    ·
                      refine ⟨416976073328889053040419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4447744782174816565764469 416976073328889053040419)
                      ·
                        rfl

theorem cell23_812058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_812058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812058 prefixEnd_812058 := by exact prefixLift 812058
  have htrace : WordTrace (prefixWord ++ tailWord_812058) baseStart_812058 baseEnd_812058 := by
    simpa [prefixWord, tailWord_812058, baseEnd_812058] using wordTrace_append hprefix tailTrace_812058
  have hstable : (prefixWord ++ tailWord_812058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812058).length < 2 ^ (prefixWord ++ tailWord_812058).sum := by decide
  have hdescent : baseEnd_812058 < baseStart_812058 := by decide
  rcases family_descends (prefixWord ++ tailWord_812058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812085 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_812085 : Nat := 118140960795 + 812085 * 2 ^ 59
def prefixEnd_812085 : Nat := 4983230072969 + 3 ^ 40 * 812085 * 2
def baseEnd_812085 : Nat := 416989937306560447402795

theorem tailTrace_812085 : CollatzResearch.WordTrace tailWord_812085 prefixEnd_812085 416989937306560447402795 := by
  unfold tailWord_812085
  simp only [CollatzResearch.WordTrace]
  refine ⟨29619173262962212921189709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19746115508641475280793139 29619173262962212921189709)
  ·
    refine ⟨11107189973610829845446141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29619173262962212921189709 11107189973610829845446141)
    ·
      refine ⟨4165196240104061192042303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11107189973610829845446141 4165196240104061192042303)
      ·
        refine ⟨6247794360156091788063455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165196240104061192042303 6247794360156091788063455)
        ·
          refine ⟨9371691540234137682095183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247794360156091788063455 9371691540234137682095183)
          ·
            refine ⟨14057537310351206523142775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371691540234137682095183 14057537310351206523142775)
            ·
              refine ⟨21086305965526809784714163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14057537310351206523142775 21086305965526809784714163)
              ·
                refine ⟨31629458948290214677071245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21086305965526809784714163 31629458948290214677071245)
                ·
                  refine ⟨11861047105608830503901717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31629458948290214677071245 11861047105608830503901717)
                  ·
                    refine ⟨555986583075413929870393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11861047105608830503901717 555986583075413929870393)
                    ·
                      refine ⟨416989937306560447402795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 555986583075413929870393 416989937306560447402795)
                      ·
                        rfl

theorem cell23_812085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_812085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812085 prefixEnd_812085 := by exact prefixLift 812085
  have htrace : WordTrace (prefixWord ++ tailWord_812085) baseStart_812085 baseEnd_812085 := by
    simpa [prefixWord, tailWord_812085, baseEnd_812085] using wordTrace_append hprefix tailTrace_812085
  have hstable : (prefixWord ++ tailWord_812085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812085).length < 2 ^ (prefixWord ++ tailWord_812085).sum := by decide
  have hdescent : baseEnd_812085 < baseStart_812085 := by decide
  rcases family_descends (prefixWord ++ tailWord_812085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812128 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_812128 : Nat := 118140960795 + 812128 * 2 ^ 59
def prefixEnd_812128 : Nat := 4983230072969 + 3 ^ 40 * 812128 * 2
def baseEnd_812128 : Nat := 417012016974703779165097

theorem tailTrace_812128 : CollatzResearch.WordTrace tailWord_812128 prefixEnd_812128 417012016974703779165097 := by
  unfold tailWord_812128
  simp only [CollatzResearch.WordTrace]
  refine ⟨14810370800903215632502519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19747161067870954176670025 14810370800903215632502519)
  ·
    refine ⟨22215556201354823448753779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14810370800903215632502519 22215556201354823448753779)
    ·
      refine ⟨33323334302032235173130669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22215556201354823448753779 33323334302032235173130669)
      ·
        refine ⟨12496250363262088189924001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33323334302032235173130669 12496250363262088189924001)
        ·
          refine ⟨9372187772446566142443001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12496250363262088189924001 9372187772446566142443001)
          ·
            refine ⟨7029140829334924606832251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9372187772446566142443001 7029140829334924606832251)
            ·
              refine ⟨10543711244002386910248377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7029140829334924606832251 10543711244002386910248377)
              ·
                refine ⟨7907783433001790182686283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10543711244002386910248377 7907783433001790182686283)
                ·
                  refine ⟨11861675149502685274029425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7907783433001790182686283 11861675149502685274029425)
                  ·
                    refine ⟨8896256362127013955522069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11861675149502685274029425 8896256362127013955522069)
                    ·
                      refine ⟨417012016974703779165097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8896256362127013955522069 417012016974703779165097)
                      ·
                        rfl

theorem cell23_812128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_812128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812128 prefixEnd_812128 := by exact prefixLift 812128
  have htrace : WordTrace (prefixWord ++ tailWord_812128) baseStart_812128 baseEnd_812128 := by
    simpa [prefixWord, tailWord_812128, baseEnd_812128] using wordTrace_append hprefix tailTrace_812128
  have hstable : (prefixWord ++ tailWord_812128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812128).length < 2 ^ (prefixWord ++ tailWord_812128).sum := by decide
  have hdescent : baseEnd_812128 < baseStart_812128 := by decide
  rcases family_descends (prefixWord ++ tailWord_812128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812169 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 3, 1, 3]
def baseStart_812169 : Nat := 118140960795 + 812169 * 2 ^ 59
def prefixEnd_812169 : Nat := 4983230072969 + 3 ^ 40 * 812169 * 2
def baseEnd_812169 : Nat := 417033069681538118752409

theorem tailTrace_812169 : CollatzResearch.WordTrace tailWord_812169 prefixEnd_812169 417033069681538118752409 := by
  unfold tailWord_812169
  simp only [CollatzResearch.WordTrace]
  refine ⟨29622236994657895267247561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19748157996438596844831707 29622236994657895267247561)
  ·
    refine ⟨22216677745993421450435671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29622236994657895267247561 22216677745993421450435671)
    ·
      refine ⟨33325016618990132175653507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22216677745993421450435671 33325016618990132175653507)
      ·
        refine ⟨49987524928485198263480261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33325016618990132175653507 49987524928485198263480261)
        ·
          refine ⟨9372660924090974674402549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49987524928485198263480261 9372660924090974674402549)
          ·
            refine ⟨878686961633528875725239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9372660924090974674402549 878686961633528875725239)
            ·
              refine ⟨1318030442450293313587859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878686961633528875725239 1318030442450293313587859)
              ·
                refine ⟨1977045663675439970381789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318030442450293313587859 1977045663675439970381789)
                ·
                  refine ⟨741392123878289988893171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1977045663675439970381789 741392123878289988893171)
                  ·
                    refine ⟨1112088185817434983339757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 741392123878289988893171 1112088185817434983339757)
                    ·
                      refine ⟨417033069681538118752409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1112088185817434983339757 417033069681538118752409)
                      ·
                        rfl

theorem cell23_812169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 1, 3].length) (baseStart_812169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812169 prefixEnd_812169 := by exact prefixLift 812169
  have htrace : WordTrace (prefixWord ++ tailWord_812169) baseStart_812169 baseEnd_812169 := by
    simpa [prefixWord, tailWord_812169, baseEnd_812169] using wordTrace_append hprefix tailTrace_812169
  have hstable : (prefixWord ++ tailWord_812169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812169).length < 2 ^ (prefixWord ++ tailWord_812169).sum := by decide
  have hdescent : baseEnd_812169 < baseStart_812169 := by decide
  rcases family_descends (prefixWord ++ tailWord_812169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812175 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 3, 8, 2]
def baseStart_812175 : Nat := 118140960795 + 812175 * 2 ^ 59
def prefixEnd_812175 : Nat := 4983230072969 + 3 ^ 40 * 812175 * 2
def baseEnd_812175 : Nat := 417036150565465095277381

theorem tailTrace_812175 : CollatzResearch.WordTrace tailWord_812175 prefixEnd_812175 417036150565465095277381 := by
  unfold tailWord_812175
  simp only [CollatzResearch.WordTrace]
  refine ⟨29622455832636158291965979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19748303888424105527977319 29622455832636158291965979)
  ·
    refine ⟨44433683748954237437948969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29622455832636158291965979 44433683748954237437948969)
    ·
      refine ⟨33325262811715678078461727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44433683748954237437948969 33325262811715678078461727)
      ·
        refine ⟨49987894217573517117692591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33325262811715678078461727 49987894217573517117692591)
        ·
          refine ⟨74981841326360275676538887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49987894217573517117692591 74981841326360275676538887)
          ·
            refine ⟨112472761989540413514808331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74981841326360275676538887 112472761989540413514808331)
            ·
              refine ⟨168709142984310620272212497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112472761989540413514808331 168709142984310620272212497)
              ·
                refine ⟨126531857238232965204159373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168709142984310620272212497 126531857238232965204159373)
                ·
                  refine ⟨47449446464337361951559765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126531857238232965204159373 47449446464337361951559765)
                  ·
                    refine ⟨556048200753953460369841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47449446464337361951559765 556048200753953460369841)
                    ·
                      refine ⟨417036150565465095277381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556048200753953460369841 417036150565465095277381)
                      ·
                        rfl

theorem cell23_812175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 8, 2].length) (baseStart_812175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812175 prefixEnd_812175 := by exact prefixLift 812175
  have htrace : WordTrace (prefixWord ++ tailWord_812175) baseStart_812175 baseEnd_812175 := by
    simpa [prefixWord, tailWord_812175, baseEnd_812175] using wordTrace_append hprefix tailTrace_812175
  have hstable : (prefixWord ++ tailWord_812175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812175).length < 2 ^ (prefixWord ++ tailWord_812175).sum := by decide
  have hdescent : baseEnd_812175 < baseStart_812175 := by decide
  rcases family_descends (prefixWord ++ tailWord_812175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812202 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_812202 : Nat := 118140960795 + 812202 * 2 ^ 59
def prefixEnd_812202 : Nat := 4983230072969 + 3 ^ 40 * 812202 * 2
def baseEnd_812202 : Nat := 139016671514378829879919

theorem tailTrace_812202 : CollatzResearch.WordTrace tailWord_812202 prefixEnd_812202 139016671514378829879919 := by
  unfold tailWord_812202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405860150884585475799715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19748960402358894602132573 7405860150884585475799715)
  ·
    refine ⟨11108790226326878213699573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7405860150884585475799715 11108790226326878213699573)
    ·
      refine ⟨1041449083718144832534335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11108790226326878213699573 1041449083718144832534335)
      ·
        refine ⟨1562173625577217248801503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041449083718144832534335 1562173625577217248801503)
        ·
          refine ⟨2343260438365825873202255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562173625577217248801503 2343260438365825873202255)
          ·
            refine ⟨3514890657548738809803383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343260438365825873202255 3514890657548738809803383)
            ·
              refine ⟨5272335986323108214705075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514890657548738809803383 5272335986323108214705075)
              ·
                refine ⟨7908503979484662322057613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5272335986323108214705075 7908503979484662322057613)
                ·
                  refine ⟨2965688992306748370771605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7908503979484662322057613 2965688992306748370771605)
                  ·
                    refine ⟨139016671514378829879919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2965688992306748370771605 139016671514378829879919)
                    ·
                      rfl

theorem cell23_812202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_812202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812202 prefixEnd_812202 := by exact prefixLift 812202
  have htrace : WordTrace (prefixWord ++ tailWord_812202) baseStart_812202 baseEnd_812202 := by
    simpa [prefixWord, tailWord_812202, baseEnd_812202] using wordTrace_append hprefix tailTrace_812202
  have hstable : (prefixWord ++ tailWord_812202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812202).length < 2 ^ (prefixWord ++ tailWord_812202).sum := by decide
  have hdescent : baseEnd_812202 < baseStart_812202 := by decide
  rcases family_descends (prefixWord ++ tailWord_812202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812263 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_812263 : Nat := 118140960795 + 812263 * 2 ^ 59
def prefixEnd_812263 : Nat := 4983230072969 + 3 ^ 40 * 812263 * 2
def baseEnd_812263 : Nat := 417081336863060750976977

theorem tailTrace_812263 : CollatzResearch.WordTrace tailWord_812263 prefixEnd_812263 417081336863060750976977 := by
  unfold tailWord_812263
  simp only [CollatzResearch.WordTrace]
  refine ⟨29625665456317349321169443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19750443637544899547446295 29625665456317349321169443)
  ·
    refine ⟨44438498184476023981754165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29625665456317349321169443 44438498184476023981754165)
    ·
      refine ⟨4166109204794627248289453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44438498184476023981754165 4166109204794627248289453)
      ·
        refine ⟨1562290951797985218108545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4166109204794627248289453 1562290951797985218108545)
        ·
          refine ⟨1171718213848488913581409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1562290951797985218108545 1171718213848488913581409)
          ·
            refine ⟨878788660386366685186057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1171718213848488913581409 878788660386366685186057)
            ·
              refine ⟨659091495289775013889543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878788660386366685186057 659091495289775013889543)
              ·
                refine ⟨988637242934662520834315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659091495289775013889543 988637242934662520834315)
                ·
                  refine ⟨1482955864401993781251473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988637242934662520834315 1482955864401993781251473)
                  ·
                    refine ⟨1112216898301495335938605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1482955864401993781251473 1112216898301495335938605)
                    ·
                      refine ⟨417081336863060750976977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1112216898301495335938605 417081336863060750976977)
                      ·
                        rfl

theorem cell23_812263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_812263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812263 prefixEnd_812263 := by exact prefixLift 812263
  have htrace : WordTrace (prefixWord ++ tailWord_812263) baseStart_812263 baseEnd_812263 := by
    simpa [prefixWord, tailWord_812263, baseEnd_812263] using wordTrace_append hprefix tailTrace_812263
  have hstable : (prefixWord ++ tailWord_812263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812263).length < 2 ^ (prefixWord ++ tailWord_812263).sum := by decide
  have hdescent : baseEnd_812263 < baseStart_812263 := by decide
  rcases family_descends (prefixWord ++ tailWord_812263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812275 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 2, 6]
def baseStart_812275 : Nat := 118140960795 + 812275 * 2 ^ 59
def prefixEnd_812275 : Nat := 4983230072969 + 3 ^ 40 * 812275 * 2
def baseEnd_812275 : Nat := 139029166210304901342307

theorem tailTrace_812275 : CollatzResearch.WordTrace tailWord_812275 prefixEnd_812275 139029166210304901342307 := by
  unfold tailWord_812275
  simp only [CollatzResearch.WordTrace]
  refine ⟨29626103132273875370606279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19750735421515916913737519 29626103132273875370606279)
  ·
    refine ⟨44439154698410813055909419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29626103132273875370606279 44439154698410813055909419)
    ·
      refine ⟨66658732047616219583864129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44439154698410813055909419 66658732047616219583864129)
      ·
        refine ⟨49994049035712164687898097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66658732047616219583864129 49994049035712164687898097)
        ·
          refine ⟨37495536776784123515923573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49994049035712164687898097 37495536776784123515923573)
          ·
            refine ⟨3515206572823511579617835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37495536776784123515923573 3515206572823511579617835)
            ·
              refine ⟨5272809859235267369426753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515206572823511579617835 5272809859235267369426753)
              ·
                refine ⟨3954607394426450527070065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5272809859235267369426753 3954607394426450527070065)
                ·
                  refine ⟨2965955545819837895302549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3954607394426450527070065 2965955545819837895302549)
                  ·
                    refine ⟨139029166210304901342307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2965955545819837895302549 139029166210304901342307)
                    ·
                      rfl

theorem cell23_812275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 6].length) (baseStart_812275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812275 prefixEnd_812275 := by exact prefixLift 812275
  have htrace : WordTrace (prefixWord ++ tailWord_812275) baseStart_812275 baseEnd_812275 := by
    simpa [prefixWord, tailWord_812275, baseEnd_812275] using wordTrace_append hprefix tailTrace_812275
  have hstable : (prefixWord ++ tailWord_812275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812275).length < 2 ^ (prefixWord ++ tailWord_812275).sum := by decide
  have hdescent : baseEnd_812275 < baseStart_812275 := by decide
  rcases family_descends (prefixWord ++ tailWord_812275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812285 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_812285 : Nat := 118140960795 + 812285 * 2 ^ 59
def prefixEnd_812285 : Nat := 4983230072969 + 3 ^ 40 * 812285 * 2
def baseEnd_812285 : Nat := 417092633437459664901875

theorem tailTrace_812285 : CollatzResearch.WordTrace tailWord_812285 prefixEnd_812285 417092633437459664901875 := by
  unfold tailWord_812285
  simp only [CollatzResearch.WordTrace]
  refine ⟨29626467862237647078470309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19750978574825098052313539 29626467862237647078470309)
  ·
    refine ⟨5554962724169558827213183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29626467862237647078470309 5554962724169558827213183)
    ·
      refine ⟨8332444086254338240819775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5554962724169558827213183 8332444086254338240819775)
      ·
        refine ⟨12498666129381507361229663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8332444086254338240819775 12498666129381507361229663)
        ·
          refine ⟨18747999194072261041844495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12498666129381507361229663 18747999194072261041844495)
          ·
            refine ⟨28121998791108391562766743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18747999194072261041844495 28121998791108391562766743)
            ·
              refine ⟨42182998186662587344150115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28121998791108391562766743 42182998186662587344150115)
              ·
                refine ⟨63274497279993881016225173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42182998186662587344150115 63274497279993881016225173)
                ·
                  refine ⟨2965992059999713172635555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63274497279993881016225173 2965992059999713172635555)
                  ·
                    refine ⟨4448988089999569758953333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2965992059999713172635555 4448988089999569758953333)
                    ·
                      refine ⟨417092633437459664901875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4448988089999569758953333 417092633437459664901875)
                      ·
                        rfl

theorem cell23_812285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_812285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812285 prefixEnd_812285 := by exact prefixLift 812285
  have htrace : WordTrace (prefixWord ++ tailWord_812285) baseStart_812285 baseEnd_812285 := by
    simpa [prefixWord, tailWord_812285, baseEnd_812285] using wordTrace_append hprefix tailTrace_812285
  have hstable : (prefixWord ++ tailWord_812285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812285).length < 2 ^ (prefixWord ++ tailWord_812285).sum := by decide
  have hdescent : baseEnd_812285 < baseStart_812285 := by decide
  rcases family_descends (prefixWord ++ tailWord_812285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812292 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_812292 : Nat := 118140960795 + 812292 * 2 ^ 59
def prefixEnd_812292 : Nat := 4983230072969 + 3 ^ 40 * 812292 * 2
def baseEnd_812292 : Nat := 139032075934013712504781

theorem tailTrace_812292 : CollatzResearch.WordTrace tailWord_812292 prefixEnd_812292 139032075934013712504781 := by
  unfold tailWord_812292
  simp only [CollatzResearch.WordTrace]
  refine ⟨14813361586606143636987565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19751148782141524849316753 14813361586606143636987565)
  ·
    refine ⟨5555010594977303863870337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14813361586606143636987565 5555010594977303863870337)
    ·
      refine ⟨4166257946232977897902753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5555010594977303863870337 4166257946232977897902753)
      ·
        refine ⟨3124693459674733423427065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4166257946232977897902753 3124693459674733423427065)
        ·
          refine ⟨2343520094756050067570299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3124693459674733423427065 2343520094756050067570299)
          ·
            refine ⟨3515280142134075101355449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343520094756050067570299 3515280142134075101355449)
            ·
              refine ⟨2636460106600556326016587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3515280142134075101355449 2636460106600556326016587)
              ·
                refine ⟨3954690159900834489024881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636460106600556326016587 3954690159900834489024881)
                ·
                  refine ⟨2966017619925625866768661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3954690159900834489024881 2966017619925625866768661)
                  ·
                    refine ⟨139032075934013712504781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2966017619925625866768661 139032075934013712504781)
                    ·
                      rfl

theorem cell23_812292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_812292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812292 prefixEnd_812292 := by exact prefixLift 812292
  have htrace : WordTrace (prefixWord ++ tailWord_812292) baseStart_812292 baseEnd_812292 := by
    simpa [prefixWord, tailWord_812292, baseEnd_812292] using wordTrace_append hprefix tailTrace_812292
  have hstable : (prefixWord ++ tailWord_812292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812292).length < 2 ^ (prefixWord ++ tailWord_812292).sum := by decide
  have hdescent : baseEnd_812292 < baseStart_812292 := by decide
  rcases family_descends (prefixWord ++ tailWord_812292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812299 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 1, 4, 2]
def baseStart_812299 : Nat := 118140960795 + 812299 * 2 ^ 59
def prefixEnd_812299 : Nat := 4983230072969 + 3 ^ 40 * 812299 * 2
def baseEnd_812299 : Nat := 417099822166622610126811

theorem tailTrace_812299 : CollatzResearch.WordTrace tailWord_812299 prefixEnd_812299 417099822166622610126811 := by
  unfold tailWord_812299
  simp only [CollatzResearch.WordTrace]
  refine ⟨29626978484186927469479951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19751318989457951646319967 29626978484186927469479951)
  ·
    refine ⟨44440467726280391204219927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29626978484186927469479951 44440467726280391204219927)
    ·
      refine ⟨66660701589420586806329891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44440467726280391204219927 66660701589420586806329891)
      ·
        refine ⟨99991052384130880209494837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66660701589420586806329891 99991052384130880209494837)
        ·
          refine ⟨9374161161012270019640141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99991052384130880209494837 9374161161012270019640141)
          ·
            refine ⟨3515310435379601257365053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9374161161012270019640141 3515310435379601257365053)
            ·
              refine ⟨1318241413267350471511895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3515310435379601257365053 1318241413267350471511895)
              ·
                refine ⟨1977362119901025707267843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318241413267350471511895 1977362119901025707267843)
                ·
                  refine ⟨2966043179851538560901765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977362119901025707267843 2966043179851538560901765)
                  ·
                    refine ⟨556133096222163480169081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966043179851538560901765 556133096222163480169081)
                    ·
                      refine ⟨417099822166622610126811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556133096222163480169081 417099822166622610126811)
                      ·
                        rfl

theorem cell23_812299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 4, 2].length) (baseStart_812299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812299 prefixEnd_812299 := by exact prefixLift 812299
  have htrace : WordTrace (prefixWord ++ tailWord_812299) baseStart_812299 baseEnd_812299 := by
    simpa [prefixWord, tailWord_812299, baseEnd_812299] using wordTrace_append hprefix tailTrace_812299
  have hstable : (prefixWord ++ tailWord_812299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812299).length < 2 ^ (prefixWord ++ tailWord_812299).sum := by decide
  have hdescent : baseEnd_812299 < baseStart_812299 := by decide
  rcases family_descends (prefixWord ++ tailWord_812299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812305 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 7]
def baseStart_812305 : Nat := 118140960795 + 812305 * 2 ^ 59
def prefixEnd_812305 : Nat := 4983230072969 + 3 ^ 40 * 812305 * 2
def baseEnd_812305 : Nat := 46344767005616620739087

theorem tailTrace_812305 : CollatzResearch.WordTrace tailWord_812305 prefixEnd_812305 46344767005616620739087 := by
  unfold tailWord_812305
  simp only [CollatzResearch.WordTrace]
  refine ⟨29627197322165190494198369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19751464881443460329465579 29627197322165190494198369)
  ·
    refine ⟨22220397991623892870648777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29627197322165190494198369 22220397991623892870648777)
    ·
      refine ⟨16665298493717919652986583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22220397991623892870648777 16665298493717919652986583)
      ·
        refine ⟨24997947740576879479479875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16665298493717919652986583 24997947740576879479479875)
        ·
          refine ⟨37496921610865319219219813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24997947740576879479479875 37496921610865319219219813)
          ·
            refine ⟨7030672802037247353603715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37496921610865319219219813 7030672802037247353603715)
            ·
              refine ⟨10546009203055871030405573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030672802037247353603715 10546009203055871030405573)
              ·
                refine ⟨1977376725572975818201045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10546009203055871030405573 1977376725572975818201045)
                ·
                  refine ⟨46344767005616620739087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1977376725572975818201045 46344767005616620739087)
                  ·
                    rfl

theorem cell23_812305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 7].length) (baseStart_812305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812305 prefixEnd_812305 := by exact prefixLift 812305
  have htrace : WordTrace (prefixWord ++ tailWord_812305) baseStart_812305 baseEnd_812305 := by
    simpa [prefixWord, tailWord_812305, baseEnd_812305] using wordTrace_append hprefix tailTrace_812305
  have hstable : (prefixWord ++ tailWord_812305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812305).length < 2 ^ (prefixWord ++ tailWord_812305).sum := by decide
  have hdescent : baseEnd_812305 < baseStart_812305 := by decide
  rcases family_descends (prefixWord ++ tailWord_812305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812333 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_812333 : Nat := 118140960795 + 812333 * 2 ^ 59
def prefixEnd_812333 : Nat := 4983230072969 + 3 ^ 40 * 812333 * 2
def baseEnd_812333 : Nat := 417117280508875477101655

theorem tailTrace_812333 : CollatzResearch.WordTrace tailWord_812333 prefixEnd_812333 417117280508875477101655 := by
  unfold tailWord_812333
  simp only [CollatzResearch.WordTrace]
  refine ⟨29628218566063751276217653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19752145710709167517478435 29628218566063751276217653)
  ·
    refine ⟨2777645490568476682145405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29628218566063751276217653 2777645490568476682145405)
    ·
      refine ⟨1041617058963178755804527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2777645490568476682145405 1041617058963178755804527)
      ·
        refine ⟨1562425588444768133706791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041617058963178755804527 1562425588444768133706791)
        ·
          refine ⟨2343638382667152200560187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562425588444768133706791 2343638382667152200560187)
          ·
            refine ⟨3515457574000728300840281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343638382667152200560187 3515457574000728300840281)
            ·
              refine ⟨2636593180500546225630211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3515457574000728300840281 2636593180500546225630211)
              ·
                refine ⟨3954889770750819338445317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636593180500546225630211 3954889770750819338445317)
                ·
                  refine ⟨741541832015778625958497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3954889770750819338445317 741541832015778625958497)
                  ·
                    refine ⟨556156374011833969468873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 741541832015778625958497 556156374011833969468873)
                    ·
                      refine ⟨417117280508875477101655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556156374011833969468873 417117280508875477101655)
                      ·
                        rfl

theorem cell23_812333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_812333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812333 prefixEnd_812333 := by exact prefixLift 812333
  have htrace : WordTrace (prefixWord ++ tailWord_812333) baseStart_812333 baseEnd_812333 := by
    simpa [prefixWord, tailWord_812333, baseEnd_812333] using wordTrace_append hprefix tailTrace_812333
  have hstable : (prefixWord ++ tailWord_812333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812333).length < 2 ^ (prefixWord ++ tailWord_812333).sum := by decide
  have hdescent : baseEnd_812333 < baseStart_812333 := by decide
  rcases family_descends (prefixWord ++ tailWord_812333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812389 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 2, 4, 2]
def baseStart_812389 : Nat := 118140960795 + 812389 * 2 ^ 59
def prefixEnd_812389 : Nat := 4983230072969 + 3 ^ 40 * 812389 * 2
def baseEnd_812389 : Nat := 417146035425527258001397

theorem tailTrace_812389 : CollatzResearch.WordTrace tailWord_812389 prefixEnd_812389 417146035425527258001397 := by
  unfold tailWord_812389
  simp only [CollatzResearch.WordTrace]
  refine ⟨29630261053860872840256221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19753507369240581893504147 29630261053860872840256221)
  ·
    refine ⟨11111347895197827315096083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29630261053860872840256221 11111347895197827315096083)
    ·
      refine ⟨16667021842796740972644125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11111347895197827315096083 16667021842796740972644125)
      ·
        refine ⟨6250133191048777864741547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16667021842796740972644125 6250133191048777864741547)
        ·
          refine ⟨9375199786573166797112321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6250133191048777864741547 9375199786573166797112321)
          ·
            refine ⟨7031399839929875097834241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9375199786573166797112321 7031399839929875097834241)
            ·
              refine ⟨5273549879947406323375681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7031399839929875097834241 5273549879947406323375681)
              ·
                refine ⟨3955162409960554742531761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5273549879947406323375681 3955162409960554742531761)
                ·
                  refine ⟨2966371807470416056898821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3955162409960554742531761 2966371807470416056898821)
                  ·
                    refine ⟨556194713900703010668529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966371807470416056898821 556194713900703010668529)
                    ·
                      refine ⟨417146035425527258001397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556194713900703010668529 417146035425527258001397)
                      ·
                        rfl

theorem cell23_812389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_812389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812389 prefixEnd_812389 := by exact prefixLift 812389
  have htrace : WordTrace (prefixWord ++ tailWord_812389) baseStart_812389 baseEnd_812389 := by
    simpa [prefixWord, tailWord_812389, baseEnd_812389] using wordTrace_append hprefix tailTrace_812389
  have hstable : (prefixWord ++ tailWord_812389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812389).length < 2 ^ (prefixWord ++ tailWord_812389).sum := by decide
  have hdescent : baseEnd_812389 < baseStart_812389 := by decide
  rcases family_descends (prefixWord ++ tailWord_812389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812412 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 6]
def baseStart_812412 : Nat := 118140960795 + 812412 * 2 ^ 59
def prefixEnd_812412 : Nat := 4983230072969 + 3 ^ 40 * 812412 * 2
def baseEnd_812412 : Nat := 46350871720064518668199

theorem tailTrace_812412 : CollatzResearch.WordTrace tailWord_812412 prefixEnd_812412 46350871720064518668199 := by
  unfold tailWord_812412
  simp only [CollatzResearch.WordTrace]
  refine ⟨14815549966388773884171745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19754066621851698512228993 14815549966388773884171745)
  ·
    refine ⟨11111662474791580413128809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14815549966388773884171745 11111662474791580413128809)
    ·
      refine ⟨8333746856093685309846607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11111662474791580413128809 8333746856093685309846607)
      ·
        refine ⟨12500620284140527964769911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8333746856093685309846607 12500620284140527964769911)
        ·
          refine ⟨18750930426210791947154867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12500620284140527964769911 18750930426210791947154867)
          ·
            refine ⟨28126395639316187920732301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18750930426210791947154867 28126395639316187920732301)
            ·
              refine ⟨10547398364743570470274613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28126395639316187920732301 10547398364743570470274613)
              ·
                refine ⟨988818596694709731588245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10547398364743570470274613 988818596694709731588245)
                ·
                  refine ⟨46350871720064518668199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 988818596694709731588245 46350871720064518668199)
                  ·
                    rfl

theorem cell23_812412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_812412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812412 prefixEnd_812412 := by exact prefixLift 812412
  have htrace : WordTrace (prefixWord ++ tailWord_812412) baseStart_812412 baseEnd_812412 := by
    simpa [prefixWord, tailWord_812412, baseEnd_812412] using wordTrace_append hprefix tailTrace_812412
  have hstable : (prefixWord ++ tailWord_812412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812412).length < 2 ^ (prefixWord ++ tailWord_812412).sum := by decide
  have hdescent : baseEnd_812412 < baseStart_812412 := by decide
  rcases family_descends (prefixWord ++ tailWord_812412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812439 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 7, 1, 3]
def baseStart_812439 : Nat := 118140960795 + 812439 * 2 ^ 59
def prefixEnd_812439 : Nat := 4983230072969 + 3 ^ 40 * 812439 * 2
def baseEnd_812439 : Nat := 417171709458252062376167

theorem tailTrace_812439 : CollatzResearch.WordTrace tailWord_812439 prefixEnd_812439 417171709458252062376167 := by
  unfold tailWord_812439
  simp only [CollatzResearch.WordTrace]
  refine ⟨29632084703679731379576371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19754723135786487586384247 29632084703679731379576371)
  ·
    refine ⟨44448127055519597069364557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29632084703679731379576371 44448127055519597069364557)
    ·
      refine ⟨16668047645819848901011709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44448127055519597069364557 16668047645819848901011709)
      ·
        refine ⟨6250517867182443337879391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16668047645819848901011709 6250517867182443337879391)
        ·
          refine ⟨9375776800773665006819087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6250517867182443337879391 9375776800773665006819087)
          ·
            refine ⟨14063665201160497510228631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9375776800773665006819087 14063665201160497510228631)
            ·
              refine ⟨21095497801740746265342947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14063665201160497510228631 21095497801740746265342947)
              ·
                refine ⟨31643246702611119398014421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21095497801740746265342947 31643246702611119398014421)
                ·
                  refine ⟨741638594592448110890963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 31643246702611119398014421 741638594592448110890963)
                  ·
                    refine ⟨1112457891888672166336445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 741638594592448110890963 1112457891888672166336445)
                    ·
                      refine ⟨417171709458252062376167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1112457891888672166336445 417171709458252062376167)
                      ·
                        rfl

theorem cell23_812439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_812439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812439 prefixEnd_812439 := by exact prefixLift 812439
  have htrace : WordTrace (prefixWord ++ tailWord_812439) baseStart_812439 baseEnd_812439 := by
    simpa [prefixWord, tailWord_812439, baseEnd_812439] using wordTrace_append hprefix tailTrace_812439
  have hstable : (prefixWord ++ tailWord_812439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812439).length < 2 ^ (prefixWord ++ tailWord_812439).sum := by decide
  have hdescent : baseEnd_812439 < baseStart_812439 := by decide
  rcases family_descends (prefixWord ++ tailWord_812439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812446 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_812446 : Nat := 118140960795 + 812446 * 2 ^ 59
def prefixEnd_812446 : Nat := 4983230072969 + 3 ^ 40 * 812446 * 2
def baseEnd_812446 : Nat := 46352811535870392776515

theorem tailTrace_812446 : CollatzResearch.WordTrace tailWord_812446 prefixEnd_812446 46352811535870392776515 := by
  unfold tailWord_812446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3704042501831796446885149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19754893343102914383387461 3704042501831796446885149)
  ·
    refine ⟨1389015938186923667581931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3704042501831796446885149 1389015938186923667581931)
    ·
      refine ⟨2083523907280385501372897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1389015938186923667581931 2083523907280385501372897)
      ·
        refine ⟨1562642930460289126029673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2083523907280385501372897 1562642930460289126029673)
        ·
          refine ⟨1171982197845216844522255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1562642930460289126029673 1171982197845216844522255)
          ·
            refine ⟨1757973296767825266783383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171982197845216844522255 1757973296767825266783383)
            ·
              refine ⟨2636959945151737900175075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757973296767825266783383 2636959945151737900175075)
              ·
                refine ⟨3955439917727606850262613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636959945151737900175075 3955439917727606850262613)
                ·
                  refine ⟨46352811535870392776515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3955439917727606850262613 46352811535870392776515)
                  ·
                    rfl

theorem cell23_812446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_812446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812446 prefixEnd_812446 := by exact prefixLift 812446
  have htrace : WordTrace (prefixWord ++ tailWord_812446) baseStart_812446 baseEnd_812446 := by
    simpa [prefixWord, tailWord_812446, baseEnd_812446] using wordTrace_append hprefix tailTrace_812446
  have hstable : (prefixWord ++ tailWord_812446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812446).length < 2 ^ (prefixWord ++ tailWord_812446).sum := by decide
  have hdescent : baseEnd_812446 < baseStart_812446 := by decide
  rcases family_descends (prefixWord ++ tailWord_812446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812490 : List Nat := [3, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3]
def baseStart_812490 : Nat := 118140960795 + 812490 * 2 ^ 59
def prefixEnd_812490 : Nat := 4983230072969 + 3 ^ 40 * 812490 * 2
def baseEnd_812490 : Nat := 417197896971631362838433

theorem tailTrace_812490 : CollatzResearch.WordTrace tailWord_812490 prefixEnd_812490 417197896971631362838433 := by
  unfold tailWord_812490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7408486206623741772420731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19755963217663311393121949 7408486206623741772420731)
  ·
    refine ⟨11112729309935612658631097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7408486206623741772420731 11112729309935612658631097)
    ·
      refine ⟨8334546982451709493973323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11112729309935612658631097 8334546982451709493973323)
      ·
        refine ⟨12501820473677564240959985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8334546982451709493973323 12501820473677564240959985)
        ·
          refine ⟨9376365355258173180719989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12501820473677564240959985 9376365355258173180719989)
          ·
            refine ⟨879034252055453735692499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9376365355258173180719989 879034252055453735692499)
            ·
              refine ⟨1318551378083180603538749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879034252055453735692499 1318551378083180603538749)
              ·
                refine ⟨494456766781192726327031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1318551378083180603538749 494456766781192726327031)
                ·
                  refine ⟨741685150171789089490547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494456766781192726327031 741685150171789089490547)
                  ·
                    refine ⟨1112527725257683634235821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 741685150171789089490547 1112527725257683634235821)
                    ·
                      refine ⟨417197896971631362838433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1112527725257683634235821 417197896971631362838433)
                      ·
                        rfl

theorem cell23_812490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_812490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812490 prefixEnd_812490 := by exact prefixLift 812490
  have htrace : WordTrace (prefixWord ++ tailWord_812490) baseStart_812490 baseEnd_812490 := by
    simpa [prefixWord, tailWord_812490, baseEnd_812490] using wordTrace_append hprefix tailTrace_812490
  have hstable : (prefixWord ++ tailWord_812490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812490).length < 2 ^ (prefixWord ++ tailWord_812490).sum := by decide
  have hdescent : baseEnd_812490 < baseStart_812490 := by decide
  rcases family_descends (prefixWord ++ tailWord_812490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812509 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_812509 : Nat := 118140960795 + 812509 * 2 ^ 59
def prefixEnd_812509 : Nat := 4983230072969 + 3 ^ 40 * 812509 * 2
def baseEnd_812509 : Nat := 417207653104066788500845

theorem tailTrace_812509 : CollatzResearch.WordTrace tailWord_812509 prefixEnd_812509 417207653104066788500845 := by
  unfold tailWord_812509
  simp only [CollatzResearch.WordTrace]
  refine ⟨29634637813426133334624581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19756425208950755556416387 29634637813426133334624581)
  ·
    refine ⟨5556494590017400000242109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29634637813426133334624581 5556494590017400000242109)
    ·
      refine ⟨2083685471256525000090791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5556494590017400000242109 2083685471256525000090791)
      ·
        refine ⟨3125528206884787500136187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083685471256525000090791 3125528206884787500136187)
        ·
          refine ⟨4688292310327181250204281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125528206884787500136187 4688292310327181250204281)
          ·
            refine ⟨3516219232745385937653211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4688292310327181250204281 3516219232745385937653211)
            ·
              refine ⟨5274328849118078906479817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3516219232745385937653211 5274328849118078906479817)
              ·
                refine ⟨3955746636838559179859863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5274328849118078906479817 3955746636838559179859863)
                ·
                  refine ⟨5933619955257838769789795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955746636838559179859863 5933619955257838769789795)
                  ·
                    refine ⟨8900429932886758154684693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5933619955257838769789795 8900429932886758154684693)
                    ·
                      refine ⟨417207653104066788500845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8900429932886758154684693 417207653104066788500845)
                      ·
                        rfl

theorem cell23_812509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_812509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812509 prefixEnd_812509 := by exact prefixLift 812509
  have htrace : WordTrace (prefixWord ++ tailWord_812509) baseStart_812509 baseEnd_812509 := by
    simpa [prefixWord, tailWord_812509, baseEnd_812509] using wordTrace_append hprefix tailTrace_812509
  have hstable : (prefixWord ++ tailWord_812509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812509).length < 2 ^ (prefixWord ++ tailWord_812509).sum := by decide
  have hdescent : baseEnd_812509 < baseStart_812509 := by decide
  rcases family_descends (prefixWord ++ tailWord_812509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812513 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 3, 2, 2]
def baseStart_812513 : Nat := 118140960795 + 812513 * 2 ^ 59
def prefixEnd_812513 : Nat := 4983230072969 + 3 ^ 40 * 812513 * 2
def baseEnd_812513 : Nat := 417209707026684772850827

theorem tailTrace_812513 : CollatzResearch.WordTrace tailWord_812513 prefixEnd_812513 417209707026684772850827 := by
  unfold tailWord_812513
  simp only [CollatzResearch.WordTrace]
  refine ⟨29634783705411642017770193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19756522470274428011846795 29634783705411642017770193)
  ·
    refine ⟨22226087779058731513327645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29634783705411642017770193 22226087779058731513327645)
    ·
      refine ⟨8334782917147024317497867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22226087779058731513327645 8334782917147024317497867)
      ·
        refine ⟨12502174375720536476246801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8334782917147024317497867 12502174375720536476246801)
        ·
          refine ⟨9376630781790402357185101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12502174375720536476246801 9376630781790402357185101)
          ·
            refine ⟨3516236543171400883944413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9376630781790402357185101 3516236543171400883944413)
            ·
              refine ⟨1318588703689275331479155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3516236543171400883944413 1318588703689275331479155)
              ·
                refine ⟨1977883055533912997218733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318588703689275331479155 1977883055533912997218733)
                ·
                  refine ⟨741706145825217373957025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1977883055533912997218733 741706145825217373957025)
                  ·
                    refine ⟨556279609368913030467769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 741706145825217373957025 556279609368913030467769)
                    ·
                      refine ⟨417209707026684772850827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556279609368913030467769 417209707026684772850827)
                      ·
                        rfl

theorem cell23_812513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_812513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812513 prefixEnd_812513 := by exact prefixLift 812513
  have htrace : WordTrace (prefixWord ++ tailWord_812513) baseStart_812513 baseEnd_812513 := by
    simpa [prefixWord, tailWord_812513, baseEnd_812513] using wordTrace_append hprefix tailTrace_812513
  have hstable : (prefixWord ++ tailWord_812513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812513).length < 2 ^ (prefixWord ++ tailWord_812513).sum := by decide
  have hdescent : baseEnd_812513 < baseStart_812513 := by decide
  rcases family_descends (prefixWord ++ tailWord_812513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812519 : List Nat := [1, 1, 5, 2, 1, 3, 2, 8]
def baseStart_812519 : Nat := 118140960795 + 812519 * 2 ^ 59
def prefixEnd_812519 : Nat := 4983230072969 + 3 ^ 40 * 812519 * 2
def baseEnd_812519 : Nat := 15452325478170805532437

theorem tailTrace_812519 : CollatzResearch.WordTrace tailWord_812519 prefixEnd_812519 15452325478170805532437 := by
  unfold tailWord_812519
  simp only [CollatzResearch.WordTrace]
  refine ⟨29635002543389905042488611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19756668362259936694992407 29635002543389905042488611)
  ·
    refine ⟨44452503815084857563732917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29635002543389905042488611 44452503815084857563732917)
    ·
      refine ⟨4167422232664205396599961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44452503815084857563732917 4167422232664205396599961)
      ·
        refine ⟨3125566674498154047449971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4167422232664205396599961 3125566674498154047449971)
        ·
          refine ⟨4688350011747231071174957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125566674498154047449971 4688350011747231071174957)
          ·
            refine ⟨1758131254405211651690609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4688350011747231071174957 1758131254405211651690609)
            ·
              refine ⟨1318598440803908738767957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758131254405211651690609 1318598440803908738767957)
              ·
                refine ⟨15452325478170805532437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1318598440803908738767957 15452325478170805532437)
                ·
                  rfl

theorem cell23_812519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 8].length) (baseStart_812519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812519 prefixEnd_812519 := by exact prefixLift 812519
  have htrace : WordTrace (prefixWord ++ tailWord_812519) baseStart_812519 baseEnd_812519 := by
    simpa [prefixWord, tailWord_812519, baseEnd_812519] using wordTrace_append hprefix tailTrace_812519
  have hstable : (prefixWord ++ tailWord_812519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812519).length < 2 ^ (prefixWord ++ tailWord_812519).sum := by decide
  have hdescent : baseEnd_812519 < baseStart_812519 := by decide
  rcases family_descends (prefixWord ++ tailWord_812519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812533 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_812533 : Nat := 118140960795 + 812533 * 2 ^ 59
def prefixEnd_812533 : Nat := 4983230072969 + 3 ^ 40 * 812533 * 2
def baseEnd_812533 : Nat := 417219976639774694600735

theorem tailTrace_812533 : CollatzResearch.WordTrace tailWord_812533 prefixEnd_812533 417219976639774694600735 := by
  unfold tailWord_812533
  simp only [CollatzResearch.WordTrace]
  refine ⟨29635513165339185433498253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19757008776892790288998835 29635513165339185433498253)
  ·
    refine ⟨11113317437002194537561845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29635513165339185433498253 11113317437002194537561845)
    ·
      refine ⟨1041873509718955737896423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11113317437002194537561845 1041873509718955737896423)
      ·
        refine ⟨1562810264578433606844635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041873509718955737896423 1562810264578433606844635)
        ·
          refine ⟨2344215396867650410266953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562810264578433606844635 2344215396867650410266953)
          ·
            refine ⟨1758161547650737807700215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2344215396867650410266953 1758161547650737807700215)
            ·
              refine ⟨2637242321476106711550323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758161547650737807700215 2637242321476106711550323)
              ·
                refine ⟨3955863482214160067325485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637242321476106711550323 3955863482214160067325485)
                ·
                  refine ⟨1483448805830310025247057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3955863482214160067325485 1483448805830310025247057)
                  ·
                    refine ⟨1112586604372732518935293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1483448805830310025247057 1112586604372732518935293)
                    ·
                      refine ⟨417219976639774694600735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1112586604372732518935293 417219976639774694600735)
                      ·
                        rfl

theorem cell23_812533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_812533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812533 prefixEnd_812533 := by exact prefixLift 812533
  have htrace : WordTrace (prefixWord ++ tailWord_812533) baseStart_812533 baseEnd_812533 := by
    simpa [prefixWord, tailWord_812533, baseEnd_812533] using wordTrace_append hprefix tailTrace_812533
  have hstable : (prefixWord ++ tailWord_812533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812533).length < 2 ^ (prefixWord ++ tailWord_812533).sum := by decide
  have hdescent : baseEnd_812533 < baseStart_812533 := by decide
  rcases family_descends (prefixWord ++ tailWord_812533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812539 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 2, 7, 2]
def baseStart_812539 : Nat := 118140960795 + 812539 * 2 ^ 59
def prefixEnd_812539 : Nat := 4983230072969 + 3 ^ 40 * 812539 * 2
def baseEnd_812539 : Nat := 417223057523701671125707

theorem tailTrace_812539 : CollatzResearch.WordTrace tailWord_812539 prefixEnd_812539 417223057523701671125707 := by
  unfold tailWord_812539
  simp only [CollatzResearch.WordTrace]
  refine ⟨29635732003317448458216671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19757154668878298972144447 29635732003317448458216671)
  ·
    refine ⟨44453598004976172687325007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29635732003317448458216671 44453598004976172687325007)
    ·
      refine ⟨66680397007464259030987511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44453598004976172687325007 66680397007464259030987511)
      ·
        refine ⟨100020595511196388546481267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66680397007464259030987511 100020595511196388546481267)
        ·
          refine ⟨150030893266794582819721901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100020595511196388546481267 150030893266794582819721901)
          ·
            refine ⟨56261584975047968557395713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150030893266794582819721901 56261584975047968557395713)
            ·
              refine ⟨42196188731285976418046785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56261584975047968557395713 42196188731285976418046785)
              ·
                refine ⟨31647141548464482313535089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42196188731285976418046785 31647141548464482313535089)
                ·
                  refine ⟨23735356161348361735151317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31647141548464482313535089 23735356161348361735151317)
                  ·
                    refine ⟨556297410031602228167609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23735356161348361735151317 556297410031602228167609)
                    ·
                      refine ⟨417223057523701671125707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556297410031602228167609 417223057523701671125707)
                      ·
                        rfl

theorem cell23_812539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 7, 2].length) (baseStart_812539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812539 prefixEnd_812539 := by exact prefixLift 812539
  have htrace : WordTrace (prefixWord ++ tailWord_812539) baseStart_812539 baseEnd_812539 := by
    simpa [prefixWord, tailWord_812539, baseEnd_812539] using wordTrace_append hprefix tailTrace_812539
  have hstable : (prefixWord ++ tailWord_812539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812539).length < 2 ^ (prefixWord ++ tailWord_812539).sum := by decide
  have hdescent : baseEnd_812539 < baseStart_812539 := by decide
  rcases family_descends (prefixWord ++ tailWord_812539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812557 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_812557 : Nat := 118140960795 + 812557 * 2 ^ 59
def prefixEnd_812557 : Nat := 4983230072969 + 3 ^ 40 * 812557 * 2
def baseEnd_812557 : Nat := 139077433391827533566875

theorem tailTrace_812557 : CollatzResearch.WordTrace tailWord_812557 prefixEnd_812557 139077433391827533566875 := by
  unfold tailWord_812557
  simp only [CollatzResearch.WordTrace]
  refine ⟨29636388517252237532371925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19757592344834825021581283 29636388517252237532371925)
  ·
    refine ⟨694602855873099317164967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 29636388517252237532371925 694602855873099317164967)
    ·
      refine ⟨1041904283809648975747451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 694602855873099317164967 1041904283809648975747451)
      ·
        refine ⟨1562856425714473463621177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041904283809648975747451 1562856425714473463621177)
        ·
          refine ⟨1172142319285855097715883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1562856425714473463621177 1172142319285855097715883)
          ·
            refine ⟨1758213478928782646573825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172142319285855097715883 1758213478928782646573825)
            ·
              refine ⟨1318660109196586984930369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758213478928782646573825 1318660109196586984930369)
              ·
                refine ⟨988995081897440238697777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318660109196586984930369 988995081897440238697777)
                ·
                  refine ⟨741746311423080179023333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 988995081897440238697777 741746311423080179023333)
                  ·
                    refine ⟨139077433391827533566875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 741746311423080179023333 139077433391827533566875)
                    ·
                      rfl

theorem cell23_812557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_812557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812557 prefixEnd_812557 := by exact prefixLift 812557
  have htrace : WordTrace (prefixWord ++ tailWord_812557) baseStart_812557 baseEnd_812557 := by
    simpa [prefixWord, tailWord_812557, baseEnd_812557] using wordTrace_append hprefix tailTrace_812557
  have hstable : (prefixWord ++ tailWord_812557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812557).length < 2 ^ (prefixWord ++ tailWord_812557).sum := by decide
  have hdescent : baseEnd_812557 < baseStart_812557 := by decide
  rcases family_descends (prefixWord ++ tailWord_812557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812563 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 2, 1, 3]
def baseStart_812563 : Nat := 118140960795 + 812563 * 2 ^ 59
def prefixEnd_812563 : Nat := 4983230072969 + 3 ^ 40 * 812563 * 2
def baseEnd_812563 : Nat := 417235381059409577225597

theorem tailTrace_812563 : CollatzResearch.WordTrace tailWord_812563 prefixEnd_812563 417235381059409577225597 := by
  unfold tailWord_812563
  simp only [CollatzResearch.WordTrace]
  refine ⟨29636607355230500557090343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19757738236820333704726895 29636607355230500557090343)
  ·
    refine ⟨44454911032845750835635515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29636607355230500557090343 44454911032845750835635515)
    ·
      refine ⟨66682366549268626253453273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44454911032845750835635515 66682366549268626253453273)
      ·
        refine ⟨50011774911951469690089955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66682366549268626253453273 50011774911951469690089955)
        ·
          refine ⟨75017662367927204535134933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50011774911951469690089955 75017662367927204535134933)
          ·
            refine ⟨1758226461748293856292225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 75017662367927204535134933 1758226461748293856292225)
            ·
              refine ⟨1318669846311220392219169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758226461748293856292225 1318669846311220392219169)
              ·
                refine ⟨989002384733415294164377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318669846311220392219169 989002384733415294164377)
                ·
                  refine ⟨741751788550061470623283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989002384733415294164377 741751788550061470623283)
                  ·
                    refine ⟨1112627682825092205934925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 741751788550061470623283 1112627682825092205934925)
                    ·
                      refine ⟨417235381059409577225597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1112627682825092205934925 417235381059409577225597)
                      ·
                        rfl

theorem cell23_812563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 1, 3].length) (baseStart_812563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812563 prefixEnd_812563 := by exact prefixLift 812563
  have htrace : WordTrace (prefixWord ++ tailWord_812563) baseStart_812563 baseEnd_812563 := by
    simpa [prefixWord, tailWord_812563, baseEnd_812563] using wordTrace_append hprefix tailTrace_812563
  have hstable : (prefixWord ++ tailWord_812563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812563).length < 2 ^ (prefixWord ++ tailWord_812563).sum := by decide
  have hdescent : baseEnd_812563 < baseStart_812563 := by decide
  rcases family_descends (prefixWord ++ tailWord_812563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812564 : List Nat := [2, 4, 3, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_812564 : Nat := 118140960795 + 812564 * 2 ^ 59
def prefixEnd_812564 : Nat := 4983230072969 + 3 ^ 40 * 812564 * 2
def baseEnd_812564 : Nat := 417235894540064073313093

theorem tailTrace_812564 : CollatzResearch.WordTrace tailWord_812564 prefixEnd_812564 417235894540064073313093 := by
  unfold tailWord_812564
  simp only [CollatzResearch.WordTrace]
  refine ⟨14818321914113438863938373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19757762552151251818584497 14818321914113438863938373)
  ·
    refine ⟨2778435358896269786988445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14818321914113438863938373 2778435358896269786988445)
    ·
      refine ⟨1041913259586101170120667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2778435358896269786988445 1041913259586101170120667)
      ·
        refine ⟨1562869889379151755181001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041913259586101170120667 1562869889379151755181001)
        ·
          refine ⟨1172152417034363816385751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1562869889379151755181001 1172152417034363816385751)
          ·
            refine ⟨1758228625551545724578627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172152417034363816385751 1758228625551545724578627)
            ·
              refine ⟨2637342938327318586867941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758228625551545724578627 2637342938327318586867941)
              ·
                refine ⟨494501800936372235037739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2637342938327318586867941 494501800936372235037739)
                ·
                  refine ⟨741752701404558352556609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494501800936372235037739 741752701404558352556609)
                  ·
                    refine ⟨556314526053418764417457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 741752701404558352556609 556314526053418764417457)
                    ·
                      refine ⟨417235894540064073313093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556314526053418764417457 417235894540064073313093)
                      ·
                        rfl

theorem cell23_812564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_812564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812564 prefixEnd_812564 := by exact prefixLift 812564
  have htrace : WordTrace (prefixWord ++ tailWord_812564) baseStart_812564 baseEnd_812564 := by
    simpa [prefixWord, tailWord_812564, baseEnd_812564] using wordTrace_append hprefix tailTrace_812564
  have hstable : (prefixWord ++ tailWord_812564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812564).length < 2 ^ (prefixWord ++ tailWord_812564).sum := by decide
  have hdescent : baseEnd_812564 < baseStart_812564 := by decide
  rcases family_descends (prefixWord ++ tailWord_812564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812609 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 9]
def baseStart_812609 : Nat := 118140960795 + 812609 * 2 ^ 59
def prefixEnd_812609 : Nat := 4983230072969 + 3 ^ 40 * 812609 * 2
def baseEnd_812609 : Nat := 46362111241057377472265

theorem tailTrace_812609 : CollatzResearch.WordTrace tailWord_812609 prefixEnd_812609 46362111241057377472265 := by
  unfold tailWord_812609
  simp only [CollatzResearch.WordTrace]
  refine ⟨29638285113063850413264881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19758856742042566942176587 29638285113063850413264881)
  ·
    refine ⟨22228713834797887809948661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29638285113063850413264881 22228713834797887809948661)
    ·
      refine ⟨2083941922012301982182687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22228713834797887809948661 2083941922012301982182687)
      ·
        refine ⟨3125912883018452973274031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083941922012301982182687 3125912883018452973274031)
        ·
          refine ⟨4688869324527679459911047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125912883018452973274031 4688869324527679459911047)
          ·
            refine ⟨7033303986791519189866571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4688869324527679459911047 7033303986791519189866571)
            ·
              refine ⟨10549955980187278784799857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7033303986791519189866571 10549955980187278784799857)
              ·
                refine ⟨7912466985140459088599893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10549955980187278784799857 7912466985140459088599893)
                ·
                  refine ⟨46362111241057377472265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7912466985140459088599893 46362111241057377472265)
                  ·
                    rfl

theorem cell23_812609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 9].length) (baseStart_812609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812609 prefixEnd_812609 := by exact prefixLift 812609
  have htrace : WordTrace (prefixWord ++ tailWord_812609) baseStart_812609 baseEnd_812609 := by
    simpa [prefixWord, tailWord_812609, baseEnd_812609] using wordTrace_append hprefix tailTrace_812609
  have hstable : (prefixWord ++ tailWord_812609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812609).length < 2 ^ (prefixWord ++ tailWord_812609).sum := by decide
  have hdescent : baseEnd_812609 < baseStart_812609 := by decide
  rcases family_descends (prefixWord ++ tailWord_812609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812614 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_812614 : Nat := 118140960795 + 812614 * 2 ^ 59
def prefixEnd_812614 : Nat := 4983230072969 + 3 ^ 40 * 812614 * 2
def baseEnd_812614 : Nat := 417261568572788877687863

theorem tailTrace_812614 : CollatzResearch.WordTrace tailWord_812614 prefixEnd_812614 417261568572788877687863 := by
  unfold tailWord_812614
  simp only [CollatzResearch.WordTrace]
  refine ⟨926202108688929258349903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19758978318697157511464597 926202108688929258349903)
  ·
    refine ⟨1389303163033393887524855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 926202108688929258349903 1389303163033393887524855)
    ·
      refine ⟨2083954744550090831287283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1389303163033393887524855 2083954744550090831287283)
      ·
        refine ⟨3125932116825136246930925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083954744550090831287283 3125932116825136246930925)
        ·
          refine ⟨1172224543809426092599097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3125932116825136246930925 1172224543809426092599097)
          ·
            refine ⟨879168407857069569449323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1172224543809426092599097 879168407857069569449323)
            ·
              refine ⟨1318752611785604354173985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879168407857069569449323 1318752611785604354173985)
              ·
                refine ⟨989064458839203265630489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318752611785604354173985 989064458839203265630489)
                ·
                  refine ⟨741798344129402449222867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989064458839203265630489 741798344129402449222867)
                  ·
                    refine ⟨1112697516194103673834301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 741798344129402449222867 1112697516194103673834301)
                    ·
                      refine ⟨417261568572788877687863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1112697516194103673834301 417261568572788877687863)
                      ·
                        rfl

theorem cell23_812614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_812614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812614 prefixEnd_812614 := by exact prefixLift 812614
  have htrace : WordTrace (prefixWord ++ tailWord_812614) baseStart_812614 baseEnd_812614 := by
    simpa [prefixWord, tailWord_812614, baseEnd_812614] using wordTrace_append hprefix tailTrace_812614
  have hstable : (prefixWord ++ tailWord_812614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812614).length < 2 ^ (prefixWord ++ tailWord_812614).sum := by decide
  have hdescent : baseEnd_812614 < baseStart_812614 := by decide
  rcases family_descends (prefixWord ++ tailWord_812614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812620 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 2, 2, 2]
def baseStart_812620 : Nat := 118140960795 + 812620 * 2 ^ 59
def prefixEnd_812620 : Nat := 4983230072969 + 3 ^ 40 * 812620 * 2
def baseEnd_812620 : Nat := 417264649456715854212835

theorem tailTrace_812620 : CollatzResearch.WordTrace tailWord_812620 prefixEnd_812620 417264649456715854212835 := by
  unfold tailWord_812620
  simp only [CollatzResearch.WordTrace]
  refine ⟨14819343158011999645957657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19759124210682666194610209 14819343158011999645957657)
  ·
    refine ⟨11114507368508999734468243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14819343158011999645957657 11114507368508999734468243)
    ·
      refine ⟨16671761052763499601702365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11114507368508999734468243 16671761052763499601702365)
      ·
        refine ⟨6251910394786312350638387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16671761052763499601702365 6251910394786312350638387)
        ·
          refine ⟨9377865592179468525957581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6251910394786312350638387 9377865592179468525957581)
          ·
            refine ⟨3516699597067300697234093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9377865592179468525957581 3516699597067300697234093)
            ·
              refine ⟨1318762348900237761462785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3516699597067300697234093 1318762348900237761462785)
              ·
                refine ⟨989071761675178321097089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318762348900237761462785 989071761675178321097089)
                ·
                  refine ⟨741803821256383740822817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989071761675178321097089 741803821256383740822817)
                  ·
                    refine ⟨556352865942287805617113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 741803821256383740822817 556352865942287805617113)
                    ·
                      refine ⟨417264649456715854212835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556352865942287805617113 417264649456715854212835)
                      ·
                        rfl

theorem cell23_812620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_812620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812620 prefixEnd_812620 := by exact prefixLift 812620
  have htrace : WordTrace (prefixWord ++ tailWord_812620) baseStart_812620 baseEnd_812620 := by
    simpa [prefixWord, tailWord_812620, baseEnd_812620] using wordTrace_append hprefix tailTrace_812620
  have hstable : (prefixWord ++ tailWord_812620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812620).length < 2 ^ (prefixWord ++ tailWord_812620).sum := by decide
  have hdescent : baseEnd_812620 < baseStart_812620 := by decide
  rcases family_descends (prefixWord ++ tailWord_812620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812626 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 7]
def baseStart_812626 : Nat := 118140960795 + 812626 * 2 ^ 59
def prefixEnd_812626 : Nat := 4983230072969 + 3 ^ 40 * 812626 * 2
def baseEnd_812626 : Nat := 46363081148960314526423

theorem tailTrace_812626 : CollatzResearch.WordTrace tailWord_812626 prefixEnd_812626 46363081148960314526423 := by
  unfold tailWord_812626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7409726288500565579158433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19759270102668174877755821 7409726288500565579158433)
  ·
    refine ⟨5557294716375424184368825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7409726288500565579158433 5557294716375424184368825)
    ·
      refine ⟨4167971037281568138276619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5557294716375424184368825 4167971037281568138276619)
      ·
        refine ⟨6251956555922352207414929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4167971037281568138276619 6251956555922352207414929)
        ·
          refine ⟨4688967416941764155561197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6251956555922352207414929 4688967416941764155561197)
          ·
            refine ⟨1758362781353161558335449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4688967416941764155561197 1758362781353161558335449)
            ·
              refine ⟨1318772086014871168751587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758362781353161558335449 1318772086014871168751587)
              ·
                refine ⟨1978158129022306753127381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318772086014871168751587 1978158129022306753127381)
                ·
                  refine ⟨46363081148960314526423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1978158129022306753127381 46363081148960314526423)
                  ·
                    rfl

theorem cell23_812626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_812626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812626 prefixEnd_812626 := by exact prefixLift 812626
  have htrace : WordTrace (prefixWord ++ tailWord_812626) baseStart_812626 baseEnd_812626 := by
    simpa [prefixWord, tailWord_812626, baseEnd_812626] using wordTrace_append hprefix tailTrace_812626
  have hstable : (prefixWord ++ tailWord_812626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812626).length < 2 ^ (prefixWord ++ tailWord_812626).sum := by decide
  have hdescent : baseEnd_812626 < baseStart_812626 := by decide
  rcases family_descends (prefixWord ++ tailWord_812626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812689 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_812689 : Nat := 118140960795 + 812689 * 2 ^ 59
def prefixEnd_812689 : Nat := 4983230072969 + 3 ^ 40 * 812689 * 2
def baseEnd_812689 : Nat := 417300079621876084250017

theorem tailTrace_812689 : CollatzResearch.WordTrace tailWord_812689 prefixEnd_812689 417300079621876084250017 := by
  unfold tailWord_812689
  simp only [CollatzResearch.WordTrace]
  refine ⟨29641202952774024076177121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19760801968516016050784747 29641202952774024076177121)
  ·
    refine ⟨22230902214580518057132841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29641202952774024076177121 22230902214580518057132841)
    ·
      refine ⟨16673176660935388542849631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22230902214580518057132841 16673176660935388542849631)
      ·
        refine ⟨25009764991403082814274447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16673176660935388542849631 25009764991403082814274447)
        ·
          refine ⟨37514647487104624221411671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25009764991403082814274447 37514647487104624221411671)
          ·
            refine ⟨56271971230656936332117507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37514647487104624221411671 56271971230656936332117507)
            ·
              refine ⟨84407956845985404498176261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56271971230656936332117507 84407956845985404498176261)
              ·
                refine ⟨15826491908622263343408049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84407956845985404498176261 15826491908622263343408049)
                ·
                  refine ⟨11869868931466697507556037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15826491908622263343408049 11869868931466697507556037)
                  ·
                    refine ⟨2225600424650005782666757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11869868931466697507556037 2225600424650005782666757)
                    ·
                      refine ⟨417300079621876084250017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2225600424650005782666757 417300079621876084250017)
                      ·
                        rfl

theorem cell23_812689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_812689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812689 prefixEnd_812689 := by exact prefixLift 812689
  have htrace : WordTrace (prefixWord ++ tailWord_812689) baseStart_812689 baseEnd_812689 := by
    simpa [prefixWord, tailWord_812689, baseEnd_812689] using wordTrace_append hprefix tailTrace_812689
  have hstable : (prefixWord ++ tailWord_812689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812689).length < 2 ^ (prefixWord ++ tailWord_812689).sum := by decide
  have hdescent : baseEnd_812689 < baseStart_812689 := by decide
  rcases family_descends (prefixWord ++ tailWord_812689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812739 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 5]
def baseStart_812739 : Nat := 118140960795 + 812739 * 2 ^ 59
def prefixEnd_812739 : Nat := 4983230072969 + 3 ^ 40 * 812739 * 2
def baseEnd_812739 : Nat := 417325753654600888624787

theorem tailTrace_812739 : CollatzResearch.WordTrace tailWord_812739 prefixEnd_812739 417325753654600888624787 := by
  unfold tailWord_812739
  simp only [CollatzResearch.WordTrace]
  refine ⟨29643026602592882615497271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19762017735061921743664847 29643026602592882615497271)
  ·
    refine ⟨44464539903889323923245907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29643026602592882615497271 44464539903889323923245907)
    ·
      refine ⟨66696809855833985884868861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44464539903889323923245907 66696809855833985884868861)
      ·
        refine ⟨25011303695937744706825823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66696809855833985884868861 25011303695937744706825823)
        ·
          refine ⟨37516955543906617060238735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25011303695937744706825823 37516955543906617060238735)
          ·
            refine ⟨56275433315859925590358103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37516955543906617060238735 56275433315859925590358103)
            ·
              refine ⟨84413149973789888385537155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56275433315859925590358103 84413149973789888385537155)
              ·
                refine ⟨126619724960684832578305733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84413149973789888385537155 126619724960684832578305733)
                ·
                  refine ⟨23741198430128406108432325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126619724960684832578305733 23741198430128406108432325)
                  ·
                    refine ⟨4451474705649076145331061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23741198430128406108432325 4451474705649076145331061)
                    ·
                      refine ⟨417325753654600888624787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4451474705649076145331061 417325753654600888624787)
                      ·
                        rfl

theorem cell23_812739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_812739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812739 prefixEnd_812739 := by exact prefixLift 812739
  have htrace : WordTrace (prefixWord ++ tailWord_812739) baseStart_812739 baseEnd_812739 := by
    simpa [prefixWord, tailWord_812739, baseEnd_812739] using wordTrace_append hprefix tailTrace_812739
  have hstable : (prefixWord ++ tailWord_812739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812739).length < 2 ^ (prefixWord ++ tailWord_812739).sum := by decide
  have hdescent : baseEnd_812739 < baseStart_812739 := by decide
  rcases family_descends (prefixWord ++ tailWord_812739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812743 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_812743 : Nat := 118140960795 + 812743 * 2 ^ 59
def prefixEnd_812743 : Nat := 4983230072969 + 3 ^ 40 * 812743 * 2
def baseEnd_812743 : Nat := 417327807577218872974769

theorem tailTrace_812743 : CollatzResearch.WordTrace tailWord_812743 prefixEnd_812743 417327807577218872974769 := by
  unfold tailWord_812743
  simp only [CollatzResearch.WordTrace]
  refine ⟨29643172494578391298642883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19762114996385594199095255 29643172494578391298642883)
  ·
    refine ⟨44464758741867586947964325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29643172494578391298642883 44464758741867586947964325)
    ·
      refine ⟨8337142264100172552743311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44464758741867586947964325 8337142264100172552743311)
      ·
        refine ⟨12505713396150258829114967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8337142264100172552743311 12505713396150258829114967)
        ·
          refine ⟨18758570094225388243672451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12505713396150258829114967 18758570094225388243672451)
          ·
            refine ⟨28137855141338082365508677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18758570094225388243672451 28137855141338082365508677)
            ·
              refine ⟨5275847839000890443532877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28137855141338082365508677 5275847839000890443532877)
              ·
                refine ⟨1978442939625333916324829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5275847839000890443532877 1978442939625333916324829)
                ·
                  refine ⟨741916102359500218621811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1978442939625333916324829 741916102359500218621811)
                  ·
                    refine ⟨1112874153539250327932717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 741916102359500218621811 1112874153539250327932717)
                    ·
                      refine ⟨417327807577218872974769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1112874153539250327932717 417327807577218872974769)
                      ·
                        rfl

theorem cell23_812743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_812743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812743 prefixEnd_812743 := by exact prefixLift 812743
  have htrace : WordTrace (prefixWord ++ tailWord_812743) baseStart_812743 baseEnd_812743 := by
    simpa [prefixWord, tailWord_812743, baseEnd_812743] using wordTrace_append hprefix tailTrace_812743
  have hstable : (prefixWord ++ tailWord_812743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812743).length < 2 ^ (prefixWord ++ tailWord_812743).sum := by decide
  have hdescent : baseEnd_812743 < baseStart_812743 := by decide
  rcases family_descends (prefixWord ++ tailWord_812743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812764 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_812764 : Nat := 118140960795 + 812764 * 2 ^ 59
def prefixEnd_812764 : Nat := 4983230072969 + 3 ^ 40 * 812764 * 2
def baseEnd_812764 : Nat := 417338590670963290812173

theorem tailTrace_812764 : CollatzResearch.WordTrace tailWord_812764 prefixEnd_812764 417338590670963290812173 := by
  unfold tailWord_812764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14821969213751155942578673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19762625618334874590104897 14821969213751155942578673)
  ·
    refine ⟨11116476910313366956934005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14821969213751155942578673 11116476910313366956934005)
    ·
      refine ⟨1042169710341878152212563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11116476910313366956934005 1042169710341878152212563)
      ·
        refine ⟨1563254565512817228318845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042169710341878152212563 1563254565512817228318845)
        ·
          refine ⟨586220462067306460619567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1563254565512817228318845 586220462067306460619567)
          ·
            refine ⟨879330693100959690929351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586220462067306460619567 879330693100959690929351)
            ·
              refine ⟨1318996039651439536394027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879330693100959690929351 1318996039651439536394027)
              ·
                refine ⟨1978494059477159304591041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318996039651439536394027 1978494059477159304591041)
                ·
                  refine ⟨1483870544607869478443281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1978494059477159304591041 1483870544607869478443281)
                  ·
                    refine ⟨1112902908455902108832461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1483870544607869478443281 1112902908455902108832461)
                    ·
                      refine ⟨417338590670963290812173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1112902908455902108832461 417338590670963290812173)
                      ·
                        rfl

theorem cell23_812764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_812764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812764 prefixEnd_812764 := by exact prefixLift 812764
  have htrace : WordTrace (prefixWord ++ tailWord_812764) baseStart_812764 baseEnd_812764 := by
    simpa [prefixWord, tailWord_812764, baseEnd_812764] using wordTrace_append hprefix tailTrace_812764
  have hstable : (prefixWord ++ tailWord_812764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812764).length < 2 ^ (prefixWord ++ tailWord_812764).sum := by decide
  have hdescent : baseEnd_812764 < baseStart_812764 := by decide
  rcases family_descends (prefixWord ++ tailWord_812764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812783 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 4]
def baseStart_812783 : Nat := 118140960795 + 812783 * 2 ^ 59
def prefixEnd_812783 : Nat := 4983230072969 + 3 ^ 40 * 812783 * 2
def baseEnd_812783 : Nat := 417348346803398716474585

theorem tailTrace_812783 : CollatzResearch.WordTrace tailWord_812783 prefixEnd_812783 417348346803398716474585 := by
  unfold tailWord_812783
  simp only [CollatzResearch.WordTrace]
  refine ⟨29644631414433478130099003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19763087609622318753399335 29644631414433478130099003)
  ·
    refine ⟨44466947121650217195148505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29644631414433478130099003 44466947121650217195148505)
    ·
      refine ⟨33350210341237662896361379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44466947121650217195148505 33350210341237662896361379)
      ·
        refine ⟨50025315511856494344542069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33350210341237662896361379 50025315511856494344542069)
        ·
          refine ⟨4689873329236546344800819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50025315511856494344542069 4689873329236546344800819)
          ·
            refine ⟨7034809993854819517201229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689873329236546344800819 7034809993854819517201229)
            ·
              refine ⟨2638053747695557318950461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7034809993854819517201229 2638053747695557318950461)
              ·
                refine ⟨989270155385833994606423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2638053747695557318950461 989270155385833994606423)
                ·
                  refine ⟨1483905233078750991909635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989270155385833994606423 1483905233078750991909635)
                  ·
                    refine ⟨2225857849618126487864453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1483905233078750991909635 2225857849618126487864453)
                    ·
                      refine ⟨417348346803398716474585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2225857849618126487864453 417348346803398716474585)
                      ·
                        rfl

theorem cell23_812783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 4].length) (baseStart_812783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812783 prefixEnd_812783 := by exact prefixLift 812783
  have htrace : WordTrace (prefixWord ++ tailWord_812783) baseStart_812783 baseEnd_812783 := by
    simpa [prefixWord, tailWord_812783, baseEnd_812783] using wordTrace_append hprefix tailTrace_812783
  have hstable : (prefixWord ++ tailWord_812783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812783).length < 2 ^ (prefixWord ++ tailWord_812783).sum := by decide
  have hdescent : baseEnd_812783 < baseStart_812783 := by decide
  rcases family_descends (prefixWord ++ tailWord_812783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812796 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_812796 : Nat := 118140960795 + 812796 * 2 ^ 59
def prefixEnd_812796 : Nat := 4983230072969 + 3 ^ 40 * 812796 * 2
def baseEnd_812796 : Nat := 417355022051907165612025

theorem tailTrace_812796 : CollatzResearch.WordTrace tailWord_812796 prefixEnd_812796 417355022051907165612025 := by
  unfold tailWord_812796
  simp only [CollatzResearch.WordTrace]
  refine ⟨14822552781693190675161121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19763403708924254233548161 14822552781693190675161121)
  ·
    refine ⟨11116914586269893006370841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14822552781693190675161121 11116914586269893006370841)
    ·
      refine ⟨8337685939702419754778131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11116914586269893006370841 8337685939702419754778131)
      ·
        refine ⟨12506528909553629632167197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8337685939702419754778131 12506528909553629632167197)
        ·
          refine ⟨4689948341082611112062699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12506528909553629632167197 4689948341082611112062699)
          ·
            refine ⟨7034922511623916668094049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689948341082611112062699 7034922511623916668094049)
            ·
              refine ⟨5276191883717937501070537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7034922511623916668094049 5276191883717937501070537)
              ·
                refine ⟨3957143912788453125802903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5276191883717937501070537 3957143912788453125802903)
                ·
                  refine ⟨5935715869182679688704355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3957143912788453125802903 5935715869182679688704355)
                  ·
                    refine ⟨8903573803774019533056533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5935715869182679688704355 8903573803774019533056533)
                    ·
                      refine ⟨417355022051907165612025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8903573803774019533056533 417355022051907165612025)
                      ·
                        rfl

theorem cell23_812796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_812796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812796 prefixEnd_812796 := by exact prefixLift 812796
  have htrace : WordTrace (prefixWord ++ tailWord_812796) baseStart_812796 baseEnd_812796 := by
    simpa [prefixWord, tailWord_812796, baseEnd_812796] using wordTrace_append hprefix tailTrace_812796
  have hstable : (prefixWord ++ tailWord_812796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812796).length < 2 ^ (prefixWord ++ tailWord_812796).sum := by decide
  have hdescent : baseEnd_812796 < baseStart_812796 := by decide
  rcases family_descends (prefixWord ++ tailWord_812796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812823 : List Nat := [1, 1, 3, 4, 2, 1, 4, 7]
def baseStart_812823 : Nat := 118140960795 + 812823 * 2 ^ 59
def prefixEnd_812823 : Nat := 4983230072969 + 3 ^ 40 * 812823 * 2
def baseEnd_812823 : Nat := 15458106889984391110163

theorem tailTrace_812823 : CollatzResearch.WordTrace tailWord_812823 prefixEnd_812823 15458106889984391110163 := by
  unfold tailWord_812823
  simp only [CollatzResearch.WordTrace]
  refine ⟨29646090334288564961555123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19764060222859043307703415 29646090334288564961555123)
  ·
    refine ⟨44469135501432847442332685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29646090334288564961555123 44469135501432847442332685)
    ·
      refine ⟨16675925813037317790874757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44469135501432847442332685 16675925813037317790874757)
      ·
        refine ⟨3126736089944497085789017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16675925813037317790874757 3126736089944497085789017)
        ·
          refine ⟨2345052067458372814341763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3126736089944497085789017 2345052067458372814341763)
          ·
            refine ⟨3517578101187559221512645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345052067458372814341763 3517578101187559221512645)
            ·
              refine ⟨659545893972667354033621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3517578101187559221512645 659545893972667354033621)
              ·
                refine ⟨15458106889984391110163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 659545893972667354033621 15458106889984391110163)
                ·
                  rfl

theorem cell23_812823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 7].length) (baseStart_812823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812823 prefixEnd_812823 := by exact prefixLift 812823
  have htrace : WordTrace (prefixWord ++ tailWord_812823) baseStart_812823 baseEnd_812823 := by
    simpa [prefixWord, tailWord_812823, baseEnd_812823] using wordTrace_append hprefix tailTrace_812823
  have hstable : (prefixWord ++ tailWord_812823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812823).length < 2 ^ (prefixWord ++ tailWord_812823).sum := by decide
  have hdescent : baseEnd_812823 < baseStart_812823 := by decide
  rcases family_descends (prefixWord ++ tailWord_812823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812850 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_812850 : Nat := 118140960795 + 812850 * 2 ^ 59
def prefixEnd_812850 : Nat := 4983230072969 + 3 ^ 40 * 812850 * 2
def baseEnd_812850 : Nat := 417382750007249954336777

theorem tailTrace_812850 : CollatzResearch.WordTrace tailWord_812850 prefixEnd_812850 417382750007249954336777 := by
  unfold tailWord_812850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7411768776297687143197001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19764716736793832381858669 7411768776297687143197001)
  ·
    refine ⟨5558826582223265357397751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7411768776297687143197001 5558826582223265357397751)
    ·
      refine ⟨8338239873334898036096627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5558826582223265357397751 8338239873334898036096627)
      ·
        refine ⟨12507359810002347054144941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8338239873334898036096627 12507359810002347054144941)
        ·
          refine ⟨4690259928750880145304353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12507359810002347054144941 4690259928750880145304353)
          ·
            refine ⟨3517694946563160108978265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4690259928750880145304353 3517694946563160108978265)
            ·
              refine ⟨2638271209922370081733699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517694946563160108978265 2638271209922370081733699)
              ·
                refine ⟨3957406814883555122600549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638271209922370081733699 3957406814883555122600549)
                ·
                  refine ⟨742013777790666585487603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3957406814883555122600549 742013777790666585487603)
                  ·
                    refine ⟨1113020666685999878231405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 742013777790666585487603 1113020666685999878231405)
                    ·
                      refine ⟨417382750007249954336777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1113020666685999878231405 417382750007249954336777)
                      ·
                        rfl

theorem cell23_812850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_812850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812850 prefixEnd_812850 := by exact prefixLift 812850
  have htrace : WordTrace (prefixWord ++ tailWord_812850) baseStart_812850 baseEnd_812850 := by
    simpa [prefixWord, tailWord_812850, baseEnd_812850] using wordTrace_append hprefix tailTrace_812850
  have hstable : (prefixWord ++ tailWord_812850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812850).length < 2 ^ (prefixWord ++ tailWord_812850).sum := by decide
  have hdescent : baseEnd_812850 < baseStart_812850 := by decide
  rcases family_descends (prefixWord ++ tailWord_812850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812851 : List Nat := [1, 1, 1, 2, 7, 1, 3, 2, 1, 2, 2]
def baseStart_812851 : Nat := 118140960795 + 812851 * 2 ^ 59
def prefixEnd_812851 : Nat := 4983230072969 + 3 ^ 40 * 812851 * 2
def baseEnd_812851 : Nat := 417383263487904450424273

theorem tailTrace_812851 : CollatzResearch.WordTrace tailWord_812851 prefixEnd_812851 417383263487904450424273 := by
  unfold tailWord_812851
  simp only [CollatzResearch.WordTrace]
  refine ⟨29647111578187125743574407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19764741052124750495716271 29647111578187125743574407)
  ·
    refine ⟨44470667367280688615361611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29647111578187125743574407 44470667367280688615361611)
    ·
      refine ⟨66706001050921032923042417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44470667367280688615361611 66706001050921032923042417)
      ·
        refine ⟨50029500788190774692281813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66706001050921032923042417 50029500788190774692281813)
        ·
          refine ⟨1172566424723221281850355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50029500788190774692281813 1172566424723221281850355)
          ·
            refine ⟨1758849637084831922775533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172566424723221281850355 1758849637084831922775533)
            ·
              refine ⟨659568613906811971040825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1758849637084831922775533 659568613906811971040825)
              ·
                refine ⟨494676460430108978280619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659568613906811971040825 494676460430108978280619)
                ·
                  refine ⟨742014690645163467420929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494676460430108978280619 742014690645163467420929)
                  ·
                    refine ⟨556511017983872600565697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 742014690645163467420929 556511017983872600565697)
                    ·
                      refine ⟨417383263487904450424273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556511017983872600565697 417383263487904450424273)
                      ·
                        rfl

theorem cell23_812851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 1, 2, 2].length) (baseStart_812851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812851 prefixEnd_812851 := by exact prefixLift 812851
  have htrace : WordTrace (prefixWord ++ tailWord_812851) baseStart_812851 baseEnd_812851 := by
    simpa [prefixWord, tailWord_812851, baseEnd_812851] using wordTrace_append hprefix tailTrace_812851
  have hstable : (prefixWord ++ tailWord_812851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812851).length < 2 ^ (prefixWord ++ tailWord_812851).sum := by decide
  have hdescent : baseEnd_812851 < baseStart_812851 := by decide
  rcases family_descends (prefixWord ++ tailWord_812851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812867 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 2, 1, 3]
def baseStart_812867 : Nat := 118140960795 + 812867 * 2 ^ 59
def prefixEnd_812867 : Nat := 4983230072969 + 3 ^ 40 * 812867 * 2
def baseEnd_812867 : Nat := 417391479178376387824199

theorem tailTrace_812867 : CollatzResearch.WordTrace tailWord_812867 prefixEnd_812867 417391479178376387824199 := by
  unfold tailWord_812867
  simp only [CollatzResearch.WordTrace]
  refine ⟨29647695146129160476156855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19765130097419440317437903 29647695146129160476156855)
  ·
    refine ⟨44471542719193740714235283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29647695146129160476156855 44471542719193740714235283)
    ·
      refine ⟨66707314078790611071352925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44471542719193740714235283 66707314078790611071352925)
      ·
        refine ⟨25015242779546479151757347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66707314078790611071352925 25015242779546479151757347)
        ·
          refine ⟨37522864169319718727636021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25015242779546479151757347 37522864169319718727636021)
          ·
            refine ⟨3517768515873723630715877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37522864169319718727636021 3517768515873723630715877)
            ·
              refine ⟨659581596726323180759227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3517768515873723630715877 659581596726323180759227)
              ·
                refine ⟨989372395089484771138841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659581596726323180759227 989372395089484771138841)
                ·
                  refine ⟨742029296317113578354131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989372395089484771138841 742029296317113578354131)
                  ·
                    refine ⟨1113043944475670367531197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 742029296317113578354131 1113043944475670367531197)
                    ·
                      refine ⟨417391479178376387824199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1113043944475670367531197 417391479178376387824199)
                      ·
                        rfl

theorem cell23_812867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_812867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812867 prefixEnd_812867 := by exact prefixLift 812867
  have htrace : WordTrace (prefixWord ++ tailWord_812867) baseStart_812867 baseEnd_812867 := by
    simpa [prefixWord, tailWord_812867, baseEnd_812867] using wordTrace_append hprefix tailTrace_812867
  have hstable : (prefixWord ++ tailWord_812867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812867).length < 2 ^ (prefixWord ++ tailWord_812867).sum := by decide
  have hdescent : baseEnd_812867 < baseStart_812867 := by decide
  rcases family_descends (prefixWord ++ tailWord_812867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812890 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2]
def baseStart_812890 : Nat := 118140960795 + 812890 * 2 ^ 59
def prefixEnd_812890 : Nat := 4983230072969 + 3 ^ 40 * 812890 * 2
def baseEnd_812890 : Nat := 417403289233429797836593

theorem tailTrace_812890 : CollatzResearch.WordTrace tailWord_812890 prefixEnd_812890 417403289233429797836593 := by
  unfold tailWord_812890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412133506261458851061031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19765689350030556936162749 7412133506261458851061031)
  ·
    refine ⟨11118200259392188276591547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7412133506261458851061031 11118200259392188276591547)
    ·
      refine ⟨16677300389088282414887321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11118200259392188276591547 16677300389088282414887321)
      ·
        refine ⟨12507975291816211811165491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16677300389088282414887321 12507975291816211811165491)
        ·
          refine ⟨18761962937724317716748237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12507975291816211811165491 18761962937724317716748237)
          ·
            refine ⟨7035736101646619143780589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18761962937724317716748237 7035736101646619143780589)
            ·
              refine ⟨2638401038117482178917721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7035736101646619143780589 2638401038117482178917721)
              ·
                refine ⟨1978800778588111634188291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638401038117482178917721 1978800778588111634188291)
                ·
                  refine ⟨2968201167882167451282437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978800778588111634188291 2968201167882167451282437)
                  ·
                    refine ⟨556537718977906397115457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968201167882167451282437 556537718977906397115457)
                    ·
                      refine ⟨417403289233429797836593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556537718977906397115457 417403289233429797836593)
                      ·
                        rfl

theorem cell23_812890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_812890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812890 prefixEnd_812890 := by exact prefixLift 812890
  have htrace : WordTrace (prefixWord ++ tailWord_812890) baseStart_812890 baseEnd_812890 := by
    simpa [prefixWord, tailWord_812890, baseEnd_812890] using wordTrace_append hprefix tailTrace_812890
  have hstable : (prefixWord ++ tailWord_812890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812890).length < 2 ^ (prefixWord ++ tailWord_812890).sum := by decide
  have hdescent : baseEnd_812890 < baseStart_812890 := by decide
  rcases family_descends (prefixWord ++ tailWord_812890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812903 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_812903 : Nat := 118140960795 + 812903 * 2 ^ 59
def prefixEnd_812903 : Nat := 4983230072969 + 3 ^ 40 * 812903 * 2
def baseEnd_812903 : Nat := 417409964481938246974033

theorem tailTrace_812903 : CollatzResearch.WordTrace tailWord_812903 prefixEnd_812903 417409964481938246974033 := by
  unfold tailWord_812903
  simp only [CollatzResearch.WordTrace]
  refine ⟨29649008173998738624467363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19766005449332492416311575 29649008173998738624467363)
  ·
    refine ⟨44473512260998107936701045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29649008173998738624467363 44473512260998107936701045)
    ·
      refine ⟨4169391774468572619065723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44473512260998107936701045 4169391774468572619065723)
      ·
        refine ⟨6254087661702858928598585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4169391774468572619065723 6254087661702858928598585)
        ·
          refine ⟨4690565746277144196448939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6254087661702858928598585 4690565746277144196448939)
          ·
            refine ⟨7035848619415716294673409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690565746277144196448939 7035848619415716294673409)
            ·
              refine ⟨5276886464561787221005057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7035848619415716294673409 5276886464561787221005057)
              ·
                refine ⟨3957664848421340415753793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5276886464561787221005057 3957664848421340415753793)
                ·
                  refine ⟨2968248636316005311815345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3957664848421340415753793 2968248636316005311815345)
                  ·
                    refine ⟨2226186477237003983861509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2968248636316005311815345 2226186477237003983861509)
                    ·
                      refine ⟨417409964481938246974033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2226186477237003983861509 417409964481938246974033)
                      ·
                        rfl

theorem cell23_812903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_812903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812903 prefixEnd_812903 := by exact prefixLift 812903
  have htrace : WordTrace (prefixWord ++ tailWord_812903) baseStart_812903 baseEnd_812903 := by
    simpa [prefixWord, tailWord_812903, baseEnd_812903] using wordTrace_append hprefix tailTrace_812903
  have hstable : (prefixWord ++ tailWord_812903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812903).length < 2 ^ (prefixWord ++ tailWord_812903).sum := by decide
  have hdescent : baseEnd_812903 < baseStart_812903 := by decide
  rcases family_descends (prefixWord ++ tailWord_812903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812910 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_812910 : Nat := 118140960795 + 812910 * 2 ^ 59
def prefixEnd_812910 : Nat := 4983230072969 + 3 ^ 40 * 812910 * 2
def baseEnd_812910 : Nat := 417413558846519719586501

theorem tailTrace_812910 : CollatzResearch.WordTrace tailWord_812910 prefixEnd_812910 417413558846519719586501 := by
  unfold tailWord_812910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3706157935621672352496523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19766175656648919213314789 3706157935621672352496523)
  ·
    refine ⟨5559236903432508528744785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3706157935621672352496523 5559236903432508528744785)
    ·
      refine ⟨4169427677574381396558589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5559236903432508528744785 4169427677574381396558589)
      ·
        refine ⟨1563535379090393023709471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4169427677574381396558589 1563535379090393023709471)
        ·
          refine ⟨2345303068635589535564207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1563535379090393023709471 2345303068635589535564207)
          ·
            refine ⟨3517954602953384303346311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345303068635589535564207 3517954602953384303346311)
            ·
              refine ⟨5276931904430076455019467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517954602953384303346311 5276931904430076455019467)
              ·
                refine ⟨7915397856645114682529201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276931904430076455019467 7915397856645114682529201)
                ·
                  refine ⟨5936548392483836011896901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7915397856645114682529201 5936548392483836011896901)
                  ·
                    refine ⟨1113102823590719252230669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5936548392483836011896901 1113102823590719252230669)
                    ·
                      refine ⟨417413558846519719586501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1113102823590719252230669 417413558846519719586501)
                      ·
                        rfl

theorem cell23_812910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_812910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812910 prefixEnd_812910 := by exact prefixLift 812910
  have htrace : WordTrace (prefixWord ++ tailWord_812910) baseStart_812910 baseEnd_812910 := by
    simpa [prefixWord, tailWord_812910, baseEnd_812910] using wordTrace_append hprefix tailTrace_812910
  have hstable : (prefixWord ++ tailWord_812910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812910).length < 2 ^ (prefixWord ++ tailWord_812910).sum := by decide
  have hdescent : baseEnd_812910 < baseStart_812910 := by decide
  rcases family_descends (prefixWord ++ tailWord_812910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812963 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 4]
def baseStart_812963 : Nat := 118140960795 + 812963 * 2 ^ 59
def prefixEnd_812963 : Nat := 4983230072969 + 3 ^ 40 * 812963 * 2
def baseEnd_812963 : Nat := 417440773321208012223757

theorem tailTrace_812963 : CollatzResearch.WordTrace tailWord_812963 prefixEnd_812963 417440773321208012223757 := by
  unfold tailWord_812963
  simp only [CollatzResearch.WordTrace]
  refine ⟨29651196553781368871651543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19767464369187579247767695 29651196553781368871651543)
  ·
    refine ⟨44476794830672053307477315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29651196553781368871651543 44476794830672053307477315)
    ·
      refine ⟨66715192246008079961215973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44476794830672053307477315 66715192246008079961215973)
      ·
        refine ⟨12509098546126514992727995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66715192246008079961215973 12509098546126514992727995)
        ·
          refine ⟨18763647819189772489091993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12509098546126514992727995 18763647819189772489091993)
          ·
            refine ⟨14072735864392329366818995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18763647819189772489091993 14072735864392329366818995)
            ·
              refine ⟨21109103796588494050228493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14072735864392329366818995 21109103796588494050228493)
              ·
                refine ⟨7915913923720685268835685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21109103796588494050228493 7915913923720685268835685)
                ·
                  refine ⟨1484233860697628487906691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7915913923720685268835685 1484233860697628487906691)
                  ·
                    refine ⟨2226350791046442731860037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1484233860697628487906691 2226350791046442731860037)
                    ·
                      refine ⟨417440773321208012223757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2226350791046442731860037 417440773321208012223757)
                      ·
                        rfl

theorem cell23_812963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_812963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_812963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_812963 prefixEnd_812963 := by exact prefixLift 812963
  have htrace : WordTrace (prefixWord ++ tailWord_812963) baseStart_812963 baseEnd_812963 := by
    simpa [prefixWord, tailWord_812963, baseEnd_812963] using wordTrace_append hprefix tailTrace_812963
  have hstable : (prefixWord ++ tailWord_812963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812963).length < 2 ^ (prefixWord ++ tailWord_812963).sum := by decide
  have hdescent : baseEnd_812963 < baseStart_812963 := by decide
  rcases family_descends (prefixWord ++ tailWord_812963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813000 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_813000 : Nat := 118140960795 + 813000 * 2 ^ 59
def prefixEnd_813000 : Nat := 4983230072969 + 3 ^ 40 * 813000 * 2
def baseEnd_813000 : Nat := 417459772105424367461087

theorem tailTrace_813000 : CollatzResearch.WordTrace tailWord_813000 prefixEnd_813000 417459772105424367461087 := by
  unfold tailWord_813000
  simp only [CollatzResearch.WordTrace]
  refine ⟨14826273027323662095374227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19768364036431549460498969 14826273027323662095374227)
  ·
    refine ⟨22239409540985493143061341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14826273027323662095374227 22239409540985493143061341)
    ·
      refine ⟨8339778577869559928648003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22239409540985493143061341 8339778577869559928648003)
      ·
        refine ⟨12509667866804339892972005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8339778577869559928648003 12509667866804339892972005)
        ·
          refine ⟨2345562725025813729932251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12509667866804339892972005 2345562725025813729932251)
          ·
            refine ⟨3518344087538720594898377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345562725025813729932251 3518344087538720594898377)
            ·
              refine ⟨2638758065654040446173783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3518344087538720594898377 2638758065654040446173783)
              ·
                refine ⟨3958137098481060669260675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638758065654040446173783 3958137098481060669260675)
                ·
                  refine ⟨5937205647721591003891013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958137098481060669260675 5937205647721591003891013)
                  ·
                    refine ⟨1113226058947798313229565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5937205647721591003891013 1113226058947798313229565)
                    ·
                      refine ⟨417459772105424367461087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1113226058947798313229565 417459772105424367461087)
                      ·
                        rfl

theorem cell23_813000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_813000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813000 prefixEnd_813000 := by exact prefixLift 813000
  have htrace : WordTrace (prefixWord ++ tailWord_813000) baseStart_813000 baseEnd_813000 := by
    simpa [prefixWord, tailWord_813000, baseEnd_813000] using wordTrace_append hprefix tailTrace_813000
  have hstable : (prefixWord ++ tailWord_813000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813000).length < 2 ^ (prefixWord ++ tailWord_813000).sum := by decide
  have hdescent : baseEnd_813000 < baseStart_813000 := by decide
  rcases family_descends (prefixWord ++ tailWord_813000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813014 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_813014 : Nat := 118140960795 + 813014 * 2 ^ 59
def prefixEnd_813014 : Nat := 4983230072969 + 3 ^ 40 * 813014 * 2
def baseEnd_813014 : Nat := 417466960834587312686023

theorem tailTrace_813014 : CollatzResearch.WordTrace tailWord_813014 prefixEnd_813014 417466960834587312686023 := by
  unfold tailWord_813014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853316042287287786359881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19768704451064403054505397 1853316042287287786359881)
  ·
    refine ⟨1389987031715465839769911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1853316042287287786359881 1389987031715465839769911)
    ·
      refine ⟨2084980547573198759654867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1389987031715465839769911 2084980547573198759654867)
      ·
        refine ⟨3127470821359798139482301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084980547573198759654867 3127470821359798139482301)
        ·
          refine ⟨1172801558009924302305863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3127470821359798139482301 1172801558009924302305863)
          ·
            refine ⟨1759202337014886453458795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172801558009924302305863 1759202337014886453458795)
            ·
              refine ⟨2638803505522329680188193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759202337014886453458795 2638803505522329680188193)
              ·
                refine ⟨1979102629141747260141145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638803505522329680188193 1979102629141747260141145)
                ·
                  refine ⟨1484326971856310445105859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1979102629141747260141145 1484326971856310445105859)
                  ·
                    refine ⟨2226490457784465667658789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1484326971856310445105859 2226490457784465667658789)
                    ·
                      refine ⟨417466960834587312686023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2226490457784465667658789 417466960834587312686023)
                      ·
                        rfl

theorem cell23_813014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_813014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813014 prefixEnd_813014 := by exact prefixLift 813014
  have htrace : WordTrace (prefixWord ++ tailWord_813014) baseStart_813014 baseEnd_813014 := by
    simpa [prefixWord, tailWord_813014, baseEnd_813014] using wordTrace_append hprefix tailTrace_813014
  have hstable : (prefixWord ++ tailWord_813014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813014).length < 2 ^ (prefixWord ++ tailWord_813014).sum := by decide
  have hdescent : baseEnd_813014 < baseStart_813014 := by decide
  rcases family_descends (prefixWord ++ tailWord_813014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813017 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 2, 2, 3]
def baseStart_813017 : Nat := 118140960795 + 813017 * 2 ^ 59
def prefixEnd_813017 : Nat := 4983230072969 + 3 ^ 40 * 813017 * 2
def baseEnd_813017 : Nat := 417468501276550800948509

theorem tailTrace_813017 : CollatzResearch.WordTrace tailWord_813017 prefixEnd_813017 417468501276550800948509 := by
  unfold tailWord_813017
  simp only [CollatzResearch.WordTrace]
  refine ⟨29653166095585736094117305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19768777397057157396078203 29653166095585736094117305)
  ·
    refine ⟨22239874571689302070587979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29653166095585736094117305 22239874571689302070587979)
    ·
      refine ⟨33359811857533953105881969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22239874571689302070587979 33359811857533953105881969)
      ·
        refine ⟨25019858893150464829411477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33359811857533953105881969 25019858893150464829411477)
        ·
          refine ⟨1172805885616428038878663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25019858893150464829411477 1172805885616428038878663)
          ·
            refine ⟨1759208828424642058317995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172805885616428038878663 1759208828424642058317995)
            ·
              refine ⟨2638813242636963087476993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759208828424642058317995 2638813242636963087476993)
              ·
                refine ⟨1979109931977722315607745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638813242636963087476993 1979109931977722315607745)
                ·
                  refine ⟨1484332448983291736705809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1979109931977722315607745 1484332448983291736705809)
                  ·
                    refine ⟨1113249336737468802529357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1484332448983291736705809 1113249336737468802529357)
                    ·
                      refine ⟨417468501276550800948509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1113249336737468802529357 417468501276550800948509)
                      ·
                        rfl

theorem cell23_813017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_813017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813017 prefixEnd_813017 := by exact prefixLift 813017
  have htrace : WordTrace (prefixWord ++ tailWord_813017) baseStart_813017 baseEnd_813017 := by
    simpa [prefixWord, tailWord_813017, baseEnd_813017] using wordTrace_append hprefix tailTrace_813017
  have hstable : (prefixWord ++ tailWord_813017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813017).length < 2 ^ (prefixWord ++ tailWord_813017).sum := by decide
  have hdescent : baseEnd_813017 < baseStart_813017 := by decide
  rcases family_descends (prefixWord ++ tailWord_813017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813040 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 3, 5, 2]
def baseStart_813040 : Nat := 118140960795 + 813040 * 2 ^ 59
def prefixEnd_813040 : Nat := 4983230072969 + 3 ^ 40 * 813040 * 2
def baseEnd_813040 : Nat := 417480311331604210960903

theorem tailTrace_813040 : CollatzResearch.WordTrace tailWord_813040 prefixEnd_813040 417480311331604210960903 := by
  unfold tailWord_813040
  simp only [CollatzResearch.WordTrace]
  refine ⟨14827002487251205511102287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19769336649668274014803049 14827002487251205511102287)
  ·
    refine ⟨22240503730876808266653431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14827002487251205511102287 22240503730876808266653431)
    ·
      refine ⟨33360755596315212399980147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22240503730876808266653431 33360755596315212399980147)
      ·
        refine ⟨50041133394472818599970221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33360755596315212399980147 50041133394472818599970221)
        ·
          refine ⟨18765425022927306974988833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50041133394472818599970221 18765425022927306974988833)
          ·
            refine ⟨14074068767195480231241625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18765425022927306974988833 14074068767195480231241625)
            ·
              refine ⟨10555551575396610173431219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14074068767195480231241625 10555551575396610173431219)
              ·
                refine ⟨15833327363094915260146829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10555551575396610173431219 15833327363094915260146829)
                ·
                  refine ⟨5937497761160593222555061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15833327363094915260146829 5937497761160593222555061)
                  ·
                    refine ⟨556640415108805614614537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5937497761160593222555061 556640415108805614614537)
                    ·
                      refine ⟨417480311331604210960903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556640415108805614614537 417480311331604210960903)
                      ·
                        rfl

theorem cell23_813040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 5, 2].length) (baseStart_813040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813040 prefixEnd_813040 := by exact prefixLift 813040
  have htrace : WordTrace (prefixWord ++ tailWord_813040) baseStart_813040 baseEnd_813040 := by
    simpa [prefixWord, tailWord_813040, baseEnd_813040] using wordTrace_append hprefix tailTrace_813040
  have hstable : (prefixWord ++ tailWord_813040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813040).length < 2 ^ (prefixWord ++ tailWord_813040).sum := by decide
  have hdescent : baseEnd_813040 < baseStart_813040 := by decide
  rcases family_descends (prefixWord ++ tailWord_813040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813064 : List Nat := [2, 1, 3, 2, 1, 2, 2, 5, 1, 1, 3]
def baseStart_813064 : Nat := 118140960795 + 813064 * 2 ^ 59
def prefixEnd_813064 : Nat := 4983230072969 + 3 ^ 40 * 813064 * 2
def baseEnd_813064 : Nat := 417492634867312117060793

theorem tailTrace_813064 : CollatzResearch.WordTrace tailWord_813064 prefixEnd_813064 417492634867312117060793 := by
  unfold tailWord_813064
  simp only [CollatzResearch.WordTrace]
  refine ⟨14827440163207731560539123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19769920217610308747385497 14827440163207731560539123)
  ·
    refine ⟨22241160244811597340808685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14827440163207731560539123 22241160244811597340808685)
    ·
      refine ⟨8340435091804349002803257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22241160244811597340808685 8340435091804349002803257)
      ·
        refine ⟨6255326318853261752102443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8340435091804349002803257 6255326318853261752102443)
        ·
          refine ⟨9382989478279892628153665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6255326318853261752102443 9382989478279892628153665)
          ·
            refine ⟨7037242108709919471115249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9382989478279892628153665 7037242108709919471115249)
            ·
              refine ⟨5277931581532439603336437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7037242108709919471115249 5277931581532439603336437)
              ·
                refine ⟨494806085768666212812791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5277931581532439603336437 494806085768666212812791)
                ·
                  refine ⟨742209128652999319219187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494806085768666212812791 742209128652999319219187)
                  ·
                    refine ⟨1113313692979498978828781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 742209128652999319219187 1113313692979498978828781)
                    ·
                      refine ⟨417492634867312117060793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1113313692979498978828781 417492634867312117060793)
                      ·
                        rfl

theorem cell23_813064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_813064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813064 prefixEnd_813064 := by exact prefixLift 813064
  have htrace : WordTrace (prefixWord ++ tailWord_813064) baseStart_813064 baseEnd_813064 := by
    simpa [prefixWord, tailWord_813064, baseEnd_813064] using wordTrace_append hprefix tailTrace_813064
  have hstable : (prefixWord ++ tailWord_813064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813064).length < 2 ^ (prefixWord ++ tailWord_813064).sum := by decide
  have hdescent : baseEnd_813064 < baseStart_813064 := by decide
  rcases family_descends (prefixWord ++ tailWord_813064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813067 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 1, 5]
def baseStart_813067 : Nat := 118140960795 + 813067 * 2 ^ 59
def prefixEnd_813067 : Nat := 4983230072969 + 3 ^ 40 * 813067 * 2
def baseEnd_813067 : Nat := 139164725103091868441093

theorem tailTrace_813067 : CollatzResearch.WordTrace tailWord_813067 prefixEnd_813067 139164725103091868441093 := by
  unfold tailWord_813067
  simp only [CollatzResearch.WordTrace]
  refine ⟨29654989745404594633437455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19769993163603063088958303 29654989745404594633437455)
  ·
    refine ⟨44482484618106891950156183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29654989745404594633437455 44482484618106891950156183)
    ·
      refine ⟨66723726927160337925234275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44482484618106891950156183 66723726927160337925234275)
      ·
        refine ⟨100085590390740506887851413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66723726927160337925234275 100085590390740506887851413)
        ·
          refine ⟨4691512049565961260368035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100085590390740506887851413 4691512049565961260368035)
          ·
            refine ⟨7037268074348941890552053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4691512049565961260368035 7037268074348941890552053)
            ·
              refine ⟨659743881970213302239255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7037268074348941890552053 659743881970213302239255)
              ·
                refine ⟨989615822955319953358883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659743881970213302239255 989615822955319953358883)
                ·
                  refine ⟨1484423734432979930038325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989615822955319953358883 1484423734432979930038325)
                  ·
                    refine ⟨139164725103091868441093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1484423734432979930038325 139164725103091868441093)
                    ·
                      rfl

theorem cell23_813067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 5].length) (baseStart_813067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813067 prefixEnd_813067 := by exact prefixLift 813067
  have htrace : WordTrace (prefixWord ++ tailWord_813067) baseStart_813067 baseEnd_813067 := by
    simpa [prefixWord, tailWord_813067, baseEnd_813067] using wordTrace_append hprefix tailTrace_813067
  have hstable : (prefixWord ++ tailWord_813067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813067).length < 2 ^ (prefixWord ++ tailWord_813067).sum := by decide
  have hdescent : baseEnd_813067 < baseStart_813067 := by decide
  rcases family_descends (prefixWord ++ tailWord_813067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813083 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 6]
def baseStart_813083 : Nat := 118140960795 + 813083 * 2 ^ 59
def prefixEnd_813083 : Nat := 4983230072969 + 3 ^ 40 * 813083 * 2
def baseEnd_813083 : Nat := 417502390999747542723205

theorem tailTrace_813083 : CollatzResearch.WordTrace tailWord_813083 prefixEnd_813083 417502390999747542723205 := by
  unfold tailWord_813083
  simp only [CollatzResearch.WordTrace]
  refine ⟨29655573313346629366019903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19770382208897752910679935 29655573313346629366019903)
  ·
    refine ⟨44483359970019944049029855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29655573313346629366019903 44483359970019944049029855)
    ·
      refine ⟨66725039955029916073544783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44483359970019944049029855 66725039955029916073544783)
      ·
        refine ⟨100087559932544874110317175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66725039955029916073544783 100087559932544874110317175)
        ·
          refine ⟨150131339898817311165475763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100087559932544874110317175 150131339898817311165475763)
          ·
            refine ⟨225197009848225966748213645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150131339898817311165475763 225197009848225966748213645)
            ·
              refine ⟨84448878693084737530580117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225197009848225966748213645 84448878693084737530580117)
              ·
                refine ⟨3958541188738347071745943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84448878693084737530580117 3958541188738347071745943)
                ·
                  refine ⟨5937811783107520607618915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958541188738347071745943 5937811783107520607618915)
                  ·
                    refine ⟨8906717674661280911428373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5937811783107520607618915 8906717674661280911428373)
                    ·
                      refine ⟨417502390999747542723205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8906717674661280911428373 417502390999747542723205)
                      ·
                        rfl

theorem cell23_813083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 6].length) (baseStart_813083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813083 prefixEnd_813083 := by exact prefixLift 813083
  have htrace : WordTrace (prefixWord ++ tailWord_813083) baseStart_813083 baseEnd_813083 := by
    simpa [prefixWord, tailWord_813083, baseEnd_813083] using wordTrace_append hprefix tailTrace_813083
  have hstable : (prefixWord ++ tailWord_813083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813083).length < 2 ^ (prefixWord ++ tailWord_813083).sum := by decide
  have hdescent : baseEnd_813083 < baseStart_813083 := by decide
  rcases family_descends (prefixWord ++ tailWord_813083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813090 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_813090 : Nat := 118140960795 + 813090 * 2 ^ 59
def prefixEnd_813090 : Nat := 4983230072969 + 3 ^ 40 * 813090 * 2
def baseEnd_813090 : Nat := 417505985364329015335673

theorem tailTrace_813090 : CollatzResearch.WordTrace tailWord_813090 prefixEnd_813090 417505985364329015335673 := by
  unfold tailWord_813090
  simp only [CollatzResearch.WordTrace]
  refine ⟨7413957156080317390381181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19770552416214179707683149 7413957156080317390381181)
  ·
    refine ⟨2780233933530119021392943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7413957156080317390381181 2780233933530119021392943)
    ·
      refine ⟨4170350900295178532089415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2780233933530119021392943 4170350900295178532089415)
      ·
        refine ⟨6255526350442767798134123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170350900295178532089415 6255526350442767798134123)
        ·
          refine ⟨9383289525664151697201185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6255526350442767798134123 9383289525664151697201185)
          ·
            refine ⟨7037467144248113772900889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9383289525664151697201185 7037467144248113772900889)
            ·
              refine ⟨5278100358186085329675667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7037467144248113772900889 5278100358186085329675667)
              ·
                refine ⟨7917150537279127994513501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5278100358186085329675667 7917150537279127994513501)
                ·
                  refine ⟨2968931451479672997942563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7917150537279127994513501 2968931451479672997942563)
                  ·
                    refine ⟨4453397177219509496913845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2968931451479672997942563 4453397177219509496913845)
                    ·
                      refine ⟨417505985364329015335673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4453397177219509496913845 417505985364329015335673)
                      ·
                        rfl

theorem cell23_813090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_813090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813090 prefixEnd_813090 := by exact prefixLift 813090
  have htrace : WordTrace (prefixWord ++ tailWord_813090) baseStart_813090 baseEnd_813090 := by
    simpa [prefixWord, tailWord_813090, baseEnd_813090] using wordTrace_append hprefix tailTrace_813090
  have hstable : (prefixWord ++ tailWord_813090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813090).length < 2 ^ (prefixWord ++ tailWord_813090).sum := by decide
  have hdescent : baseEnd_813090 < baseStart_813090 := by decide
  rcases family_descends (prefixWord ++ tailWord_813090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813104 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 3, 2, 2]
def baseStart_813104 : Nat := 118140960795 + 813104 * 2 ^ 59
def prefixEnd_813104 : Nat := 4983230072969 + 3 ^ 40 * 813104 * 2
def baseEnd_813104 : Nat := 417513174093491960560609

theorem tailTrace_813104 : CollatzResearch.WordTrace tailWord_813104 prefixEnd_813104 417513174093491960560609 := by
  unfold tailWord_813104
  simp only [CollatzResearch.WordTrace]
  refine ⟨14828169623135274976267183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19770892830847033301689577 14828169623135274976267183)
  ·
    refine ⟨22242254434702912464400775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14828169623135274976267183 22242254434702912464400775)
    ·
      refine ⟨33363381652054368696601163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22242254434702912464400775 33363381652054368696601163)
      ·
        refine ⟨50045072478081553044901745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33363381652054368696601163 50045072478081553044901745)
        ·
          refine ⟨37533804358561164783676309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50045072478081553044901745 37533804358561164783676309)
          ·
            refine ⟨1759397079307554599234827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37533804358561164783676309 1759397079307554599234827)
            ·
              refine ⟨2639095618961331898852241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759397079307554599234827 2639095618961331898852241)
              ·
                refine ⟨1979321714220998924139181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639095618961331898852241 1979321714220998924139181)
                ·
                  refine ⟨742245642832874596552193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1979321714220998924139181 742245642832874596552193)
                  ·
                    refine ⟨556684232124655947414145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 742245642832874596552193 556684232124655947414145)
                    ·
                      refine ⟨417513174093491960560609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556684232124655947414145 417513174093491960560609)
                      ·
                        rfl

theorem cell23_813104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3, 2, 2].length) (baseStart_813104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813104 prefixEnd_813104 := by exact prefixLift 813104
  have htrace : WordTrace (prefixWord ++ tailWord_813104) baseStart_813104 baseEnd_813104 := by
    simpa [prefixWord, tailWord_813104, baseEnd_813104] using wordTrace_append hprefix tailTrace_813104
  have hstable : (prefixWord ++ tailWord_813104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813104).length < 2 ^ (prefixWord ++ tailWord_813104).sum := by decide
  have hdescent : baseEnd_813104 < baseStart_813104 := by decide
  rcases family_descends (prefixWord ++ tailWord_813104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813108 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_813108 : Nat := 118140960795 + 813108 * 2 ^ 59
def prefixEnd_813108 : Nat := 4983230072969 + 3 ^ 40 * 813108 * 2
def baseEnd_813108 : Nat := 417515228016109944910591

theorem tailTrace_813108 : CollatzResearch.WordTrace tailWord_813108 prefixEnd_813108 417515228016109944910591 := by
  unfold tailWord_813108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14828242569128029317839989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19770990092170705757119985 14828242569128029317839989)
  ·
    refine ⟨1390147740855752748547499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14828242569128029317839989 1390147740855752748547499)
    ·
      refine ⟨2085221611283629122821249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390147740855752748547499 2085221611283629122821249)
      ·
        refine ⟨1563916208462721842115937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2085221611283629122821249 1563916208462721842115937)
        ·
          refine ⟨1172937156347041381586953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1563916208462721842115937 1172937156347041381586953)
          ·
            refine ⟨879702867260281036190215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1172937156347041381586953 879702867260281036190215)
            ·
              refine ⟨1319554300890421554285323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879702867260281036190215 1319554300890421554285323)
              ·
                refine ⟨1979331451335632331427985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319554300890421554285323 1979331451335632331427985)
                ·
                  refine ⟨1484498588501724248570989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1979331451335632331427985 1484498588501724248570989)
                  ·
                    refine ⟨556686970688146593214121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1484498588501724248570989 556686970688146593214121)
                    ·
                      refine ⟨417515228016109944910591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556686970688146593214121 417515228016109944910591)
                      ·
                        rfl

theorem cell23_813108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_813108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813108 prefixEnd_813108 := by exact prefixLift 813108
  have htrace : WordTrace (prefixWord ++ tailWord_813108) baseStart_813108 baseEnd_813108 := by
    simpa [prefixWord, tailWord_813108, baseEnd_813108] using wordTrace_append hprefix tailTrace_813108
  have hstable : (prefixWord ++ tailWord_813108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813108).length < 2 ^ (prefixWord ++ tailWord_813108).sum := by decide
  have hdescent : baseEnd_813108 < baseStart_813108 := by decide
  rcases family_descends (prefixWord ++ tailWord_813108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813118 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_813118 : Nat := 118140960795 + 813118 * 2 ^ 59
def prefixEnd_813118 : Nat := 4983230072969 + 3 ^ 40 * 813118 * 2
def baseEnd_813118 : Nat := 139173454274218301928515

theorem tailTrace_813118 : CollatzResearch.WordTrace tailWord_813118 prefixEnd_813118 139173454274218301928515 := by
  unfold tailWord_813118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707106233527478792943001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19771233245479886895696005 3707106233527478792943001)
  ·
    refine ⟨2780329675145609094707251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3707106233527478792943001 2780329675145609094707251)
    ·
      refine ⟨4170494512718413642060877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2780329675145609094707251 4170494512718413642060877)
      ·
        refine ⟨1563935442269405115772829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4170494512718413642060877 1563935442269405115772829)
        ·
          refine ⟨586475790851026918414811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1563935442269405115772829 586475790851026918414811)
          ·
            refine ⟨879713686276540377622217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586475790851026918414811 879713686276540377622217)
            ·
              refine ⟨659785264707405283216663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879713686276540377622217 659785264707405283216663)
              ·
                refine ⟨989677897061107924824995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659785264707405283216663 989677897061107924824995)
                ·
                  refine ⟨1484516845591661887237493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989677897061107924824995 1484516845591661887237493)
                  ·
                    refine ⟨139173454274218301928515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1484516845591661887237493 139173454274218301928515)
                    ·
                      rfl

theorem cell23_813118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_813118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813118 prefixEnd_813118 := by exact prefixLift 813118
  have htrace : WordTrace (prefixWord ++ tailWord_813118) baseStart_813118 baseEnd_813118 := by
    simpa [prefixWord, tailWord_813118, baseEnd_813118] using wordTrace_append hprefix tailTrace_813118
  have hstable : (prefixWord ++ tailWord_813118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813118).length < 2 ^ (prefixWord ++ tailWord_813118).sum := by decide
  have hdescent : baseEnd_813118 < baseStart_813118 := by decide
  rcases family_descends (prefixWord ++ tailWord_813118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813121 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_813121 : Nat := 118140960795 + 813121 * 2 ^ 59
def prefixEnd_813121 : Nat := 4983230072969 + 3 ^ 40 * 813121 * 2
def baseEnd_813121 : Nat := 417521903264618394048031

theorem tailTrace_813121 : CollatzResearch.WordTrace tailWord_813121 prefixEnd_813121 417521903264618394048031 := by
  unfold tailWord_813121
  simp only [CollatzResearch.WordTrace]
  refine ⟨29656959287208961855903217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19771306191472641237268811 29656959287208961855903217)
  ·
    refine ⟨22242719465406721391927413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29656959287208961855903217 22242719465406721391927413)
    ·
      refine ⟨2085254949881880130493195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22242719465406721391927413 2085254949881880130493195)
      ·
        refine ⟨3127882424822820195739793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2085254949881880130493195 3127882424822820195739793)
        ·
          refine ⟨2345911818617115146804845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3127882424822820195739793 2345911818617115146804845)
          ·
            refine ⟨879716931981418180051817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2345911818617115146804845 879716931981418180051817)
            ·
              refine ⟨659787698986063635038863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879716931981418180051817 659787698986063635038863)
              ·
                refine ⟨989681548479095452558295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659787698986063635038863 989681548479095452558295)
                ·
                  refine ⟨1484522322718643178837443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989681548479095452558295 1484522322718643178837443)
                  ·
                    refine ⟨2226783484077964768256165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1484522322718643178837443 2226783484077964768256165)
                    ·
                      refine ⟨417521903264618394048031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2226783484077964768256165 417521903264618394048031)
                      ·
                        rfl

theorem cell23_813121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_813121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813121 prefixEnd_813121 := by exact prefixLift 813121
  have htrace : WordTrace (prefixWord ++ tailWord_813121) baseStart_813121 baseEnd_813121 := by
    simpa [prefixWord, tailWord_813121, baseEnd_813121] using wordTrace_append hprefix tailTrace_813121
  have hstable : (prefixWord ++ tailWord_813121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813121).length < 2 ^ (prefixWord ++ tailWord_813121).sum := by decide
  have hdescent : baseEnd_813121 < baseStart_813121 := by decide
  rcases family_descends (prefixWord ++ tailWord_813121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813123 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 1, 9]
def baseStart_813123 : Nat := 118140960795 + 813123 * 2 ^ 59
def prefixEnd_813123 : Nat := 4983230072969 + 3 ^ 40 * 813123 * 2
def baseEnd_813123 : Nat := 139174310075309128741007

theorem tailTrace_813123 : CollatzResearch.WordTrace tailWord_813123 prefixEnd_813123 139174310075309128741007 := by
  unfold tailWord_813123
  simp only [CollatzResearch.WordTrace]
  refine ⟨29657032233201716197476023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19771354822134477464984015 29657032233201716197476023)
  ·
    refine ⟨44485548349802574296214035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29657032233201716197476023 44485548349802574296214035)
    ·
      refine ⟨66728322524703861444321053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44485548349802574296214035 66728322524703861444321053)
      ·
        refine ⟨25023120946763948041620395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66728322524703861444321053 25023120946763948041620395)
        ·
          refine ⟨37534681420145922062430593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25023120946763948041620395 37534681420145922062430593)
          ·
            refine ⟨28151011065109441546822945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37534681420145922062430593 28151011065109441546822945)
            ·
              refine ⟨21113258298832081160117209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28151011065109441546822945 21113258298832081160117209)
              ·
                refine ⟨15834943724124060870087907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21113258298832081160117209 15834943724124060870087907)
                ·
                  refine ⟨23752415586186091305131861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15834943724124060870087907 23752415586186091305131861)
                  ·
                    refine ⟨139174310075309128741007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 23752415586186091305131861 139174310075309128741007)
                    ·
                      rfl

theorem cell23_813123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 9].length) (baseStart_813123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813123 prefixEnd_813123 := by exact prefixLift 813123
  have htrace : WordTrace (prefixWord ++ tailWord_813123) baseStart_813123 baseEnd_813123 := by
    simpa [prefixWord, tailWord_813123, baseEnd_813123] using wordTrace_append hprefix tailTrace_813123
  have hstable : (prefixWord ++ tailWord_813123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813123).length < 2 ^ (prefixWord ++ tailWord_813123).sum := by decide
  have hdescent : baseEnd_813123 < baseStart_813123 := by decide
  rcases family_descends (prefixWord ++ tailWord_813123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813164 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 1, 3, 2]
def baseStart_813164 : Nat := 118140960795 + 813164 * 2 ^ 59
def prefixEnd_813164 : Nat := 4983230072969 + 3 ^ 40 * 813164 * 2
def baseEnd_813164 : Nat := 417543982932761725810333

theorem tailTrace_813164 : CollatzResearch.WordTrace tailWord_813164 prefixEnd_813164 417543982932761725810333 := by
  unfold tailWord_813164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829263813026590099859273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19772351750702120133145697 14829263813026590099859273)
  ·
    refine ⟨11121947859769942574894455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14829263813026590099859273 11121947859769942574894455)
    ·
      refine ⟨16682921789654913862341683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11121947859769942574894455 16682921789654913862341683)
      ·
        refine ⟨25024382684482370793512525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16682921789654913862341683 25024382684482370793512525)
        ·
          refine ⟨9384143506680889047567197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25024382684482370793512525 9384143506680889047567197)
          ·
            refine ⟨3519053815005333392837699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9384143506680889047567197 3519053815005333392837699)
            ·
              refine ⟨5278580722508000089256549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519053815005333392837699 5278580722508000089256549)
              ·
                refine ⟨989733885470250016735603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5278580722508000089256549 989733885470250016735603)
                ·
                  refine ⟨1484600828205375025103405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989733885470250016735603 1484600828205375025103405)
                  ·
                    refine ⟨556725310577015634413777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1484600828205375025103405 556725310577015634413777)
                    ·
                      refine ⟨417543982932761725810333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556725310577015634413777 417543982932761725810333)
                      ·
                        rfl

theorem cell23_813164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_813164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813164 prefixEnd_813164 := by exact prefixLift 813164
  have htrace : WordTrace (prefixWord ++ tailWord_813164) baseStart_813164 baseEnd_813164 := by
    simpa [prefixWord, tailWord_813164, baseEnd_813164] using wordTrace_append hprefix tailTrace_813164
  have hstable : (prefixWord ++ tailWord_813164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813164).length < 2 ^ (prefixWord ++ tailWord_813164).sum := by decide
  have hdescent : baseEnd_813164 < baseStart_813164 := by decide
  rcases family_descends (prefixWord ++ tailWord_813164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813180 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_813180 : Nat := 118140960795 + 813180 * 2 ^ 59
def prefixEnd_813180 : Nat := 4983230072969 + 3 ^ 40 * 813180 * 2
def baseEnd_813180 : Nat := 417552198623233663210259

theorem tailTrace_813180 : CollatzResearch.WordTrace tailWord_813180 prefixEnd_813180 417552198623233663210259 := by
  unfold tailWord_813180
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829555596997607466150497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19772740795996809954867329 14829555596997607466150497)
  ·
    refine ⟨11122166697748205599612873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14829555596997607466150497 11122166697748205599612873)
    ·
      refine ⟨8341625023311154199709655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11122166697748205599612873 8341625023311154199709655)
      ·
        refine ⟨12512437534966731299564483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8341625023311154199709655 12512437534966731299564483)
        ·
          refine ⟨18768656302450096949346725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12512437534966731299564483 18768656302450096949346725)
          ·
            refine ⟨3519123056709393178002511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18768656302450096949346725 3519123056709393178002511)
            ·
              refine ⟨5278684585064089767003767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519123056709393178002511 5278684585064089767003767)
              ·
                refine ⟨7918026877596134650505651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5278684585064089767003767 7918026877596134650505651)
                ·
                  refine ⟨11877040316394201975758477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7918026877596134650505651 11877040316394201975758477)
                  ·
                    refine ⟨4453890118647825740909429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11877040316394201975758477 4453890118647825740909429)
                    ·
                      refine ⟨417552198623233663210259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4453890118647825740909429 417552198623233663210259)
                      ·
                        rfl

theorem cell23_813180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_813180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813180 prefixEnd_813180 := by exact prefixLift 813180
  have htrace : WordTrace (prefixWord ++ tailWord_813180) baseStart_813180 baseEnd_813180 := by
    simpa [prefixWord, tailWord_813180, baseEnd_813180] using wordTrace_append hprefix tailTrace_813180
  have hstable : (prefixWord ++ tailWord_813180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813180).length < 2 ^ (prefixWord ++ tailWord_813180).sum := by decide
  have hdescent : baseEnd_813180 < baseStart_813180 := by decide
  rcases family_descends (prefixWord ++ tailWord_813180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813240 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_813240 : Nat := 118140960795 + 813240 * 2 ^ 59
def prefixEnd_813240 : Nat := 4983230072969 + 3 ^ 40 * 813240 * 2
def baseEnd_813240 : Nat := 417583007462503428459983

theorem tailTrace_813240 : CollatzResearch.WordTrace tailWord_813240 prefixEnd_813240 417583007462503428459983 := by
  unfold tailWord_813240
  simp only [CollatzResearch.WordTrace]
  refine ⟨14830649786888922589742587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19774199715851896786323449 14830649786888922589742587)
  ·
    refine ⟨22245974680333383884613881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14830649786888922589742587 22245974680333383884613881)
    ·
      refine ⟨16684481010250037913460411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22245974680333383884613881 16684481010250037913460411)
      ·
        refine ⟨25026721515375056870190617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16684481010250037913460411 25026721515375056870190617)
        ·
          refine ⟨18770041136531292652642963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25026721515375056870190617 18770041136531292652642963)
          ·
            refine ⟨28155061704796938978964445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18770041136531292652642963 28155061704796938978964445)
            ·
              refine ⟨10558148139298852117111667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28155061704796938978964445 10558148139298852117111667)
              ·
                refine ⟨15837222208948278175667501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10558148139298852117111667 15837222208948278175667501)
                ·
                  refine ⟨5938958328355604315875313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15837222208948278175667501 5938958328355604315875313)
                  ·
                    refine ⟨4454218746266703236906485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5938958328355604315875313 4454218746266703236906485)
                    ·
                      refine ⟨417583007462503428459983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4454218746266703236906485 417583007462503428459983)
                      ·
                        rfl

theorem cell23_813240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_813240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813240 prefixEnd_813240 := by exact prefixLift 813240
  have htrace : WordTrace (prefixWord ++ tailWord_813240) baseStart_813240 baseEnd_813240 := by
    simpa [prefixWord, tailWord_813240, baseEnd_813240] using wordTrace_append hprefix tailTrace_813240
  have hstable : (prefixWord ++ tailWord_813240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813240).length < 2 ^ (prefixWord ++ tailWord_813240).sum := by decide
  have hdescent : baseEnd_813240 < baseStart_813240 := by decide
  rcases family_descends (prefixWord ++ tailWord_813240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813324 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 6]
def baseStart_813324 : Nat := 118140960795 + 813324 * 2 ^ 59
def prefixEnd_813324 : Nat := 4983230072969 + 3 ^ 40 * 813324 * 2
def baseEnd_813324 : Nat := 46402904426386788867733

theorem tailTrace_813324 : CollatzResearch.WordTrace tailWord_813324 prefixEnd_813324 46402904426386788867733 := by
  unfold tailWord_813324
  simp only [CollatzResearch.WordTrace]
  refine ⟨14832181652736763762771513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19776242203649018350362017 14832181652736763762771513)
  ·
    refine ⟨11124136239552572822078635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14832181652736763762771513 11124136239552572822078635)
    ·
      refine ⟨16686204359328859233117953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11124136239552572822078635 16686204359328859233117953)
      ·
        refine ⟨12514653269496644424838465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16686204359328859233117953 12514653269496644424838465)
        ·
          refine ⟨9385989952122483318628849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12514653269496644424838465 9385989952122483318628849)
          ·
            refine ⟨7039492464091862488971637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9385989952122483318628849 7039492464091862488971637)
            ·
              refine ⟨659952418508612108341091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7039492464091862488971637 659952418508612108341091)
              ·
                refine ⟨989928627762918162511637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659952418508612108341091 989928627762918162511637)
                ·
                  refine ⟨46402904426386788867733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 989928627762918162511637 46402904426386788867733)
                  ·
                    rfl

theorem cell23_813324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_813324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813324 prefixEnd_813324 := by exact prefixLift 813324
  have htrace : WordTrace (prefixWord ++ tailWord_813324) baseStart_813324 baseEnd_813324 := by
    simpa [prefixWord, tailWord_813324, baseEnd_813324] using wordTrace_append hprefix tailTrace_813324
  have hstable : (prefixWord ++ tailWord_813324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813324).length < 2 ^ (prefixWord ++ tailWord_813324).sum := by decide
  have hdescent : baseEnd_813324 < baseStart_813324 := by decide
  rcases family_descends (prefixWord ++ tailWord_813324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813408 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 1, 1, 4]
def baseStart_813408 : Nat := 118140960795 + 813408 * 2 ^ 59
def prefixEnd_813408 : Nat := 4983230072969 + 3 ^ 40 * 813408 * 2
def baseEnd_813408 : Nat := 417669272212458771159211

theorem tailTrace_813408 : CollatzResearch.WordTrace tailWord_813408 prefixEnd_813408 417669272212458771159211 := by
  unfold tailWord_813408
  simp only [CollatzResearch.WordTrace]
  refine ⟨14833713518584604935800439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19778284691446139914400585 14833713518584604935800439)
  ·
    refine ⟨22250570277876907403700659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14833713518584604935800439 22250570277876907403700659)
    ·
      refine ⟨33375855416815361105550989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22250570277876907403700659 33375855416815361105550989)
      ·
        refine ⟨12515945781305760414581621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33375855416815361105550989 12515945781305760414581621)
        ·
          refine ⟨1173369916997415038867027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12515945781305760414581621 1173369916997415038867027)
          ·
            refine ⟨1760054875496122558300541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173369916997415038867027 1760054875496122558300541)
            ·
              refine ⟨660020578311045959362703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1760054875496122558300541 660020578311045959362703)
              ·
                refine ⟨990030867466568939044055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660020578311045959362703 990030867466568939044055)
                ·
                  refine ⟨1485046301199853408566083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990030867466568939044055 1485046301199853408566083)
                  ·
                    refine ⟨2227569451799780112849125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1485046301199853408566083 2227569451799780112849125)
                    ·
                      refine ⟨417669272212458771159211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2227569451799780112849125 417669272212458771159211)
                      ·
                        rfl

theorem cell23_813408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_813408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813408 prefixEnd_813408 := by exact prefixLift 813408
  have htrace : WordTrace (prefixWord ++ tailWord_813408) baseStart_813408 baseEnd_813408 := by
    simpa [prefixWord, tailWord_813408, baseEnd_813408] using wordTrace_append hprefix tailTrace_813408
  have hstable : (prefixWord ++ tailWord_813408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813408).length < 2 ^ (prefixWord ++ tailWord_813408).sum := by decide
  have hdescent : baseEnd_813408 < baseStart_813408 := by decide
  rcases family_descends (prefixWord ++ tailWord_813408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813418 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_813418 : Nat := 118140960795 + 813418 * 2 ^ 59
def prefixEnd_813418 : Nat := 4983230072969 + 3 ^ 40 * 813418 * 2
def baseEnd_813418 : Nat := 139224802339667910678055

theorem tailTrace_813418 : CollatzResearch.WordTrace tailWord_813418 prefixEnd_813418 139224802339667910678055 := by
  unfold tailWord_813418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7416947941783245394866227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19778527844755321052976605 7416947941783245394866227)
  ·
    refine ⟨11125421912674868092299341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7416947941783245394866227 11125421912674868092299341)
    ·
      refine ⟨4172033217253075534612253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11125421912674868092299341 4172033217253075534612253)
      ·
        refine ⟨1564512456469903325479595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4172033217253075534612253 1564512456469903325479595)
        ·
          refine ⟨2346768684704854988219393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564512456469903325479595 2346768684704854988219393)
          ·
            refine ⟨1760076513528641241164545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2346768684704854988219393 1760076513528641241164545)
            ·
              refine ⟨1320057385146480930873409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760076513528641241164545 1320057385146480930873409)
              ·
                refine ⟨990043038859860698155057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320057385146480930873409 990043038859860698155057)
                ·
                  refine ⟨742532279144895523616293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 990043038859860698155057 742532279144895523616293)
                  ·
                    refine ⟨139224802339667910678055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 742532279144895523616293 139224802339667910678055)
                    ·
                      rfl

theorem cell23_813418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_813418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813418 prefixEnd_813418 := by exact prefixLift 813418
  have htrace : WordTrace (prefixWord ++ tailWord_813418) baseStart_813418 baseEnd_813418 := by
    simpa [prefixWord, tailWord_813418, baseEnd_813418] using wordTrace_append hprefix tailTrace_813418
  have hstable : (prefixWord ++ tailWord_813418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813418).length < 2 ^ (prefixWord ++ tailWord_813418).sum := by decide
  have hdescent : baseEnd_813418 < baseStart_813418 := by decide
  rcases family_descends (prefixWord ++ tailWord_813418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813434 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2]
def baseStart_813434 : Nat := 118140960795 + 813434 * 2 ^ 59
def prefixEnd_813434 : Nat := 4983230072969 + 3 ^ 40 * 813434 * 2
def baseEnd_813434 : Nat := 417682622709475669434091

theorem tailTrace_813434 : CollatzResearch.WordTrace tailWord_813434 prefixEnd_813434 417682622709475669434091 := by
  unfold tailWord_813434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7417093833768754078011839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19778916890050010874698237 7417093833768754078011839)
  ·
    refine ⟨11125640750653131117017759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7417093833768754078011839 11125640750653131117017759)
    ·
      refine ⟨16688461125979696675526639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11125640750653131117017759 16688461125979696675526639)
      ·
        refine ⟨25032691688969545013289959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16688461125979696675526639 25032691688969545013289959)
        ·
          refine ⟨37549037533454317519934939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25032691688969545013289959 37549037533454317519934939)
          ·
            refine ⟨56323556300181476279902409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37549037533454317519934939 56323556300181476279902409)
            ·
              refine ⟨42242667225136107209926807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56323556300181476279902409 42242667225136107209926807)
              ·
                refine ⟨63364000837704160814890211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42242667225136107209926807 63364000837704160814890211)
                ·
                  refine ⟨95046001256556241222335317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63364000837704160814890211 95046001256556241222335317)
                  ·
                    refine ⟨556910163612634225912121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 95046001256556241222335317 556910163612634225912121)
                    ·
                      refine ⟨417682622709475669434091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556910163612634225912121 417682622709475669434091)
                      ·
                        rfl

theorem cell23_813434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_813434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813434 prefixEnd_813434 := by exact prefixLift 813434
  have htrace : WordTrace (prefixWord ++ tailWord_813434) baseStart_813434 baseEnd_813434 := by
    simpa [prefixWord, tailWord_813434, baseEnd_813434] using wordTrace_append hprefix tailTrace_813434
  have hstable : (prefixWord ++ tailWord_813434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813434).length < 2 ^ (prefixWord ++ tailWord_813434).sum := by decide
  have hdescent : baseEnd_813434 < baseStart_813434 := by decide
  rcases family_descends (prefixWord ++ tailWord_813434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813441 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_813441 : Nat := 118140960795 + 813441 * 2 ^ 59
def prefixEnd_813441 : Nat := 4983230072969 + 3 ^ 40 * 813441 * 2
def baseEnd_813441 : Nat := 417686217074057142046559

theorem tailTrace_813441 : CollatzResearch.WordTrace tailWord_813441 prefixEnd_813441 417686217074057142046559 := by
  unfold tailWord_813441
  simp only [CollatzResearch.WordTrace]
  refine ⟨29668630646049656507552177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19779087097366437671701451 29668630646049656507552177)
  ·
    refine ⟨22251472984537242380664133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29668630646049656507552177 22251472984537242380664133)
    ·
      refine ⟨4172151184600732946374525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22251472984537242380664133 4172151184600732946374525)
      ·
        refine ⟨1564556694225274854890447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4172151184600732946374525 1564556694225274854890447)
        ·
          refine ⟨2346835041337912282335671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564556694225274854890447 2346835041337912282335671)
          ·
            refine ⟨3520252562006868423503507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346835041337912282335671 3520252562006868423503507)
            ·
              refine ⟨5280378843010302635255261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520252562006868423503507 5280378843010302635255261)
              ·
                refine ⟨1980142066128863488220723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5280378843010302635255261 1980142066128863488220723)
                ·
                  refine ⟨2970213099193295232331085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980142066128863488220723 2970213099193295232331085)
                  ·
                    refine ⟨1113829912197485712124157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970213099193295232331085 1113829912197485712124157)
                    ·
                      refine ⟨417686217074057142046559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1113829912197485712124157 417686217074057142046559)
                      ·
                        rfl

theorem cell23_813441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_813441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813441 prefixEnd_813441 := by exact prefixLift 813441
  have htrace : WordTrace (prefixWord ++ tailWord_813441) baseStart_813441 baseEnd_813441 := by
    simpa [prefixWord, tailWord_813441, baseEnd_813441] using wordTrace_append hprefix tailTrace_813441
  have hstable : (prefixWord ++ tailWord_813441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813441).length < 2 ^ (prefixWord ++ tailWord_813441).sum := by decide
  have hdescent : baseEnd_813441 < baseStart_813441 := by decide
  rcases family_descends (prefixWord ++ tailWord_813441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813442 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_813442 : Nat := 118140960795 + 813442 * 2 ^ 59
def prefixEnd_813442 : Nat := 4983230072969 + 3 ^ 40 * 813442 * 2
def baseEnd_813442 : Nat := 417686730554711638134055

theorem tailTrace_813442 : CollatzResearch.WordTrace tailWord_813442 prefixEnd_813442 417686730554711638134055 := by
  unfold tailWord_813442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7417166779761508419584645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19779111412697355785559053 7417166779761508419584645)
  ·
    refine ⟨1390718771205282828672121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7417166779761508419584645 1390718771205282828672121)
    ·
      refine ⟨1043039078403962121504091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1390718771205282828672121 1043039078403962121504091)
      ·
        refine ⟨1564558617605943182256137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1043039078403962121504091 1564558617605943182256137)
        ·
          refine ⟨1173418963204457386692103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564558617605943182256137 1173418963204457386692103)
          ·
            refine ⟨1760128444806686080038155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173418963204457386692103 1760128444806686080038155)
            ·
              refine ⟨2640192667210029120057233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760128444806686080038155 2640192667210029120057233)
              ·
                refine ⟨1980144500407521840042925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2640192667210029120057233 1980144500407521840042925)
                ·
                  refine ⟨742554187652820690016097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1980144500407521840042925 742554187652820690016097)
                  ·
                    refine ⟨556915640739615517512073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 742554187652820690016097 556915640739615517512073)
                    ·
                      refine ⟨417686730554711638134055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556915640739615517512073 417686730554711638134055)
                      ·
                        rfl

theorem cell23_813442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_813442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813442 prefixEnd_813442 := by exact prefixLift 813442
  have htrace : WordTrace (prefixWord ++ tailWord_813442) baseStart_813442 baseEnd_813442 := by
    simpa [prefixWord, tailWord_813442, baseEnd_813442] using wordTrace_append hprefix tailTrace_813442
  have hstable : (prefixWord ++ tailWord_813442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813442).length < 2 ^ (prefixWord ++ tailWord_813442).sum := by decide
  have hdescent : baseEnd_813442 < baseStart_813442 := by decide
  rcases family_descends (prefixWord ++ tailWord_813442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813451 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 3, 3, 2]
def baseStart_813451 : Nat := 118140960795 + 813451 * 2 ^ 59
def prefixEnd_813451 : Nat := 4983230072969 + 3 ^ 40 * 813451 * 2
def baseEnd_813451 : Nat := 417691351880602102921513

theorem tailTrace_813451 : CollatzResearch.WordTrace tailWord_813451 prefixEnd_813451 417691351880602102921513 := by
  unfold tailWord_813451
  simp only [CollatzResearch.WordTrace]
  refine ⟨29668995376013428215416207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19779330250675618810277471 29668995376013428215416207)
  ·
    refine ⟨44503493064020142323124311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29668995376013428215416207 44503493064020142323124311)
    ·
      refine ⟨66755239596030213484686467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44503493064020142323124311 66755239596030213484686467)
      ·
        refine ⟨100132859394045320227029701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66755239596030213484686467 100132859394045320227029701)
        ·
          refine ⟨18774911136383497542568069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100132859394045320227029701 18774911136383497542568069)
          ·
            refine ⟨3520295838071905789231513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18774911136383497542568069 3520295838071905789231513)
            ·
              refine ⟨2640221878553929341923635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3520295838071905789231513 2640221878553929341923635)
              ·
                refine ⟨3960332817830894012885453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640221878553929341923635 3960332817830894012885453)
                ·
                  refine ⟨1485124806686585254832045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3960332817830894012885453 1485124806686585254832045)
                  ·
                    refine ⟨556921802507469470562017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1485124806686585254832045 556921802507469470562017)
                    ·
                      refine ⟨417691351880602102921513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556921802507469470562017 417691351880602102921513)
                      ·
                        rfl

theorem cell23_813451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 3, 2].length) (baseStart_813451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813451 prefixEnd_813451 := by exact prefixLift 813451
  have htrace : WordTrace (prefixWord ++ tailWord_813451) baseStart_813451 baseEnd_813451 := by
    simpa [prefixWord, tailWord_813451, baseEnd_813451] using wordTrace_append hprefix tailTrace_813451
  have hstable : (prefixWord ++ tailWord_813451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813451).length < 2 ^ (prefixWord ++ tailWord_813451).sum := by decide
  have hdescent : baseEnd_813451 < baseStart_813451 := by decide
  rcases family_descends (prefixWord ++ tailWord_813451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813457 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 6, 6]
def baseStart_813457 : Nat := 118140960795 + 813457 * 2 ^ 59
def prefixEnd_813457 : Nat := 4983230072969 + 3 ^ 40 * 813457 * 2
def baseEnd_813457 : Nat := 139231477588176359815495

theorem tailTrace_813457 : CollatzResearch.WordTrace tailWord_813457 prefixEnd_813457 139231477588176359815495 := by
  unfold tailWord_813457
  simp only [CollatzResearch.WordTrace]
  refine ⟨29669214213991691240134625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19779476142661127493423083 29669214213991691240134625)
  ·
    refine ⟨22251910660493768430100969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29669214213991691240134625 22251910660493768430100969)
    ·
      refine ⟨16688932995370326322575727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22251910660493768430100969 16688932995370326322575727)
      ·
        refine ⟨25033399493055489483863591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16688932995370326322575727 25033399493055489483863591)
        ·
          refine ⟨37550099239583234225795387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25033399493055489483863591 37550099239583234225795387)
          ·
            refine ⟨56325148859374851338693081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37550099239583234225795387 56325148859374851338693081)
            ·
              refine ⟨42243861644531138504019811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56325148859374851338693081 42243861644531138504019811)
              ·
                refine ⟨63365792466796707756029717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42243861644531138504019811 63365792466796707756029717)
                ·
                  refine ⟨2970271521881095676063893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63365792466796707756029717 2970271521881095676063893)
                  ·
                    refine ⟨139231477588176359815495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2970271521881095676063893 139231477588176359815495)
                    ·
                      rfl

theorem cell23_813457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_813457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813457 prefixEnd_813457 := by exact prefixLift 813457
  have htrace : WordTrace (prefixWord ++ tailWord_813457) baseStart_813457 baseEnd_813457 := by
    simpa [prefixWord, tailWord_813457, baseEnd_813457] using wordTrace_append hprefix tailTrace_813457
  have hstable : (prefixWord ++ tailWord_813457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813457).length < 2 ^ (prefixWord ++ tailWord_813457).sum := by decide
  have hdescent : baseEnd_813457 < baseStart_813457 := by decide
  rcases family_descends (prefixWord ++ tailWord_813457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813474 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_813474 : Nat := 118140960795 + 813474 * 2 ^ 59
def prefixEnd_813474 : Nat := 4983230072969 + 3 ^ 40 * 813474 * 2
def baseEnd_813474 : Nat := 139234387311885170977969

theorem tailTrace_813474 : CollatzResearch.WordTrace tailWord_813474 prefixEnd_813474 139234387311885170977969 := by
  unfold tailWord_813474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7417458563732525785875869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19779889503286735429002317 7417458563732525785875869)
  ·
    refine ⟨2781546961399697169703451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7417458563732525785875869 2781546961399697169703451)
    ·
      refine ⟨4172320442099545754555177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2781546961399697169703451 4172320442099545754555177)
      ·
        refine ⟨3129240331574659315916383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4172320442099545754555177 3129240331574659315916383)
        ·
          refine ⟨4693860497361988973874575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3129240331574659315916383 4693860497361988973874575)
          ·
            refine ⟨7040790746042983460811863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4693860497361988973874575 7040790746042983460811863)
            ·
              refine ⟨10561186119064475191217795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7040790746042983460811863 10561186119064475191217795)
              ·
                refine ⟨15841779178596712786826693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10561186119064475191217795 15841779178596712786826693)
                ·
                  refine ⟨2970333595986883647530005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15841779178596712786826693 2970333595986883647530005)
                  ·
                    refine ⟨139234387311885170977969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2970333595986883647530005 139234387311885170977969)
                    ·
                      rfl

theorem cell23_813474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_813474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813474 prefixEnd_813474 := by exact prefixLift 813474
  have htrace : WordTrace (prefixWord ++ tailWord_813474) baseStart_813474 baseEnd_813474 := by
    simpa [prefixWord, tailWord_813474, baseEnd_813474] using wordTrace_append hprefix tailTrace_813474
  have hstable : (prefixWord ++ tailWord_813474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813474).length < 2 ^ (prefixWord ++ tailWord_813474).sum := by decide
  have hdescent : baseEnd_813474 < baseStart_813474 := by decide
  rcases family_descends (prefixWord ++ tailWord_813474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813492 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_813492 : Nat := 118140960795 + 813492 * 2 ^ 59
def prefixEnd_813492 : Nat := 4983230072969 + 3 ^ 40 * 813492 * 2
def baseEnd_813492 : Nat := 417712404587436442508825

theorem tailTrace_813492 : CollatzResearch.WordTrace tailWord_813492 prefixEnd_813492 417712404587436442508825 := by
  unfold tailWord_813492
  simp only [CollatzResearch.WordTrace]
  refine ⟨14835245384432446108829365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19780327179243261478439153 14835245384432446108829365)
  ·
    refine ⟨1390804254790541822702753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14835245384432446108829365 1390804254790541822702753)
    ·
      refine ⟨1043103191092906367027065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1390804254790541822702753 1043103191092906367027065)
      ·
        refine ⟨782327393319679775270299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1043103191092906367027065 782327393319679775270299)
        ·
          refine ⟨1173491089979519662905449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782327393319679775270299 1173491089979519662905449)
          ·
            refine ⟨880118317484639747179087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173491089979519662905449 880118317484639747179087)
            ·
              refine ⟨1320177476226959620768631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880118317484639747179087 1320177476226959620768631)
              ·
                refine ⟨1980266214340439431152947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320177476226959620768631 1980266214340439431152947)
                ·
                  refine ⟨2970399321510659146729421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980266214340439431152947 2970399321510659146729421)
                  ·
                    refine ⟨1113899745566497180023533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2970399321510659146729421 1113899745566497180023533)
                    ·
                      refine ⟨417712404587436442508825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1113899745566497180023533 417712404587436442508825)
                      ·
                        rfl

theorem cell23_813492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_813492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813492 prefixEnd_813492 := by exact prefixLift 813492
  have htrace : WordTrace (prefixWord ++ tailWord_813492) baseStart_813492 baseEnd_813492 := by
    simpa [prefixWord, tailWord_813492, baseEnd_813492] using wordTrace_append hprefix tailTrace_813492
  have hstable : (prefixWord ++ tailWord_813492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813492).length < 2 ^ (prefixWord ++ tailWord_813492).sum := by decide
  have hdescent : baseEnd_813492 < baseStart_813492 := by decide
  rcases family_descends (prefixWord ++ tailWord_813492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813498 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2]
def baseStart_813498 : Nat := 118140960795 + 813498 * 2 ^ 59
def prefixEnd_813498 : Nat := 4983230072969 + 3 ^ 40 * 813498 * 2
def baseEnd_813498 : Nat := 417715485471363419033797

theorem tailTrace_813498 : CollatzResearch.WordTrace tailWord_813498 prefixEnd_813498 417715485471363419033797 := by
  unfold tailWord_813498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7417677401710788810594287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19780473071228770161584765 7417677401710788810594287)
  ·
    refine ⟨11126516102566183215891431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7417677401710788810594287 11126516102566183215891431)
    ·
      refine ⟨16689774153849274823837147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11126516102566183215891431 16689774153849274823837147)
      ·
        refine ⟨25034661230773912235755721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16689774153849274823837147 25034661230773912235755721)
        ·
          refine ⟨18775995923080434176816791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25034661230773912235755721 18775995923080434176816791)
          ·
            refine ⟨28163993884620651265225187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18775995923080434176816791 28163993884620651265225187)
            ·
              refine ⟨42245990826930976897837781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28163993884620651265225187 42245990826930976897837781)
              ·
                refine ⟨990140410006194771043073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42245990826930976897837781 990140410006194771043073)
                ·
                  refine ⟨742605307504646078282305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 990140410006194771043073 742605307504646078282305)
                  ·
                    refine ⟨556953980628484558711729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 742605307504646078282305 556953980628484558711729)
                    ·
                      refine ⟨417715485471363419033797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556953980628484558711729 417715485471363419033797)
                      ·
                        rfl

theorem cell23_813498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_813498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813498 prefixEnd_813498 := by exact prefixLift 813498
  have htrace : WordTrace (prefixWord ++ tailWord_813498) baseStart_813498 baseEnd_813498 := by
    simpa [prefixWord, tailWord_813498, baseEnd_813498] using wordTrace_append hprefix tailTrace_813498
  have hstable : (prefixWord ++ tailWord_813498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813498).length < 2 ^ (prefixWord ++ tailWord_813498).sum := by decide
  have hdescent : baseEnd_813498 < baseStart_813498 := by decide
  rcases family_descends (prefixWord ++ tailWord_813498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813544 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_813544 : Nat := 118140960795 + 813544 * 2 ^ 59
def prefixEnd_813544 : Nat := 4983230072969 + 3 ^ 40 * 813544 * 2
def baseEnd_813544 : Nat := 417739105581470239058585

theorem tailTrace_813544 : CollatzResearch.WordTrace tailWord_813544 prefixEnd_813544 417739105581470239058585 := by
  unfold tailWord_813544
  simp only [CollatzResearch.WordTrace]
  refine ⟨14836193682338252549275843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19781591576451003399034457 14836193682338252549275843)
  ·
    refine ⟨22254290523507378823913765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14836193682338252549275843 22254290523507378823913765)
    ·
      refine ⟨4172679473157633529483831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22254290523507378823913765 4172679473157633529483831)
      ·
        refine ⟨6259019209736450294225747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4172679473157633529483831 6259019209736450294225747)
        ·
          refine ⟨9388528814604675441338621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6259019209736450294225747 9388528814604675441338621)
          ·
            refine ⟨3520698305476753290501983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9388528814604675441338621 3520698305476753290501983)
            ·
              refine ⟨5281047458215129935752975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520698305476753290501983 5281047458215129935752975)
              ·
                refine ⟨7921571187322694903629463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5281047458215129935752975 7921571187322694903629463)
                ·
                  refine ⟨11882356780984042355444195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7921571187322694903629463 11882356780984042355444195)
                  ·
                    refine ⟨17823535171476063533166293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11882356780984042355444195 17823535171476063533166293)
                    ·
                      refine ⟨417739105581470239058585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17823535171476063533166293 417739105581470239058585)
                      ·
                        rfl

theorem cell23_813544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_813544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813544 prefixEnd_813544 := by exact prefixLift 813544
  have htrace : WordTrace (prefixWord ++ tailWord_813544) baseStart_813544 baseEnd_813544 := by
    simpa [prefixWord, tailWord_813544, baseEnd_813544] using wordTrace_append hprefix tailTrace_813544
  have hstable : (prefixWord ++ tailWord_813544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813544).length < 2 ^ (prefixWord ++ tailWord_813544).sum := by decide
  have hdescent : baseEnd_813544 < baseStart_813544 := by decide
  rcases family_descends (prefixWord ++ tailWord_813544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813549 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_813549 : Nat := 118140960795 + 813549 * 2 ^ 59
def prefixEnd_813549 : Nat := 4983230072969 + 3 ^ 40 * 813549 * 2
def baseEnd_813549 : Nat := 417741672984742719496063

theorem tailTrace_813549 : CollatzResearch.WordTrace tailWord_813549 prefixEnd_813549 417741672984742719496063 := by
  unfold tailWord_813549
  simp only [CollatzResearch.WordTrace]
  refine ⟨29672569729658390952483701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19781713153105593968322467 29672569729658390952483701)
  ·
    refine ⟨2781803412155474151795347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29672569729658390952483701 2781803412155474151795347)
    ·
      refine ⟨4172705118233211227693021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2781803412155474151795347 4172705118233211227693021)
      ·
        refine ⟨1564764419337454210384883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4172705118233211227693021 1564764419337454210384883)
        ·
          refine ⟨2347146629006181315577325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564764419337454210384883 2347146629006181315577325)
          ·
            refine ⟨880179985877317993341497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2347146629006181315577325 880179985877317993341497)
            ·
              refine ⟨660134989407988495006123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880179985877317993341497 660134989407988495006123)
              ·
                refine ⟨990202484111982742509185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660134989407988495006123 990202484111982742509185)
                ·
                  refine ⟨742651863083987056881889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 990202484111982742509185 742651863083987056881889)
                  ·
                    refine ⟨556988897312990292661417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 742651863083987056881889 556988897312990292661417)
                    ·
                      refine ⟨417741672984742719496063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 556988897312990292661417 417741672984742719496063)
                      ·
                        rfl

theorem cell23_813549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_813549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813549 prefixEnd_813549 := by exact prefixLift 813549
  have htrace : WordTrace (prefixWord ++ tailWord_813549) baseStart_813549 baseEnd_813549 := by
    simpa [prefixWord, tailWord_813549, baseEnd_813549] using wordTrace_append hprefix tailTrace_813549
  have hstable : (prefixWord ++ tailWord_813549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813549).length < 2 ^ (prefixWord ++ tailWord_813549).sum := by decide
  have hdescent : baseEnd_813549 < baseStart_813549 := by decide
  rcases family_descends (prefixWord ++ tailWord_813549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813571 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 4]
def baseStart_813571 : Nat := 118140960795 + 813571 * 2 ^ 59
def prefixEnd_813571 : Nat := 4983230072969 + 3 ^ 40 * 813571 * 2
def baseEnd_813571 : Nat := 417752969559141633420961

theorem tailTrace_813571 : CollatzResearch.WordTrace tailWord_813571 prefixEnd_813571 417752969559141633420961 := by
  unfold tailWord_813571
  simp only [CollatzResearch.WordTrace]
  refine ⟨29673372135578688709784567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19782248090385792473189711 29673372135578688709784567)
  ·
    refine ⟨44510058203368033064676851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29673372135578688709784567 44510058203368033064676851)
    ·
      refine ⟨66765087305052049597015277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44510058203368033064676851 66765087305052049597015277)
      ·
        refine ⟨25036907739394518598880729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66765087305052049597015277 25036907739394518598880729)
        ·
          refine ⟨18777680804545888949160547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25036907739394518598880729 18777680804545888949160547)
          ·
            refine ⟨28166521206818833423740821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18777680804545888949160547 28166521206818833423740821)
            ·
              refine ⟨1320305681569632816737851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28166521206818833423740821 1320305681569632816737851)
              ·
                refine ⟨1980458522354449225106777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320305681569632816737851 1980458522354449225106777)
                ·
                  refine ⟨1485343891765836918830083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1980458522354449225106777 1485343891765836918830083)
                  ·
                    refine ⟨2228015837648755378245125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1485343891765836918830083 2228015837648755378245125)
                    ·
                      refine ⟨417752969559141633420961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2228015837648755378245125 417752969559141633420961)
                      ·
                        rfl

theorem cell23_813571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_813571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813571 prefixEnd_813571 := by exact prefixLift 813571
  have htrace : WordTrace (prefixWord ++ tailWord_813571) baseStart_813571 baseEnd_813571 := by
    simpa [prefixWord, tailWord_813571, baseEnd_813571] using wordTrace_append hprefix tailTrace_813571
  have hstable : (prefixWord ++ tailWord_813571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813571).length < 2 ^ (prefixWord ++ tailWord_813571).sum := by decide
  have hdescent : baseEnd_813571 < baseStart_813571 := by decide
  rcases family_descends (prefixWord ++ tailWord_813571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813594 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 8]
def baseStart_813594 : Nat := 118140960795 + 813594 * 2 ^ 59
def prefixEnd_813594 : Nat := 4983230072969 + 3 ^ 40 * 813594 * 2
def baseEnd_813594 : Nat := 46418308846021671492595

theorem tailTrace_813594 : CollatzResearch.WordTrace tailWord_813594 prefixEnd_813594 46418308846021671492595 := by
  unfold tailWord_813594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7418552753623840909467959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19782807342996909091914557 7418552753623840909467959)
  ·
    refine ⟨11127829130435761364201939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7418552753623840909467959 11127829130435761364201939)
    ·
      refine ⟨16691743695653642046302909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11127829130435761364201939 16691743695653642046302909)
      ·
        refine ⟨6259403885870115767363591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16691743695653642046302909 6259403885870115767363591)
        ·
          refine ⟨9389105828805173651045387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6259403885870115767363591 9389105828805173651045387)
          ·
            refine ⟨14083658743207760476568081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9389105828805173651045387 14083658743207760476568081)
            ·
              refine ⟨10562744057405820357426061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14083658743207760476568081 10562744057405820357426061)
              ·
                refine ⟨3961029021527182634034773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10562744057405820357426061 3961029021527182634034773)
                ·
                  refine ⟨46418308846021671492595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3961029021527182634034773 46418308846021671492595)
                  ·
                    rfl

theorem cell23_813594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_813594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813594 prefixEnd_813594 := by exact prefixLift 813594
  have htrace : WordTrace (prefixWord ++ tailWord_813594) baseStart_813594 baseEnd_813594 := by
    simpa [prefixWord, tailWord_813594, baseEnd_813594] using wordTrace_append hprefix tailTrace_813594
  have hstable : (prefixWord ++ tailWord_813594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813594).length < 2 ^ (prefixWord ++ tailWord_813594).sum := by decide
  have hdescent : baseEnd_813594 < baseStart_813594 := by decide
  rcases family_descends (prefixWord ++ tailWord_813594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813645 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 6]
def baseStart_813645 : Nat := 118140960795 + 813645 * 2 ^ 59
def prefixEnd_813645 : Nat := 4983230072969 + 3 ^ 40 * 813645 * 2
def baseEnd_813645 : Nat := 46421218569730482655069

theorem tailTrace_813645 : CollatzResearch.WordTrace tailWord_813645 prefixEnd_813645 46421218569730482655069 := by
  unfold tailWord_813645
  simp only [CollatzResearch.WordTrace]
  refine ⟨29676071137310599347978389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19784047424873732898652259 29676071137310599347978389)
  ·
    refine ⟨1391065834561434344436487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29676071137310599347978389 1391065834561434344436487)
    ·
      refine ⟨2086598751842151516654731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391065834561434344436487 2086598751842151516654731)
      ·
        refine ⟨3129898127763227274982097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2086598751842151516654731 3129898127763227274982097)
        ·
          refine ⟨2347423595822420456236573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3129898127763227274982097 2347423595822420456236573)
          ·
            refine ⟨880283848433407671088715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2347423595822420456236573 880283848433407671088715)
            ·
              refine ⟨1320425772650111506633073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880283848433407671088715 1320425772650111506633073)
              ·
                refine ⟨990319329487583629974805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320425772650111506633073 990319329487583629974805)
                ·
                  refine ⟨46421218569730482655069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 990319329487583629974805 46421218569730482655069)
                  ·
                    rfl

theorem cell23_813645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_813645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813645 prefixEnd_813645 := by exact prefixLift 813645
  have htrace : WordTrace (prefixWord ++ tailWord_813645) baseStart_813645 baseEnd_813645 := by
    simpa [prefixWord, tailWord_813645, baseEnd_813645] using wordTrace_append hprefix tailTrace_813645
  have hstable : (prefixWord ++ tailWord_813645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813645).length < 2 ^ (prefixWord ++ tailWord_813645).sum := by decide
  have hdescent : baseEnd_813645 < baseStart_813645 := by decide
  rcases family_descends (prefixWord ++ tailWord_813645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813655 : List Nat := [1, 1, 3, 2, 2, 2, 1, 6, 1, 1, 3]
def baseStart_813655 : Nat := 118140960795 + 813655 * 2 ^ 59
def prefixEnd_813655 : Nat := 4983230072969 + 3 ^ 40 * 813655 * 2
def baseEnd_813655 : Nat := 417796101934119304770575

theorem tailTrace_813655 : CollatzResearch.WordTrace tailWord_813655 prefixEnd_813655 417796101934119304770575 := by
  unfold tailWord_813655
  simp only [CollatzResearch.WordTrace]
  refine ⟨29676435867274371055842419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19784290578182914037228279 29676435867274371055842419)
  ·
    refine ⟨44514653800911556583763629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29676435867274371055842419 44514653800911556583763629)
    ·
      refine ⟨16692995175341833718911361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44514653800911556583763629 16692995175341833718911361)
      ·
        refine ⟨12519746381506375289183521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16692995175341833718911361 12519746381506375289183521)
        ·
          refine ⟨9389809786129781466887641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12519746381506375289183521 9389809786129781466887641)
          ·
            refine ⟨7042357339597336100165731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9389809786129781466887641 7042357339597336100165731)
            ·
              refine ⟨10563536009396004150248597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042357339597336100165731 10563536009396004150248597)
              ·
                refine ⟨495165750440437694542903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10563536009396004150248597 495165750440437694542903)
                ·
                  refine ⟨742748625660656541814355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495165750440437694542903 742748625660656541814355)
                  ·
                    refine ⟨1114122938490984812721533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 742748625660656541814355 1114122938490984812721533)
                    ·
                      refine ⟨417796101934119304770575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1114122938490984812721533 417796101934119304770575)
                      ·
                        rfl

theorem cell23_813655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_813655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813655 prefixEnd_813655 := by exact prefixLift 813655
  have htrace : WordTrace (prefixWord ++ tailWord_813655) baseStart_813655 baseEnd_813655 := by
    simpa [prefixWord, tailWord_813655, baseEnd_813655] using wordTrace_append hprefix tailTrace_813655
  have hstable : (prefixWord ++ tailWord_813655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813655).length < 2 ^ (prefixWord ++ tailWord_813655).sum := by decide
  have hdescent : baseEnd_813655 < baseStart_813655 := by decide
  rcases family_descends (prefixWord ++ tailWord_813655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813701 : List Nat := [1, 3, 1, 1, 4, 4, 9]
def baseStart_813701 : Nat := 118140960795 + 813701 * 2 ^ 59
def prefixEnd_813701 : Nat := 4983230072969 + 3 ^ 40 * 813701 * 2
def baseEnd_813701 : Nat := 5158268173385507713523

theorem tailTrace_813701 : CollatzResearch.WordTrace tailWord_813701 prefixEnd_813701 5158268173385507713523 := by
  unfold tailWord_813701
  simp only [CollatzResearch.WordTrace]
  refine ⟨29678113625107720912016957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19785409083405147274677971 29678113625107720912016957)
  ·
    refine ⟨11129292609415395342006359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29678113625107720912016957 11129292609415395342006359)
    ·
      refine ⟨16693938914123093013009539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11129292609415395342006359 16693938914123093013009539)
      ·
        refine ⟨25040908371184639519514309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16693938914123093013009539 25040908371184639519514309)
        ·
          refine ⟨4695170319597119909908933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25040908371184639519514309 4695170319597119909908933)
          ·
            refine ⟨880344434924459983107925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4695170319597119909908933 880344434924459983107925)
            ·
              refine ⟨5158268173385507713523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 880344434924459983107925 5158268173385507713523)
              ·
                rfl

theorem cell23_813701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 9].length) (baseStart_813701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813701 prefixEnd_813701 := by exact prefixLift 813701
  have htrace : WordTrace (prefixWord ++ tailWord_813701) baseStart_813701 baseEnd_813701 := by
    simpa [prefixWord, tailWord_813701, baseEnd_813701] using wordTrace_append hprefix tailTrace_813701
  have hstable : (prefixWord ++ tailWord_813701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813701).length < 2 ^ (prefixWord ++ tailWord_813701).sum := by decide
  have hdescent : baseEnd_813701 < baseStart_813701 := by decide
  rcases family_descends (prefixWord ++ tailWord_813701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813711 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 3]
def baseStart_813711 : Nat := 118140960795 + 813711 * 2 ^ 59
def prefixEnd_813711 : Nat := 4983230072969 + 3 ^ 40 * 813711 * 2
def baseEnd_813711 : Nat := 417824856850771085670317

theorem tailTrace_813711 : CollatzResearch.WordTrace tailWord_813711 prefixEnd_813711 417824856850771085670317 := by
  unfold tailWord_813711
  simp only [CollatzResearch.WordTrace]
  refine ⟨29678478355071492619880987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19785652236714328413253991 29678478355071492619880987)
  ·
    refine ⟨44517717532607238929821481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29678478355071492619880987 44517717532607238929821481)
    ·
      refine ⟨33388288149455429197366111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44517717532607238929821481 33388288149455429197366111)
      ·
        refine ⟨50082432224183143796049167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33388288149455429197366111 50082432224183143796049167)
        ·
          refine ⟨75123648336274715694073751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50082432224183143796049167 75123648336274715694073751)
          ·
            refine ⟨112685472504412073541110627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75123648336274715694073751 112685472504412073541110627)
            ·
              refine ⟨169028208756618110311665941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112685472504412073541110627 169028208756618110311665941)
              ·
                refine ⟨7923197285466473920859341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 169028208756618110311665941 7923197285466473920859341)
                ·
                  refine ⟨2971198982049927720322253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7923197285466473920859341 2971198982049927720322253)
                  ·
                    refine ⟨1114199618268722895120845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971198982049927720322253 1114199618268722895120845)
                    ·
                      refine ⟨417824856850771085670317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1114199618268722895120845 417824856850771085670317)
                      ·
                        rfl

theorem cell23_813711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 3].length) (baseStart_813711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813711 prefixEnd_813711 := by exact prefixLift 813711
  have htrace : WordTrace (prefixWord ++ tailWord_813711) baseStart_813711 baseEnd_813711 := by
    simpa [prefixWord, tailWord_813711, baseEnd_813711] using wordTrace_append hprefix tailTrace_813711
  have hstable : (prefixWord ++ tailWord_813711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813711).length < 2 ^ (prefixWord ++ tailWord_813711).sum := by decide
  have hdescent : baseEnd_813711 < baseStart_813711 := by decide
  rcases family_descends (prefixWord ++ tailWord_813711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813722 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_813722 : Nat := 118140960795 + 813722 * 2 ^ 59
def prefixEnd_813722 : Nat := 4983230072969 + 3 ^ 40 * 813722 * 2
def baseEnd_813722 : Nat := 139276835045990180877589

theorem tailTrace_813722 : CollatzResearch.WordTrace tailWord_813722 prefixEnd_813722 139276835045990180877589 := by
  unfold tailWord_813722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7419719889507910374632855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19785919705354427665687613 7419719889507910374632855)
  ·
    refine ⟨11129579834261865561949283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7419719889507910374632855 11129579834261865561949283)
    ·
      refine ⟨16694369751392798342923925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11129579834261865561949283 16694369751392798342923925)
      ·
        refine ⟨782548582096537422324559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16694369751392798342923925 782548582096537422324559)
        ·
          refine ⟨1173822873144806133486839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782548582096537422324559 1173822873144806133486839)
          ·
            refine ⟨1760734309717209200230259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173822873144806133486839 1760734309717209200230259)
            ·
              refine ⟨2641101464575813800345389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760734309717209200230259 2641101464575813800345389)
              ·
                refine ⟨990413049215930175129521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2641101464575813800345389 990413049215930175129521)
                ·
                  refine ⟨742809786911947631347141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 990413049215930175129521 742809786911947631347141)
                  ·
                    refine ⟨139276835045990180877589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 742809786911947631347141 139276835045990180877589)
                    ·
                      rfl

theorem cell23_813722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_813722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813722 prefixEnd_813722 := by exact prefixLift 813722
  have htrace : WordTrace (prefixWord ++ tailWord_813722) baseStart_813722 baseEnd_813722 := by
    simpa [prefixWord, tailWord_813722, baseEnd_813722] using wordTrace_append hprefix tailTrace_813722
  have hstable : (prefixWord ++ tailWord_813722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813722).length < 2 ^ (prefixWord ++ tailWord_813722).sum := by decide
  have hdescent : baseEnd_813722 < baseStart_813722 := by decide
  rcases family_descends (prefixWord ++ tailWord_813722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813785 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 1, 4, 2]
def baseStart_813785 : Nat := 118140960795 + 813785 * 2 ^ 59
def prefixEnd_813785 : Nat := 4983230072969 + 3 ^ 40 * 813785 * 2
def baseEnd_813785 : Nat := 417862854419203796144977

theorem tailTrace_813785 : CollatzResearch.WordTrace tailWord_813785 prefixEnd_813785 417862854419203796144977 := by
  unfold tailWord_813785
  simp only [CollatzResearch.WordTrace]
  refine ⟨29681177356803403258074809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19787451571202268838716539 29681177356803403258074809)
  ·
    refine ⟨22260883017602552443556107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29681177356803403258074809 22260883017602552443556107)
    ·
      refine ⟨33391324526403828665334161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22260883017602552443556107 33391324526403828665334161)
      ·
        refine ⟨25043493394802871499000621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33391324526403828665334161 25043493394802871499000621)
        ·
          refine ⟨9391310023051076812125233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25043493394802871499000621 9391310023051076812125233)
          ·
            refine ⟨7043482517288307609093925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9391310023051076812125233 7043482517288307609093925)
            ·
              refine ⟨1320652971991557676705111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7043482517288307609093925 1320652971991557676705111)
              ·
                refine ⟨1980979457987336515057667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320652971991557676705111 1980979457987336515057667)
                ·
                  refine ⟨2971469186981004772586501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980979457987336515057667 2971469186981004772586501)
                  ·
                    refine ⟨557150472558938394859969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2971469186981004772586501 557150472558938394859969)
                    ·
                      refine ⟨417862854419203796144977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 557150472558938394859969 417862854419203796144977)
                      ·
                        rfl

theorem cell23_813785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_813785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813785 prefixEnd_813785 := by exact prefixLift 813785
  have htrace : WordTrace (prefixWord ++ tailWord_813785) baseStart_813785 baseEnd_813785 := by
    simpa [prefixWord, tailWord_813785, baseEnd_813785] using wordTrace_append hprefix tailTrace_813785
  have hstable : (prefixWord ++ tailWord_813785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813785).length < 2 ^ (prefixWord ++ tailWord_813785).sum := by decide
  have hdescent : baseEnd_813785 < baseStart_813785 := by decide
  rcases family_descends (prefixWord ++ tailWord_813785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813791 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 9]
def baseStart_813791 : Nat := 118140960795 + 813791 * 2 ^ 59
def prefixEnd_813791 : Nat := 4983230072969 + 3 ^ 40 * 813791 * 2
def baseEnd_813791 : Nat := 46429548367014530296661

theorem tailTrace_813791 : CollatzResearch.WordTrace tailWord_813791 prefixEnd_813791 46429548367014530296661 := by
  unfold tailWord_813791
  simp only [CollatzResearch.WordTrace]
  refine ⟨29681396194781666282793227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19787597463187777521862151 29681396194781666282793227)
  ·
    refine ⟨44522094292172499424189841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29681396194781666282793227 44522094292172499424189841)
    ·
      refine ⟨33391570719129374568142381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44522094292172499424189841 33391570719129374568142381)
      ·
        refine ⟨12521839019673515463053393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33391570719129374568142381 12521839019673515463053393)
        ·
          refine ⟨9391379264755136597290045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12521839019673515463053393 9391379264755136597290045)
          ·
            refine ⟨3521767224283176223983767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9391379264755136597290045 3521767224283176223983767)
            ·
              refine ⟨5282650836424764335975651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521767224283176223983767 5282650836424764335975651)
              ·
                refine ⟨7923976254637146503963477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5282650836424764335975651 7923976254637146503963477)
                ·
                  refine ⟨46429548367014530296661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7923976254637146503963477 46429548367014530296661)
                  ·
                    rfl

theorem cell23_813791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 9].length) (baseStart_813791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813791 prefixEnd_813791 := by exact prefixLift 813791
  have htrace : WordTrace (prefixWord ++ tailWord_813791) baseStart_813791 baseEnd_813791 := by
    simpa [prefixWord, tailWord_813791, baseEnd_813791] using wordTrace_append hprefix tailTrace_813791
  have hstable : (prefixWord ++ tailWord_813791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813791).length < 2 ^ (prefixWord ++ tailWord_813791).sum := by decide
  have hdescent : baseEnd_813791 < baseStart_813791 := by decide
  rcases family_descends (prefixWord ++ tailWord_813791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813813 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_813813 : Nat := 118140960795 + 813813 * 2 ^ 59
def prefixEnd_813813 : Nat := 4983230072969 + 3 ^ 40 * 813813 * 2
def baseEnd_813813 : Nat := 417877231877529686594849

theorem tailTrace_813813 : CollatzResearch.WordTrace tailWord_813813 prefixEnd_813813 417877231877529686594849 := by
  unfold tailWord_813813
  simp only [CollatzResearch.WordTrace]
  refine ⟨29682198600701964040094093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19788132400467976026729395 29682198600701964040094093)
  ·
    refine ⟨11130824475263236515035285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29682198600701964040094093 11130824475263236515035285)
    ·
      refine ⟨521757397277964211642279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11130824475263236515035285 521757397277964211642279)
      ·
        refine ⟨782636095916946317463419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521757397277964211642279 782636095916946317463419)
        ·
          refine ⟨1173954143875419476195129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782636095916946317463419 1173954143875419476195129)
          ·
            refine ⟨880465607906564607146347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173954143875419476195129 880465607906564607146347)
            ·
              refine ⟨1320698411859846910719521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880465607906564607146347 1320698411859846910719521)
              ·
                refine ⟨990523808894885183039641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320698411859846910719521 990523808894885183039641)
                ·
                  refine ⟨742892856671163887279731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 990523808894885183039641 742892856671163887279731)
                  ·
                    refine ⟨1114339285006745830919597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 742892856671163887279731 1114339285006745830919597)
                    ·
                      refine ⟨417877231877529686594849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1114339285006745830919597 417877231877529686594849)
                      ·
                        rfl

theorem cell23_813813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_813813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813813 prefixEnd_813813 := by exact prefixLift 813813
  have htrace : WordTrace (prefixWord ++ tailWord_813813) baseStart_813813 baseEnd_813813 := by
    simpa [prefixWord, tailWord_813813, baseEnd_813813] using wordTrace_append hprefix tailTrace_813813
  have hstable : (prefixWord ++ tailWord_813813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813813).length < 2 ^ (prefixWord ++ tailWord_813813).sum := by decide
  have hdescent : baseEnd_813813 < baseStart_813813 := by decide
  rcases family_descends (prefixWord ++ tailWord_813813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813818 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3]
def baseStart_813818 : Nat := 118140960795 + 813818 * 2 ^ 59
def prefixEnd_813818 : Nat := 4983230072969 + 3 ^ 40 * 813818 * 2
def baseEnd_813818 : Nat := 417879799280802167032325

theorem tailTrace_813818 : CollatzResearch.WordTrace tailWord_813818 prefixEnd_813818 417879799280802167032325 := by
  unfold tailWord_813818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7420595241420962473506527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19788253977122566596017405 7420595241420962473506527)
  ·
    refine ⟨11130892862131443710259791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7420595241420962473506527 11130892862131443710259791)
    ·
      refine ⟨16696339293197165565389687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11130892862131443710259791 16696339293197165565389687)
      ·
        refine ⟨25044508939795748348084531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16696339293197165565389687 25044508939795748348084531)
        ·
          refine ⟨37566763409693622522126797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25044508939795748348084531 37566763409693622522126797)
          ·
            refine ⟨14087536278635108445797549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37566763409693622522126797 14087536278635108445797549)
            ·
              refine ⟨5282826104488165667174081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14087536278635108445797549 5282826104488165667174081)
              ·
                refine ⟨3962119578366124250380561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5282826104488165667174081 3962119578366124250380561)
                ·
                  refine ⟨2971589683774593187785421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3962119578366124250380561 2971589683774593187785421)
                  ·
                    refine ⟨1114346131415472445419533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2971589683774593187785421 1114346131415472445419533)
                    ·
                      refine ⟨417879799280802167032325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1114346131415472445419533 417879799280802167032325)
                      ·
                        rfl

theorem cell23_813818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_813818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813818 prefixEnd_813818 := by exact prefixLift 813818
  have htrace : WordTrace (prefixWord ++ tailWord_813818) baseStart_813818 baseEnd_813818 := by
    simpa [prefixWord, tailWord_813818, baseEnd_813818] using wordTrace_append hprefix tailTrace_813818
  have hstable : (prefixWord ++ tailWord_813818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813818).length < 2 ^ (prefixWord ++ tailWord_813818).sum := by decide
  have hdescent : baseEnd_813818 < baseStart_813818 := by decide
  rcases family_descends (prefixWord ++ tailWord_813818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813875 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 4]
def baseStart_813875 : Nat := 118140960795 + 813875 * 2 ^ 59
def prefixEnd_813875 : Nat := 4983230072969 + 3 ^ 40 * 813875 * 2
def baseEnd_813875 : Nat := 417909067678108444019563

theorem tailTrace_813875 : CollatzResearch.WordTrace tailWord_813875 prefixEnd_813875 417909067678108444019563 := by
  unfold tailWord_813875
  simp only [CollatzResearch.WordTrace]
  refine ⟨29684459926477348628851079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19789639950984899085900719 29684459926477348628851079)
  ·
    refine ⟨44526689889716022943276619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29684459926477348628851079 44526689889716022943276619)
    ·
      refine ⟨66790034834574034414914929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44526689889716022943276619 66790034834574034414914929)
      ·
        refine ⟨50092526125930525811186197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66790034834574034414914929 50092526125930525811186197)
        ·
          refine ⟨2348087162152993397399353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50092526125930525811186197 2348087162152993397399353)
          ·
            refine ⟨1761065371614745048049515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2348087162152993397399353 1761065371614745048049515)
            ·
              refine ⟨2641598057422117572074273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761065371614745048049515 2641598057422117572074273)
              ·
                refine ⟨1981198543066588179055705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641598057422117572074273 1981198543066588179055705)
                ·
                  refine ⟨1485898907299941134291779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1981198543066588179055705 1485898907299941134291779)
                  ·
                    refine ⟨2228848360949911701437669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1485898907299941134291779 2228848360949911701437669)
                    ·
                      refine ⟨417909067678108444019563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2228848360949911701437669 417909067678108444019563)
                      ·
                        rfl

theorem cell23_813875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_813875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813875 prefixEnd_813875 := by exact prefixLift 813875
  have htrace : WordTrace (prefixWord ++ tailWord_813875) baseStart_813875 baseEnd_813875 := by
    simpa [prefixWord, tailWord_813875, baseEnd_813875] using wordTrace_append hprefix tailTrace_813875
  have hstable : (prefixWord ++ tailWord_813875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813875).length < 2 ^ (prefixWord ++ tailWord_813875).sum := by decide
  have hdescent : baseEnd_813875 < baseStart_813875 := by decide
  rcases family_descends (prefixWord ++ tailWord_813875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813975 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 4, 4]
def baseStart_813975 : Nat := 118140960795 + 813975 * 2 ^ 59
def prefixEnd_813975 : Nat := 4983230072969 + 3 ^ 40 * 813975 * 2
def baseEnd_813975 : Nat := 139320138581186017589701

theorem tailTrace_813975 : CollatzResearch.WordTrace tailWord_813975 prefixEnd_813975 139320138581186017589701 := by
  unfold tailWord_813975
  simp only [CollatzResearch.WordTrace]
  refine ⟨29688107226115065707491379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19792071484076710471660919 29688107226115065707491379)
  ·
    refine ⟨44532160839172598561237069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29688107226115065707491379 44532160839172598561237069)
    ·
      refine ⟨16699560314689724460463901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44532160839172598561237069 16699560314689724460463901)
      ·
        refine ⟨6262335118008646672673963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16699560314689724460463901 6262335118008646672673963)
        ·
          refine ⟨9393502677012970009010945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6262335118008646672673963 9393502677012970009010945)
          ·
            refine ⟨7045127007759727506758209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9393502677012970009010945 7045127007759727506758209)
            ·
              refine ⟨5283845255819795630068657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7045127007759727506758209 5283845255819795630068657)
              ·
                refine ⟨3962883941864846722551493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5283845255819795630068657 3962883941864846722551493)
                ·
                  refine ⟨743040739099658760478405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3962883941864846722551493 743040739099658760478405)
                  ·
                    refine ⟨139320138581186017589701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 743040739099658760478405 139320138581186017589701)
                    ·
                      rfl

theorem cell23_813975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_813975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813975 prefixEnd_813975 := by exact prefixLift 813975
  have htrace : WordTrace (prefixWord ++ tailWord_813975) baseStart_813975 baseEnd_813975 := by
    simpa [prefixWord, tailWord_813975, baseEnd_813975] using wordTrace_append hprefix tailTrace_813975
  have hstable : (prefixWord ++ tailWord_813975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813975).length < 2 ^ (prefixWord ++ tailWord_813975).sum := by decide
  have hdescent : baseEnd_813975 < baseStart_813975 := by decide
  rcases family_descends (prefixWord ++ tailWord_813975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813988 : List Nat := [2, 3, 1, 2, 1, 2, 12]
def baseStart_813988 : Nat := 118140960795 + 813988 * 2 ^ 59
def prefixEnd_813988 : Nat := 4983230072969 + 3 ^ 40 * 813988 * 2
def baseEnd_813988 : Nat := 5160087543111932122303

theorem tailTrace_813988 : CollatzResearch.WordTrace tailWord_813988 prefixEnd_813988 5160087543111932122303 := by
  unfold tailWord_813988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14844290687533984463857309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19792387583378645951809745 14844290687533984463857309)
  ·
    refine ⟨5566609007825244173946491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14844290687533984463857309 5566609007825244173946491)
    ·
      refine ⟨8349913511737866260919737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5566609007825244173946491 8349913511737866260919737)
      ·
        refine ⟨6262435133803399695689803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8349913511737866260919737 6262435133803399695689803)
        ·
          refine ⟨9393652700705099543534705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6262435133803399695689803 9393652700705099543534705)
          ·
            refine ⟨7045239525528824657651029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9393652700705099543534705 7045239525528824657651029)
            ·
              refine ⟨5160087543111932122303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 7045239525528824657651029 5160087543111932122303)
              ·
                rfl

theorem cell23_813988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 12].length) (baseStart_813988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_813988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_813988 prefixEnd_813988 := by exact prefixLift 813988
  have htrace : WordTrace (prefixWord ++ tailWord_813988) baseStart_813988 baseEnd_813988 := by
    simpa [prefixWord, tailWord_813988, baseEnd_813988] using wordTrace_append hprefix tailTrace_813988
  have hstable : (prefixWord ++ tailWord_813988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813988).length < 2 ^ (prefixWord ++ tailWord_813988).sum := by decide
  have hdescent : baseEnd_813988 < baseStart_813988 := by decide
  rcases family_descends (prefixWord ++ tailWord_813988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814009 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 2, 4]
def baseStart_814009 : Nat := 118140960795 + 814009 * 2 ^ 59
def prefixEnd_814009 : Nat := 4983230072969 + 3 ^ 40 * 814009 * 2
def baseEnd_814009 : Nat := 139325958028603639914649

theorem tailTrace_814009 : CollatzResearch.WordTrace tailWord_814009 prefixEnd_814009 139325958028603639914649 := by
  unfold tailWord_814009
  simp only [CollatzResearch.WordTrace]
  refine ⟨29689347307991889514229081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19792898205327926342819387 29689347307991889514229081)
  ·
    refine ⟨22267010480993917135671811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29689347307991889514229081 22267010480993917135671811)
    ·
      refine ⟨33400515721490875703507717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22267010480993917135671811 33400515721490875703507717)
      ·
        refine ⟨6262596697779539194407697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33400515721490875703507717 6262596697779539194407697)
        ·
          refine ⟨4696947523334654395805773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6262596697779539194407697 4696947523334654395805773)
          ·
            refine ⟨1761355321250495398427165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4696947523334654395805773 1761355321250495398427165)
            ·
              refine ⟨660508245468935774410187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1761355321250495398427165 660508245468935774410187)
              ·
                refine ⟨990762368203403661615281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660508245468935774410187 990762368203403661615281)
                ·
                  refine ⟨743071776152552746211461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 990762368203403661615281 743071776152552746211461)
                  ·
                    refine ⟨139325958028603639914649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 743071776152552746211461 139325958028603639914649)
                    ·
                      rfl

theorem cell23_814009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 2, 4].length) (baseStart_814009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814009 prefixEnd_814009 := by exact prefixLift 814009
  have htrace : WordTrace (prefixWord ++ tailWord_814009) baseStart_814009 baseEnd_814009 := by
    simpa [prefixWord, tailWord_814009, baseEnd_814009] using wordTrace_append hprefix tailTrace_814009
  have hstable : (prefixWord ++ tailWord_814009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814009).length < 2 ^ (prefixWord ++ tailWord_814009).sum := by decide
  have hdescent : baseEnd_814009 < baseStart_814009 := by decide
  rcases family_descends (prefixWord ++ tailWord_814009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814015 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 3]
def baseStart_814015 : Nat := 118140960795 + 814015 * 2 ^ 59
def prefixEnd_814015 : Nat := 4983230072969 + 3 ^ 40 * 814015 * 2
def baseEnd_814015 : Nat := 417980954969737896268919

theorem tailTrace_814015 : CollatzResearch.WordTrace tailWord_814015 prefixEnd_814015 417980954969737896268919 := by
  unfold tailWord_814015
  simp only [CollatzResearch.WordTrace]
  refine ⟨29689566145970152538947499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19793044097313435025964999 29689566145970152538947499)
  ·
    refine ⟨44534349218955228808421249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29689566145970152538947499 44534349218955228808421249)
    ·
      refine ⟨33400761914216421606315937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44534349218955228808421249 33400761914216421606315937)
      ·
        refine ⟨25050571435662316204736953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33400761914216421606315937 25050571435662316204736953)
        ·
          refine ⟨18787928576746737153552715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25050571435662316204736953 18787928576746737153552715)
          ·
            refine ⟨28181892865120105730329073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18787928576746737153552715 28181892865120105730329073)
            ·
              refine ⟨21136419648840079297746805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28181892865120105730329073 21136419648840079297746805)
              ·
                refine ⟨1981539342078757434163763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21136419648840079297746805 1981539342078757434163763)
                ·
                  refine ⟨2972309013118136151245645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981539342078757434163763 2972309013118136151245645)
                  ·
                    refine ⟨1114615879919301056717117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2972309013118136151245645 1114615879919301056717117)
                    ·
                      refine ⟨417980954969737896268919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1114615879919301056717117 417980954969737896268919)
                      ·
                        rfl

theorem cell23_814015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_814015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814015 prefixEnd_814015 := by exact prefixLift 814015
  have htrace : WordTrace (prefixWord ++ tailWord_814015) baseStart_814015 baseEnd_814015 := by
    simpa [prefixWord, tailWord_814015, baseEnd_814015] using wordTrace_append hprefix tailTrace_814015
  have hstable : (prefixWord ++ tailWord_814015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814015).length < 2 ^ (prefixWord ++ tailWord_814015).sum := by decide
  have hdescent : baseEnd_814015 < baseStart_814015 := by decide
  rcases family_descends (prefixWord ++ tailWord_814015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814072 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 1, 4, 2]
def baseStart_814072 : Nat := 118140960795 + 814072 * 2 ^ 59
def prefixEnd_814072 : Nat := 4983230072969 + 3 ^ 40 * 814072 * 2
def baseEnd_814072 : Nat := 418010223367044173256157

theorem tailTrace_814072 : CollatzResearch.WordTrace tailWord_814072 prefixEnd_814072 418010223367044173256157 := by
  unfold tailWord_814072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14845822553381825636886235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19794430071175767515848313 14845822553381825636886235)
  ·
    refine ⟨22268733830072738455329353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14845822553381825636886235 22268733830072738455329353)
    ·
      refine ⟨16701550372554553841497015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22268733830072738455329353 16701550372554553841497015)
      ·
        refine ⟨25052325558831830762245523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16701550372554553841497015 25052325558831830762245523)
        ·
          refine ⟨37578488338247746143368285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25052325558831830762245523 37578488338247746143368285)
          ·
            refine ⟨14091933126842904803763107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37578488338247746143368285 14091933126842904803763107)
            ·
              refine ⟨21137899690264357205644661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14091933126842904803763107 21137899690264357205644661)
              ·
                refine ⟨1981678095962283488029187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21137899690264357205644661 1981678095962283488029187)
                ·
                  refine ⟨2972517143943425232043781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981678095962283488029187 2972517143943425232043781)
                  ·
                    refine ⟨557346964489392231008209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2972517143943425232043781 557346964489392231008209)
                    ·
                      refine ⟨418010223367044173256157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 557346964489392231008209 418010223367044173256157)
                      ·
                        rfl

theorem cell23_814072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_814072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814072 prefixEnd_814072 := by exact prefixLift 814072
  have htrace : WordTrace (prefixWord ++ tailWord_814072) baseStart_814072 baseEnd_814072 := by
    simpa [prefixWord, tailWord_814072, baseEnd_814072] using wordTrace_append hprefix tailTrace_814072
  have hstable : (prefixWord ++ tailWord_814072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814072).length < 2 ^ (prefixWord ++ tailWord_814072).sum := by decide
  have hdescent : baseEnd_814072 < baseStart_814072 := by decide
  rcases family_descends (prefixWord ++ tailWord_814072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814076 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 1, 3, 2]
def baseStart_814076 : Nat := 118140960795 + 814076 * 2 ^ 59
def prefixEnd_814076 : Nat := 4983230072969 + 3 ^ 40 * 814076 * 2
def baseEnd_814076 : Nat := 418012277289662157606139

theorem tailTrace_814076 : CollatzResearch.WordTrace tailWord_814076 prefixEnd_814076 418012277289662157606139 := by
  unfold tailWord_814076
  simp only [CollatzResearch.WordTrace]
  refine ⟨14845895499374579978459041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19794527332499439971278721 14845895499374579978459041)
  ·
    refine ⟨11134421624530934983844281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14845895499374579978459041 11134421624530934983844281)
    ·
      refine ⟨8350816218398201237883211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11134421624530934983844281 8350816218398201237883211)
      ·
        refine ⟨12526224327597301856824817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8350816218398201237883211 12526224327597301856824817)
        ·
          refine ⟨9394668245697976392618613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12526224327597301856824817 9394668245697976392618613)
          ·
            refine ⟨880750148034185286807995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9394668245697976392618613 880750148034185286807995)
            ·
              refine ⟨1321125222051277930211993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880750148034185286807995 1321125222051277930211993)
              ·
                refine ⟨990843916538458447658995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1321125222051277930211993 990843916538458447658995)
                ·
                  refine ⟨1486265874807687671488493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990843916538458447658995 1486265874807687671488493)
                  ·
                    refine ⟨557349703052882876808185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486265874807687671488493 557349703052882876808185)
                    ·
                      refine ⟨418012277289662157606139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 557349703052882876808185 418012277289662157606139)
                      ·
                        rfl

theorem cell23_814076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_814076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814076 prefixEnd_814076 := by exact prefixLift 814076
  have htrace : WordTrace (prefixWord ++ tailWord_814076) baseStart_814076 baseEnd_814076 := by
    simpa [prefixWord, tailWord_814076, baseEnd_814076] using wordTrace_append hprefix tailTrace_814076
  have hstable : (prefixWord ++ tailWord_814076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814076).length < 2 ^ (prefixWord ++ tailWord_814076).sum := by decide
  have hdescent : baseEnd_814076 < baseStart_814076 := by decide
  rcases family_descends (prefixWord ++ tailWord_814076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814106 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2]
def baseStart_814106 : Nat := 118140960795 + 814106 * 2 ^ 59
def prefixEnd_814106 : Nat := 4983230072969 + 3 ^ 40 * 814106 * 2
def baseEnd_814106 : Nat := 418027681709297040231001

theorem tailTrace_814106 : CollatzResearch.WordTrace tailWord_814106 prefixEnd_814106 418027681709297040231001 := by
  unfold tailWord_814106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7423221297160118770127543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19795256792426983387006781 7423221297160118770127543)
  ·
    refine ⟨11134831945740178155191315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7423221297160118770127543 11134831945740178155191315)
    ·
      refine ⟨16702247918610267232786973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11134831945740178155191315 16702247918610267232786973)
      ·
        refine ⟨6263342969478850212295115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16702247918610267232786973 6263342969478850212295115)
        ·
          refine ⟨9395014454218275318442673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6263342969478850212295115 9395014454218275318442673)
          ·
            refine ⟨7046260840663706488832005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9395014454218275318442673 7046260840663706488832005)
            ·
              refine ⟨1321173907624444966656001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7046260840663706488832005 1321173907624444966656001)
              ·
                refine ⟨990880430718333724992001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1321173907624444966656001 990880430718333724992001)
                ·
                  refine ⟨743160323038750293744001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 990880430718333724992001 743160323038750293744001)
                  ·
                    refine ⟨557370242279062720308001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 743160323038750293744001 557370242279062720308001)
                    ·
                      refine ⟨418027681709297040231001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 557370242279062720308001 418027681709297040231001)
                      ·
                        rfl

theorem cell23_814106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_814106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814106 prefixEnd_814106 := by exact prefixLift 814106
  have htrace : WordTrace (prefixWord ++ tailWord_814106) baseStart_814106 baseEnd_814106 := by
    simpa [prefixWord, tailWord_814106, baseEnd_814106] using wordTrace_append hprefix tailTrace_814106
  have hstable : (prefixWord ++ tailWord_814106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814106).length < 2 ^ (prefixWord ++ tailWord_814106).sum := by decide
  have hdescent : baseEnd_814106 < baseStart_814106 := by decide
  rcases family_descends (prefixWord ++ tailWord_814106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814119 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_814119 : Nat := 118140960795 + 814119 * 2 ^ 59
def prefixEnd_814119 : Nat := 4983230072969 + 3 ^ 40 * 814119 * 2
def baseEnd_814119 : Nat := 418034356957805489368441

theorem tailTrace_814119 : CollatzResearch.WordTrace tailWord_814119 prefixEnd_814119 418034356957805489368441 := by
  unfold tailWord_814119
  simp only [CollatzResearch.WordTrace]
  refine ⟨29693359337593378300733411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19795572891728918867155607 29693359337593378300733411)
  ·
    refine ⟨44540039006390067451100117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29693359337593378300733411 44540039006390067451100117)
    ·
      refine ⟨1043907164212267205885159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44540039006390067451100117 1043907164212267205885159)
      ·
        refine ⟨1565860746318400808827739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1043907164212267205885159 1565860746318400808827739)
        ·
          refine ⟨2348791119477601213241609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1565860746318400808827739 2348791119477601213241609)
          ·
            refine ⟨1761593339608200909931207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2348791119477601213241609 1761593339608200909931207)
            ·
              refine ⟨2642390009412301364896811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761593339608200909931207 2642390009412301364896811)
              ·
                refine ⟨3963585014118452047345217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642390009412301364896811 3963585014118452047345217)
                ·
                  refine ⟨2972688760588839035508913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3963585014118452047345217 2972688760588839035508913)
                  ·
                    refine ⟨2229516570441629276631685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2972688760588839035508913 2229516570441629276631685)
                    ·
                      refine ⟨418034356957805489368441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2229516570441629276631685 418034356957805489368441)
                      ·
                        rfl

theorem cell23_814119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_814119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814119 prefixEnd_814119 := by exact prefixLift 814119
  have htrace : WordTrace (prefixWord ++ tailWord_814119) baseStart_814119 baseEnd_814119 := by
    simpa [prefixWord, tailWord_814119, baseEnd_814119] using wordTrace_append hprefix tailTrace_814119
  have hstable : (prefixWord ++ tailWord_814119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814119).length < 2 ^ (prefixWord ++ tailWord_814119).sum := by decide
  have hdescent : baseEnd_814119 < baseStart_814119 := by decide
  rcases family_descends (prefixWord ++ tailWord_814119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814175 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_814175 : Nat := 118140960795 + 814175 * 2 ^ 59
def prefixEnd_814175 : Nat := 4983230072969 + 3 ^ 40 * 814175 * 2
def baseEnd_814175 : Nat := 418063111874457270268183

theorem tailTrace_814175 : CollatzResearch.WordTrace tailWord_814175 prefixEnd_814175 418063111874457270268183 := by
  unfold tailWord_814175
  simp only [CollatzResearch.WordTrace]
  refine ⟨29695401825390499864771979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19796934550260333243181319 29695401825390499864771979)
  ·
    refine ⟨44543102738085749797157969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29695401825390499864771979 44543102738085749797157969)
    ·
      refine ⟨33407327053564312347868477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44543102738085749797157969 33407327053564312347868477)
      ·
        refine ⟨12527747645086617130450679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33407327053564312347868477 12527747645086617130450679)
        ·
          refine ⟨18791621467629925695676019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12527747645086617130450679 18791621467629925695676019)
          ·
            refine ⟨28187432201444888543514029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18791621467629925695676019 28187432201444888543514029)
            ·
              refine ⟨10570287075541833203817761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28187432201444888543514029 10570287075541833203817761)
              ·
                refine ⟨7927715306656374902863321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10570287075541833203817761 7927715306656374902863321)
                ·
                  refine ⟨5945786479992281177147491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7927715306656374902863321 5945786479992281177147491)
                  ·
                    refine ⟨8918679719988421765721237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5945786479992281177147491 8918679719988421765721237)
                    ·
                      refine ⟨418063111874457270268183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8918679719988421765721237 418063111874457270268183)
                      ·
                        rfl

theorem cell23_814175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_814175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814175 prefixEnd_814175 := by exact prefixLift 814175
  have htrace : WordTrace (prefixWord ++ tailWord_814175) baseStart_814175 baseEnd_814175 := by
    simpa [prefixWord, tailWord_814175, baseEnd_814175] using wordTrace_append hprefix tailTrace_814175
  have hstable : (prefixWord ++ tailWord_814175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814175).length < 2 ^ (prefixWord ++ tailWord_814175).sum := by decide
  have hdescent : baseEnd_814175 < baseStart_814175 := by decide
  rcases family_descends (prefixWord ++ tailWord_814175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814189 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_814189 : Nat := 118140960795 + 814189 * 2 ^ 59
def prefixEnd_814189 : Nat := 4983230072969 + 3 ^ 40 * 814189 * 2
def baseEnd_814189 : Nat := 139356766867873405164373

theorem tailTrace_814189 : CollatzResearch.WordTrace tailWord_814189 prefixEnd_814189 139356766867873405164373 := by
  unfold tailWord_814189
  simp only [CollatzResearch.WordTrace]
  refine ⟨29695912447339780255781621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19797274964893186837187747 29695912447339780255781621)
  ·
    refine ⟨2783991791938104398979527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29695912447339780255781621 2783991791938104398979527)
    ·
      refine ⟨4175987687907156598469291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2783991791938104398979527 4175987687907156598469291)
      ·
        refine ⟨6263981531860734897703937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4175987687907156598469291 6263981531860734897703937)
        ·
          refine ⟨4697986148895551173277953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6263981531860734897703937 4697986148895551173277953)
          ·
            refine ⟨3523489611671663379958465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4697986148895551173277953 3523489611671663379958465)
            ·
              refine ⟨2642617208753747534968849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3523489611671663379958465 2642617208753747534968849)
              ·
                refine ⟨1981962906565310651226637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642617208753747534968849 1981962906565310651226637)
                ·
                  refine ⟨743236089961991494209989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1981962906565310651226637 743236089961991494209989)
                  ·
                    refine ⟨139356766867873405164373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 743236089961991494209989 139356766867873405164373)
                    ·
                      rfl

theorem cell23_814189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_814189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814189 prefixEnd_814189 := by exact prefixLift 814189
  have htrace : WordTrace (prefixWord ++ tailWord_814189) baseStart_814189 baseEnd_814189 := by
    simpa [prefixWord, tailWord_814189, baseEnd_814189] using wordTrace_append hprefix tailTrace_814189
  have hstable : (prefixWord ++ tailWord_814189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814189).length < 2 ^ (prefixWord ++ tailWord_814189).sum := by decide
  have hdescent : baseEnd_814189 < baseStart_814189 := by decide
  rcases family_descends (prefixWord ++ tailWord_814189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814216 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_814216 : Nat := 118140960795 + 814216 * 2 ^ 59
def prefixEnd_814216 : Nat := 4983230072969 + 3 ^ 40 * 814216 * 2
def baseEnd_814216 : Nat := 418084164581291609855495

theorem tailTrace_814216 : CollatzResearch.WordTrace tailWord_814216 prefixEnd_814216 418084164581291609855495 := by
  unfold tailWord_814216
  simp only [CollatzResearch.WordTrace]
  refine ⟨14848448609120981933507251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19797931478827975911343001 14848448609120981933507251)
  ·
    refine ⟨22272672913681472900260877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14848448609120981933507251 22272672913681472900260877)
    ·
      refine ⟨8352252342630552337597829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22272672913681472900260877 8352252342630552337597829)
      ·
        refine ⟨1566047314243228563299593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8352252342630552337597829 1566047314243228563299593)
        ·
          refine ⟨1174535485682421422474695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566047314243228563299593 1174535485682421422474695)
          ·
            refine ⟨1761803228523632133712043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174535485682421422474695 1761803228523632133712043)
            ·
              refine ⟨2642704842785448200568065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761803228523632133712043 2642704842785448200568065)
              ·
                refine ⟨1982028632089086150426049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642704842785448200568065 1982028632089086150426049)
                ·
                  refine ⟨1486521474066814612819537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982028632089086150426049 1486521474066814612819537)
                  ·
                    refine ⟨1114891105550110959614653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1486521474066814612819537 1114891105550110959614653)
                    ·
                      refine ⟨418084164581291609855495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1114891105550110959614653 418084164581291609855495)
                      ·
                        rfl

theorem cell23_814216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_814216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814216 prefixEnd_814216 := by exact prefixLift 814216
  have htrace : WordTrace (prefixWord ++ tailWord_814216) baseStart_814216 baseEnd_814216 := by
    simpa [prefixWord, tailWord_814216, baseEnd_814216] using wordTrace_append hprefix tailTrace_814216
  have hstable : (prefixWord ++ tailWord_814216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814216).length < 2 ^ (prefixWord ++ tailWord_814216).sum := by decide
  have hdescent : baseEnd_814216 < baseStart_814216 := by decide
  rcases family_descends (prefixWord ++ tailWord_814216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814229 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_814229 : Nat := 118140960795 + 814229 * 2 ^ 59
def prefixEnd_814229 : Nat := 4983230072969 + 3 ^ 40 * 814229 * 2
def baseEnd_814229 : Nat := 418090839829800058992935

theorem tailTrace_814229 : CollatzResearch.WordTrace tailWord_814229 prefixEnd_814229 418090839829800058992935 := by
  unfold tailWord_814229
  simp only [CollatzResearch.WordTrace]
  refine ⟨29697371367194867087237741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19798247578129911391491827 29697371367194867087237741)
  ·
    refine ⟨11136514262698075157714153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29697371367194867087237741 11136514262698075157714153)
    ·
      refine ⟨8352385697023556368285615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11136514262698075157714153 8352385697023556368285615)
      ·
        refine ⟨12528578545535334552428423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8352385697023556368285615 12528578545535334552428423)
        ·
          refine ⟨18792867818303001828642635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12528578545535334552428423 18792867818303001828642635)
          ·
            refine ⟨28189301727454502742963953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18792867818303001828642635 28189301727454502742963953)
            ·
              refine ⟨21141976295590877057222965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28189301727454502742963953 21141976295590877057222965)
              ·
                refine ⟨1982060277711644724114653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21141976295590877057222965 1982060277711644724114653)
                ·
                  refine ⟨743272604141866771542995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1982060277711644724114653 743272604141866771542995)
                  ·
                    refine ⟨1114908906212800157314493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 743272604141866771542995 1114908906212800157314493)
                    ·
                      refine ⟨418090839829800058992935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1114908906212800157314493 418090839829800058992935)
                      ·
                        rfl

theorem cell23_814229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_814229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814229 prefixEnd_814229 := by exact prefixLift 814229
  have htrace : WordTrace (prefixWord ++ tailWord_814229) baseStart_814229 baseEnd_814229 := by
    simpa [prefixWord, tailWord_814229, baseEnd_814229] using wordTrace_append hprefix tailTrace_814229
  have hstable : (prefixWord ++ tailWord_814229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814229).length < 2 ^ (prefixWord ++ tailWord_814229).sum := by decide
  have hdescent : baseEnd_814229 < baseStart_814229 := by decide
  rcases family_descends (prefixWord ++ tailWord_814229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814236 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 6]
def baseStart_814236 : Nat := 118140960795 + 814236 * 2 ^ 59
def prefixEnd_814236 : Nat := 4983230072969 + 3 ^ 40 * 814236 * 2
def baseEnd_814236 : Nat := 46454937132709059067267

theorem tailTrace_814236 : CollatzResearch.WordTrace tailWord_814236 prefixEnd_814236 46454937132709059067267 := by
  unfold tailWord_814236
  simp only [CollatzResearch.WordTrace]
  refine ⟨14848813339084753641371281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19798417785446338188495041 14848813339084753641371281)
  ·
    refine ⟨11136610004313565231028461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14848813339084753641371281 11136610004313565231028461)
    ·
      refine ⟨4176228751617586961635673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11136610004313565231028461 4176228751617586961635673)
      ·
        refine ⟨3132171563713190221226755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4176228751617586961635673 3132171563713190221226755)
        ·
          refine ⟨4698257345569785331840133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3132171563713190221226755 4698257345569785331840133)
          ·
            refine ⟨880923252294334749720025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4698257345569785331840133 880923252294334749720025)
            ·
              refine ⟨660692439220751062290019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880923252294334749720025 660692439220751062290019)
              ·
                refine ⟨991038658831126593435029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660692439220751062290019 991038658831126593435029)
                ·
                  refine ⟨46454937132709059067267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 991038658831126593435029 46454937132709059067267)
                  ·
                    rfl

theorem cell23_814236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_814236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814236 prefixEnd_814236 := by exact prefixLift 814236
  have htrace : WordTrace (prefixWord ++ tailWord_814236) baseStart_814236 baseEnd_814236 := by
    simpa [prefixWord, tailWord_814236, baseEnd_814236] using wordTrace_append hprefix tailTrace_814236
  have hstable : (prefixWord ++ tailWord_814236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814236).length < 2 ^ (prefixWord ++ tailWord_814236).sum := by decide
  have hdescent : baseEnd_814236 < baseStart_814236 := by decide
  rcases family_descends (prefixWord ++ tailWord_814236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814269 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_814269 : Nat := 118140960795 + 814269 * 2 ^ 59
def prefixEnd_814269 : Nat := 4983230072969 + 3 ^ 40 * 814269 * 2
def baseEnd_814269 : Nat := 418111379055979902492751

theorem tailTrace_814269 : CollatzResearch.WordTrace tailWord_814269 prefixEnd_814269 418111379055979902492751 := by
  unfold tailWord_814269
  simp only [CollatzResearch.WordTrace]
  refine ⟨29698830287049953918693861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19799220191366635945795907 29698830287049953918693861)
  ·
    refine ⟨5568530678821866359755099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29698830287049953918693861 5568530678821866359755099)
    ·
      refine ⟨8352796018232799539632649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5568530678821866359755099 8352796018232799539632649)
      ·
        refine ⟨6264597013674599654724487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8352796018232799539632649 6264597013674599654724487)
        ·
          refine ⟨9396895520511899482086731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6264597013674599654724487 9396895520511899482086731)
          ·
            refine ⟨14095343280767849223130097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9396895520511899482086731 14095343280767849223130097)
            ·
              refine ⟨10571507460575886917347573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14095343280767849223130097 10571507460575886917347573)
              ·
                refine ⟨991078824428989398501335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10571507460575886917347573 991078824428989398501335)
                ·
                  refine ⟨1486618236643484097752003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991078824428989398501335 1486618236643484097752003)
                  ·
                    refine ⟨2229927354965226146628005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1486618236643484097752003 2229927354965226146628005)
                    ·
                      refine ⟨418111379055979902492751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2229927354965226146628005 418111379055979902492751)
                      ·
                        rfl

theorem cell23_814269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_814269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814269 prefixEnd_814269 := by exact prefixLift 814269
  have htrace : WordTrace (prefixWord ++ tailWord_814269) baseStart_814269 baseEnd_814269 := by
    simpa [prefixWord, tailWord_814269, baseEnd_814269] using wordTrace_append hprefix tailTrace_814269
  have hstable : (prefixWord ++ tailWord_814269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814269).length < 2 ^ (prefixWord ++ tailWord_814269).sum := by decide
  have hdescent : baseEnd_814269 < baseStart_814269 := by decide
  rcases family_descends (prefixWord ++ tailWord_814269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814273 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_814273 : Nat := 118140960795 + 814273 * 2 ^ 59
def prefixEnd_814273 : Nat := 4983230072969 + 3 ^ 40 * 814273 * 2
def baseEnd_814273 : Nat := 418113432978597886842733

theorem tailTrace_814273 : CollatzResearch.WordTrace tailWord_814273 prefixEnd_814273 418113432978597886842733 := by
  unfold tailWord_814273
  simp only [CollatzResearch.WordTrace]
  refine ⟨29698976179035462601839473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19799317452690308401226315 29698976179035462601839473)
  ·
    refine ⟨22274232134276596951379605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29698976179035462601839473 22274232134276596951379605)
    ·
      refine ⟨1044104631294215482095919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22274232134276596951379605 1044104631294215482095919)
      ·
        refine ⟨1566156946941323223143879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044104631294215482095919 1566156946941323223143879)
        ·
          refine ⟨2349235420411984834715819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566156946941323223143879 2349235420411984834715819)
          ·
            refine ⟨3523853130617977252073729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349235420411984834715819 3523853130617977252073729)
            ·
              refine ⟨2642889847963482939055297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3523853130617977252073729 2642889847963482939055297)
              ·
                refine ⟨1982167385972612204291473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642889847963482939055297 1982167385972612204291473)
                ·
                  refine ⟨1486625539479459153218605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982167385972612204291473 1486625539479459153218605)
                  ·
                    refine ⟨557484577304797182456977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486625539479459153218605 557484577304797182456977)
                    ·
                      refine ⟨418113432978597886842733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 557484577304797182456977 418113432978597886842733)
                      ·
                        rfl

theorem cell23_814273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_814273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814273 prefixEnd_814273 := by exact prefixLift 814273
  have htrace : WordTrace (prefixWord ++ tailWord_814273) baseStart_814273 baseEnd_814273 := by
    simpa [prefixWord, tailWord_814273, baseEnd_814273] using wordTrace_append hprefix tailTrace_814273
  have hstable : (prefixWord ++ tailWord_814273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814273).length < 2 ^ (prefixWord ++ tailWord_814273).sum := by decide
  have hdescent : baseEnd_814273 < baseStart_814273 := by decide
  rcases family_descends (prefixWord ++ tailWord_814273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814274 : List Nat := [3, 5, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_814274 : Nat := 118140960795 + 814274 * 2 ^ 59
def prefixEnd_814274 : Nat := 4983230072969 + 3 ^ 40 * 814274 * 2
def baseEnd_814274 : Nat := 139371315486417460976743

theorem tailTrace_814274 : CollatzResearch.WordTrace tailWord_814274 prefixEnd_814274 139371315486417460976743 := by
  unfold tailWord_814274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7424753163007959943156469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19799341768021226515083917 7424753163007959943156469)
  ·
    refine ⟨696070609031996244670919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7424753163007959943156469 696070609031996244670919)
    ·
      refine ⟨1044105913547994367006379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696070609031996244670919 1044105913547994367006379)
      ·
        refine ⟨1566158870321991550509569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044105913547994367006379 1566158870321991550509569)
        ·
          refine ⟨1174619152741493662882177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566158870321991550509569 1174619152741493662882177)
          ·
            refine ⟨880964364556120247161633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174619152741493662882177 880964364556120247161633)
            ·
              refine ⟨660723273417090185371225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880964364556120247161633 660723273417090185371225)
              ·
                refine ⟨495542455062817639028419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660723273417090185371225 495542455062817639028419)
                ·
                  refine ⟨743313682594226458542629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495542455062817639028419 743313682594226458542629)
                  ·
                    refine ⟨139371315486417460976743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 743313682594226458542629 139371315486417460976743)
                    ·
                      rfl

theorem cell23_814274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_814274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814274 prefixEnd_814274 := by exact prefixLift 814274
  have htrace : WordTrace (prefixWord ++ tailWord_814274) baseStart_814274 baseEnd_814274 := by
    simpa [prefixWord, tailWord_814274, baseEnd_814274] using wordTrace_append hprefix tailTrace_814274
  have hstable : (prefixWord ++ tailWord_814274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814274).length < 2 ^ (prefixWord ++ tailWord_814274).sum := by decide
  have hdescent : baseEnd_814274 < baseStart_814274 := by decide
  rcases family_descends (prefixWord ++ tailWord_814274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814323 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 1, 2, 3]
def baseStart_814323 : Nat := 118140960795 + 814323 * 2 ^ 59
def prefixEnd_814323 : Nat := 4983230072969 + 3 ^ 40 * 814323 * 2
def baseEnd_814323 : Nat := 418139107011322691217503

theorem tailTrace_814323 : CollatzResearch.WordTrace tailWord_814323 prefixEnd_814323 418139107011322691217503 := by
  unfold tailWord_814323
  simp only [CollatzResearch.WordTrace]
  refine ⟨29700799828854321141159623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19800533219236214094106415 29700799828854321141159623)
  ·
    refine ⟨44551199743281481711739435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29700799828854321141159623 44551199743281481711739435)
    ·
      refine ⟨66826799614922222567609153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44551199743281481711739435 66826799614922222567609153)
      ·
        refine ⟨50120099711191666925706865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66826799614922222567609153 50120099711191666925706865)
        ·
          refine ⟨37590074783393750194280149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50120099711191666925706865 37590074783393750194280149)
          ·
            refine ⟨881017377735791020178441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 37590074783393750194280149 881017377735791020178441)
            ·
              refine ⟨660763033301843265133831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881017377735791020178441 660763033301843265133831)
              ·
                refine ⟨991144549952764897700747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660763033301843265133831 991144549952764897700747)
                ·
                  refine ⟨1486716824929147346551121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991144549952764897700747 1486716824929147346551121)
                  ·
                    refine ⟨1115037618696860509913341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1486716824929147346551121 1115037618696860509913341)
                    ·
                      refine ⟨418139107011322691217503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1115037618696860509913341 418139107011322691217503)
                      ·
                        rfl

theorem cell23_814323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 2, 3].length) (baseStart_814323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814323 prefixEnd_814323 := by exact prefixLift 814323
  have htrace : WordTrace (prefixWord ++ tailWord_814323) baseStart_814323 baseEnd_814323 := by
    simpa [prefixWord, tailWord_814323, baseEnd_814323] using wordTrace_append hprefix tailTrace_814323
  have hstable : (prefixWord ++ tailWord_814323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814323).length < 2 ^ (prefixWord ++ tailWord_814323).sum := by decide
  have hdescent : baseEnd_814323 < baseStart_814323 := by decide
  rcases family_descends (prefixWord ++ tailWord_814323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814353 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 2, 1, 3]
def baseStart_814353 : Nat := 118140960795 + 814353 * 2 ^ 59
def prefixEnd_814353 : Nat := 4983230072969 + 3 ^ 40 * 814353 * 2
def baseEnd_814353 : Nat := 418154511430957573842365

theorem tailTrace_814353 : CollatzResearch.WordTrace tailWord_814353 prefixEnd_814353 418154511430957573842365 := by
  unfold tailWord_814353
  simp only [CollatzResearch.WordTrace]
  refine ⟨29701894018745636264751713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19801262679163757509834475 29701894018745636264751713)
  ·
    refine ⟨22276420514059227198563785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29701894018745636264751713 22276420514059227198563785)
    ·
      refine ⟨16707315385544420398922839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22276420514059227198563785 16707315385544420398922839)
      ·
        refine ⟨25060973078316630598384259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16707315385544420398922839 25060973078316630598384259)
        ·
          refine ⟨37591459617474945897576389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25060973078316630598384259 37591459617474945897576389)
          ·
            refine ⟨7048398678276552355795573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37591459617474945897576389 7048398678276552355795573)
            ·
              refine ⟨660787376088426783355835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7048398678276552355795573 660787376088426783355835)
              ·
                refine ⟨991181064132640175033753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660787376088426783355835 991181064132640175033753)
                ·
                  refine ⟨743385798099480131275315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 991181064132640175033753 743385798099480131275315)
                  ·
                    refine ⟨1115078697149220196912973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 743385798099480131275315 1115078697149220196912973)
                    ·
                      refine ⟨418154511430957573842365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1115078697149220196912973 418154511430957573842365)
                      ·
                        rfl

theorem cell23_814353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_814353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814353 prefixEnd_814353 := by exact prefixLift 814353
  have htrace : WordTrace (prefixWord ++ tailWord_814353) baseStart_814353 baseEnd_814353 := by
    simpa [prefixWord, tailWord_814353, baseEnd_814353] using wordTrace_append hprefix tailTrace_814353
  have hstable : (prefixWord ++ tailWord_814353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814353).length < 2 ^ (prefixWord ++ tailWord_814353).sum := by decide
  have hdescent : baseEnd_814353 < baseStart_814353 := by decide
  rcases family_descends (prefixWord ++ tailWord_814353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814392 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_814392 : Nat := 118140960795 + 814392 * 2 ^ 59
def prefixEnd_814392 : Nat := 4983230072969 + 3 ^ 40 * 814392 * 2
def baseEnd_814392 : Nat := 418174537176482921254685

theorem tailTrace_814392 : CollatzResearch.WordTrace tailWord_814392 prefixEnd_814392 418174537176482921254685 := by
  unfold tailWord_814392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14851658232802172962710715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19802210977069563950280953 14851658232802172962710715)
  ·
    refine ⟨22277487349203259444066073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14851658232802172962710715 22277487349203259444066073)
    ·
      refine ⟨16708115511902444583049555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22277487349203259444066073 16708115511902444583049555)
      ·
        refine ⟨25062173267853666874574333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16708115511902444583049555 25062173267853666874574333)
        ·
          refine ⟨9398314975445125077965375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25062173267853666874574333 9398314975445125077965375)
          ·
            refine ⟨14097472463167687616948063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9398314975445125077965375 14097472463167687616948063)
            ·
              refine ⟨21146208694751531425422095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14097472463167687616948063 21146208694751531425422095)
              ·
                refine ⟨31719313042127297138133143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21146208694751531425422095 31719313042127297138133143)
                ·
                  refine ⟨47578969563190945707199715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31719313042127297138133143 47578969563190945707199715)
                  ·
                    refine ⟨71368454344786418560799573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47578969563190945707199715 71368454344786418560799573)
                    ·
                      refine ⟨418174537176482921254685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 71368454344786418560799573 418174537176482921254685)
                      ·
                        rfl

theorem cell23_814392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_814392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814392 prefixEnd_814392 := by exact prefixLift 814392
  have htrace : WordTrace (prefixWord ++ tailWord_814392) baseStart_814392 baseEnd_814392 := by
    simpa [prefixWord, tailWord_814392, baseEnd_814392] using wordTrace_append hprefix tailTrace_814392
  have hstable : (prefixWord ++ tailWord_814392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814392).length < 2 ^ (prefixWord ++ tailWord_814392).sum := by decide
  have hdescent : baseEnd_814392 < baseStart_814392 := by decide
  rcases family_descends (prefixWord ++ tailWord_814392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814399 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 7]
def baseStart_814399 : Nat := 118140960795 + 814399 * 2 ^ 59
def prefixEnd_814399 : Nat := 4983230072969 + 3 ^ 40 * 814399 * 2
def baseEnd_814399 : Nat := 46464236837896043763017

theorem tailTrace_814399 : CollatzResearch.WordTrace tailWord_814399 prefixEnd_814399 46464236837896043763017 := by
  unfold tailWord_814399
  simp only [CollatzResearch.WordTrace]
  refine ⟨29703571776578986120926251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19802381184385990747284167 29703571776578986120926251)
  ·
    refine ⟨44555357664868479181389377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29703571776578986120926251 44555357664868479181389377)
    ·
      refine ⟨33416518248651359386042033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44555357664868479181389377 33416518248651359386042033)
      ·
        refine ⟨25062388686488519539531525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33416518248651359386042033 25062388686488519539531525)
        ·
          refine ⟨4699197878716597413662161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25062388686488519539531525 4699197878716597413662161)
          ·
            refine ⟨3524398409037448060246621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4699197878716597413662161 3524398409037448060246621)
            ·
              refine ⟨1321649403389043022592483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3524398409037448060246621 1321649403389043022592483)
              ·
                refine ⟨1982474105083564533888725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321649403389043022592483 1982474105083564533888725)
                ·
                  refine ⟨46464236837896043763017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1982474105083564533888725 46464236837896043763017)
                  ·
                    rfl

theorem cell23_814399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 7].length) (baseStart_814399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814399 prefixEnd_814399 := by exact prefixLift 814399
  have htrace : WordTrace (prefixWord ++ tailWord_814399) baseStart_814399 baseEnd_814399 := by
    simpa [prefixWord, tailWord_814399, baseEnd_814399] using wordTrace_append hprefix tailTrace_814399
  have hstable : (prefixWord ++ tailWord_814399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814399).length < 2 ^ (prefixWord ++ tailWord_814399).sum := by decide
  have hdescent : baseEnd_814399 < baseStart_814399 := by decide
  rcases family_descends (prefixWord ++ tailWord_814399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814409 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 3]
def baseStart_814409 : Nat := 118140960795 + 814409 * 2 ^ 59
def prefixEnd_814409 : Nat := 4983230072969 + 3 ^ 40 * 814409 * 2
def baseEnd_814409 : Nat := 418183266347609354742107

theorem tailTrace_814409 : CollatzResearch.WordTrace tailWord_814409 prefixEnd_814409 418183266347609354742107 := by
  unfold tailWord_814409
  simp only [CollatzResearch.WordTrace]
  refine ⟨29703936506542757828790281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19802624337695171885860187 29703936506542757828790281)
  ·
    refine ⟨22277952379907068371592711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29703936506542757828790281 22277952379907068371592711)
    ·
      refine ⟨33416928569860602557389067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22277952379907068371592711 33416928569860602557389067)
      ·
        refine ⟨50125392854790903836083601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33416928569860602557389067 50125392854790903836083601)
        ·
          refine ⟨37594044641093177877062701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50125392854790903836083601 37594044641093177877062701)
          ·
            refine ⟨14097766740409941703898513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37594044641093177877062701 14097766740409941703898513)
            ·
              refine ⟨10573325055307456277923885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14097766740409941703898513 10573325055307456277923885)
              ·
                refine ⟨3964996895740296104221457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10573325055307456277923885 3964996895740296104221457)
                ·
                  refine ⟨2973747671805222078166093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3964996895740296104221457 2973747671805222078166093)
                  ·
                    refine ⟨1115155376926958279312285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2973747671805222078166093 1115155376926958279312285)
                    ·
                      refine ⟨418183266347609354742107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1115155376926958279312285 418183266347609354742107)
                      ·
                        rfl

theorem cell23_814409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 3].length) (baseStart_814409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814409 prefixEnd_814409 := by exact prefixLift 814409
  have htrace : WordTrace (prefixWord ++ tailWord_814409) baseStart_814409 baseEnd_814409 := by
    simpa [prefixWord, tailWord_814409, baseEnd_814409] using wordTrace_append hprefix tailTrace_814409
  have hstable : (prefixWord ++ tailWord_814409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814409).length < 2 ^ (prefixWord ++ tailWord_814409).sum := by decide
  have hdescent : baseEnd_814409 < baseStart_814409 := by decide
  rcases family_descends (prefixWord ++ tailWord_814409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814476 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_814476 : Nat := 118140960795 + 814476 * 2 ^ 59
def prefixEnd_814476 : Nat := 4983230072969 + 3 ^ 40 * 814476 * 2
def baseEnd_814476 : Nat := 139405889850486864201433

theorem tailTrace_814476 : CollatzResearch.WordTrace tailWord_814476 prefixEnd_814476 139405889850486864201433 := by
  unfold tailWord_814476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14853190098650014135739641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19804253464866685514319521 14853190098650014135739641)
  ·
    refine ⟨11139892573987510601804731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14853190098650014135739641 11139892573987510601804731)
    ·
      refine ⟨16709838860981265902707097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11139892573987510601804731 16709838860981265902707097)
      ·
        refine ⟨12532379145735949427030323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16709838860981265902707097 12532379145735949427030323)
        ·
          refine ⟨18798568718603924140545485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12532379145735949427030323 18798568718603924140545485)
          ·
            refine ⟨7049463269476471552704557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18798568718603924140545485 7049463269476471552704557)
            ·
              refine ⟨2643548726053676832264209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7049463269476471552704557 2643548726053676832264209)
              ·
                refine ⟨1982661544540257624198157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643548726053676832264209 1982661544540257624198157)
                ·
                  refine ⟨743498079202596609074309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1982661544540257624198157 743498079202596609074309)
                  ·
                    refine ⟨139405889850486864201433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 743498079202596609074309 139405889850486864201433)
                    ·
                      rfl

theorem cell23_814476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_814476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814476 prefixEnd_814476 := by exact prefixLift 814476
  have htrace : WordTrace (prefixWord ++ tailWord_814476) baseStart_814476 baseEnd_814476 := by
    simpa [prefixWord, tailWord_814476, baseEnd_814476] using wordTrace_append hprefix tailTrace_814476
  have hstable : (prefixWord ++ tailWord_814476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814476).length < 2 ^ (prefixWord ++ tailWord_814476).sum := by decide
  have hdescent : baseEnd_814476 < baseStart_814476 := by decide
  rcases family_descends (prefixWord ++ tailWord_814476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814576 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 5]
def baseStart_814576 : Nat := 118140960795 + 814576 * 2 ^ 59
def prefixEnd_814576 : Nat := 4983230072969 + 3 ^ 40 * 814576 * 2
def baseEnd_814576 : Nat := 418269017616910201353839

theorem tailTrace_814576 : CollatzResearch.WordTrace tailWord_814576 prefixEnd_814576 418269017616910201353839 := by
  unfold tailWord_814576
  simp only [CollatzResearch.WordTrace]
  refine ⟨14855013748468872675059791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19806684997958496900079721 14855013748468872675059791)
  ·
    refine ⟨22282520622703309012589687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14855013748468872675059791 22282520622703309012589687)
    ·
      refine ⟨33423780934054963518884531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22282520622703309012589687 33423780934054963518884531)
      ·
        refine ⟨50135671401082445278326797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33423780934054963518884531 50135671401082445278326797)
        ·
          refine ⟨18800876775405916979372549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50135671401082445278326797 18800876775405916979372549)
          ·
            refine ⟨3525164395388609433632353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18800876775405916979372549 3525164395388609433632353)
            ·
              refine ⟨2643873296541457075224265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3525164395388609433632353 2643873296541457075224265)
              ·
                refine ⟨1982904972406092806418199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643873296541457075224265 1982904972406092806418199)
                ·
                  refine ⟨2974357458609139209627299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982904972406092806418199 2974357458609139209627299)
                  ·
                    refine ⟨4461536187913708814440949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2974357458609139209627299 4461536187913708814440949)
                    ·
                      refine ⟨418269017616910201353839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4461536187913708814440949 418269017616910201353839)
                      ·
                        rfl

theorem cell23_814576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_814576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814576 prefixEnd_814576 := by exact prefixLift 814576
  have htrace : WordTrace (prefixWord ++ tailWord_814576) baseStart_814576 baseEnd_814576 := by
    simpa [prefixWord, tailWord_814576, baseEnd_814576] using wordTrace_append hprefix tailTrace_814576
  have hstable : (prefixWord ++ tailWord_814576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814576).length < 2 ^ (prefixWord ++ tailWord_814576).sum := by decide
  have hdescent : baseEnd_814576 < baseStart_814576 := by decide
  rcases family_descends (prefixWord ++ tailWord_814576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814586 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_814586 : Nat := 118140960795 + 814586 * 2 ^ 59
def prefixEnd_814586 : Nat := 4983230072969 + 3 ^ 40 * 814586 * 2
def baseEnd_814586 : Nat := 418274152423455162228793

theorem tailTrace_814586 : CollatzResearch.WordTrace tailWord_814586 prefixEnd_814586 418274152423455162228793 := by
  unfold tailWord_814586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427598056725379264495903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19806928151267678038655741 7427598056725379264495903)
  ·
    refine ⟨11141397085088068896743855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7427598056725379264495903 11141397085088068896743855)
    ·
      refine ⟨16712095627632103345115783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11141397085088068896743855 16712095627632103345115783)
      ·
        refine ⟨25068143441448155017673675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16712095627632103345115783 25068143441448155017673675)
        ·
          refine ⟨37602215162172232526510513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25068143441448155017673675 37602215162172232526510513)
          ·
            refine ⟨28201661371629174394882885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37602215162172232526510513 28201661371629174394882885)
            ·
              refine ⟨5287811507180470199040541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28201661371629174394882885 5287811507180470199040541)
              ·
                refine ⟨1982929315192676324640203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5287811507180470199040541 1982929315192676324640203)
                ·
                  refine ⟨2974393972789014486960305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982929315192676324640203 2974393972789014486960305)
                  ·
                    refine ⟨2230795479591760865220229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2974393972789014486960305 2230795479591760865220229)
                    ·
                      refine ⟨418274152423455162228793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2230795479591760865220229 418274152423455162228793)
                      ·
                        rfl

theorem cell23_814586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_814586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814586 prefixEnd_814586 := by exact prefixLift 814586
  have htrace : WordTrace (prefixWord ++ tailWord_814586) baseStart_814586 baseEnd_814586 := by
    simpa [prefixWord, tailWord_814586, baseEnd_814586] using wordTrace_append hprefix tailTrace_814586
  have hstable : (prefixWord ++ tailWord_814586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814586).length < 2 ^ (prefixWord ++ tailWord_814586).sum := by decide
  have hdescent : baseEnd_814586 < baseStart_814586 := by decide
  rcases family_descends (prefixWord ++ tailWord_814586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814603 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 4]
def baseStart_814603 : Nat := 118140960795 + 814603 * 2 ^ 59
def prefixEnd_814603 : Nat := 4983230072969 + 3 ^ 40 * 814603 * 2
def baseEnd_814603 : Nat := 418282881594581595716215

theorem tailTrace_814603 : CollatzResearch.WordTrace tailWord_814603 prefixEnd_814603 418282881594581595716215 := by
  unfold tailWord_814603
  simp only [CollatzResearch.WordTrace]
  refine ⟨29711012267839928961352463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19807341511893285974234975 29711012267839928961352463)
  ·
    refine ⟨44566518401759893442028695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29711012267839928961352463 44566518401759893442028695)
    ·
      refine ⟨66849777602639840163043043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44566518401759893442028695 66849777602639840163043043)
      ·
        refine ⟨100274666403959760244564565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66849777602639840163043043 100274666403959760244564565)
        ·
          refine ⟨1175093746921403440365991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 100274666403959760244564565 1175093746921403440365991)
          ·
            refine ⟨1762640620382105160548987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175093746921403440365991 1762640620382105160548987)
            ·
              refine ⟨2643960930573157740823481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762640620382105160548987 2643960930573157740823481)
              ·
                refine ⟨1982970697929868305617611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643960930573157740823481 1982970697929868305617611)
                ·
                  refine ⟨2974456046894802458426417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982970697929868305617611 2974456046894802458426417)
                  ·
                    refine ⟨2230842035171101843819813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2974456046894802458426417 2230842035171101843819813)
                    ·
                      refine ⟨418282881594581595716215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2230842035171101843819813 418282881594581595716215)
                      ·
                        rfl

theorem cell23_814603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 4].length) (baseStart_814603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814603 prefixEnd_814603 := by exact prefixLift 814603
  have htrace : WordTrace (prefixWord ++ tailWord_814603) baseStart_814603 baseEnd_814603 := by
    simpa [prefixWord, tailWord_814603, baseEnd_814603] using wordTrace_append hprefix tailTrace_814603
  have hstable : (prefixWord ++ tailWord_814603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814603).length < 2 ^ (prefixWord ++ tailWord_814603).sum := by decide
  have hdescent : baseEnd_814603 < baseStart_814603 := by decide
  rcases family_descends (prefixWord ++ tailWord_814603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814619 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 7]
def baseStart_814619 : Nat := 118140960795 + 814619 * 2 ^ 59
def prefixEnd_814619 : Nat := 4983230072969 + 3 ^ 40 * 814619 * 2
def baseEnd_814619 : Nat := 418291097285053533116141

theorem tailTrace_814619 : CollatzResearch.WordTrace tailWord_814619 prefixEnd_814619 418291097285053533116141 := by
  unfold tailWord_814619
  simp only [CollatzResearch.WordTrace]
  refine ⟨29711595835781963693934911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19807730557187975795956607 29711595835781963693934911)
  ·
    refine ⟨44567393753672945540902367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29711595835781963693934911 44567393753672945540902367)
    ·
      refine ⟨66851090630509418311353551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44567393753672945540902367 66851090630509418311353551)
      ·
        refine ⟨100276635945764127467030327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66851090630509418311353551 100276635945764127467030327)
        ·
          refine ⟨150414953918646191200545491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100276635945764127467030327 150414953918646191200545491)
          ·
            refine ⟨225622430877969286800818237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150414953918646191200545491 225622430877969286800818237)
            ·
              refine ⟨84608411579238482550306839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225622430877969286800818237 84608411579238482550306839)
              ·
                refine ⟨126912617368857723825460259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84608411579238482550306839 126912617368857723825460259)
                ·
                  refine ⟨190368926053286585738190389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126912617368857723825460259 190368926053286585738190389)
                  ·
                    refine ⟨17847086817495617412955349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 190368926053286585738190389 17847086817495617412955349)
                    ·
                      refine ⟨418291097285053533116141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17847086817495617412955349 418291097285053533116141)
                      ·
                        rfl

theorem cell23_814619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_814619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814619 prefixEnd_814619 := by exact prefixLift 814619
  have htrace : WordTrace (prefixWord ++ tailWord_814619) baseStart_814619 baseEnd_814619 := by
    simpa [prefixWord, tailWord_814619, baseEnd_814619] using wordTrace_append hprefix tailTrace_814619
  have hstable : (prefixWord ++ tailWord_814619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814619).length < 2 ^ (prefixWord ++ tailWord_814619).sum := by decide
  have hdescent : baseEnd_814619 < baseStart_814619 := by decide
  rcases family_descends (prefixWord ++ tailWord_814619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814623 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 4, 1, 3]
def baseStart_814623 : Nat := 118140960795 + 814623 * 2 ^ 59
def prefixEnd_814623 : Nat := 4983230072969 + 3 ^ 40 * 814623 * 2
def baseEnd_814623 : Nat := 418293151207671517466123

theorem tailTrace_814623 : CollatzResearch.WordTrace tailWord_814623 prefixEnd_814623 418293151207671517466123 := by
  unfold tailWord_814623
  simp only [CollatzResearch.WordTrace]
  refine ⟨29711741727767472377080523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19807827818511648251387015 29711741727767472377080523)
  ·
    refine ⟨44567612591651208565620785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29711741727767472377080523 44567612591651208565620785)
    ·
      refine ⟨33425709443738406424215589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44567612591651208565620785 33425709443738406424215589)
      ·
        refine ⟨6267320520700951204540423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33425709443738406424215589 6267320520700951204540423)
        ·
          refine ⟨9400980781051426806810635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6267320520700951204540423 9400980781051426806810635)
          ·
            refine ⟨14101471171577140210215953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9400980781051426806810635 14101471171577140210215953)
            ·
              refine ⟨10576103378682855157661965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14101471171577140210215953 10576103378682855157661965)
              ·
                refine ⟨3966038767006070684123237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10576103378682855157661965 3966038767006070684123237)
                ·
                  refine ⟨743632268813638253273107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3966038767006070684123237 743632268813638253273107)
                  ·
                    refine ⟨1115448403220457379909661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 743632268813638253273107 1115448403220457379909661)
                    ·
                      refine ⟨418293151207671517466123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1115448403220457379909661 418293151207671517466123)
                      ·
                        rfl

theorem cell23_814623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_814623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814623 prefixEnd_814623 := by exact prefixLift 814623
  have htrace : WordTrace (prefixWord ++ tailWord_814623) baseStart_814623 baseEnd_814623 := by
    simpa [prefixWord, tailWord_814623, baseEnd_814623] using wordTrace_append hprefix tailTrace_814623
  have hstable : (prefixWord ++ tailWord_814623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814623).length < 2 ^ (prefixWord ++ tailWord_814623).sum := by decide
  have hdescent : baseEnd_814623 < baseStart_814623 := by decide
  rcases family_descends (prefixWord ++ tailWord_814623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814624 : List Nat := [2, 1, 1, 6, 1, 2, 1, 4, 1, 2, 2]
def baseStart_814624 : Nat := 118140960795 + 814624 * 2 ^ 59
def prefixEnd_814624 : Nat := 4983230072969 + 3 ^ 40 * 814624 * 2
def baseEnd_814624 : Nat := 418293664688326013553619

theorem tailTrace_814624 : CollatzResearch.WordTrace tailWord_814624 prefixEnd_814624 418293664688326013553619 := by
  unfold tailWord_814624
  simp only [CollatzResearch.WordTrace]
  refine ⟨14855889100381924773933463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19807852133842566365244617 14855889100381924773933463)
  ·
    refine ⟨22283833650572887160900195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14855889100381924773933463 22283833650572887160900195)
    ·
      refine ⟨33425750475859330741350293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22283833650572887160900195 33425750475859330741350293)
      ·
        refine ⟨1566832053555906128500795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33425750475859330741350293 1566832053555906128500795)
        ·
          refine ⟨2350248080333859192751193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566832053555906128500795 2350248080333859192751193)
          ·
            refine ⟨1762686060250394394563395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2350248080333859192751193 1762686060250394394563395)
            ·
              refine ⟨2644029090375591591845093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762686060250394394563395 2644029090375591591845093)
              ·
                refine ⟨495755454445423423470955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2644029090375591591845093 495755454445423423470955)
                ·
                  refine ⟨743633181668135135206433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495755454445423423470955 743633181668135135206433)
                  ·
                    refine ⟨557724886251101351404825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 743633181668135135206433 557724886251101351404825)
                    ·
                      refine ⟨418293664688326013553619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 557724886251101351404825 418293664688326013553619)
                      ·
                        rfl

theorem cell23_814624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_814624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814624 prefixEnd_814624 := by exact prefixLift 814624
  have htrace : WordTrace (prefixWord ++ tailWord_814624) baseStart_814624 baseEnd_814624 := by
    simpa [prefixWord, tailWord_814624, baseEnd_814624] using wordTrace_append hprefix tailTrace_814624
  have hstable : (prefixWord ++ tailWord_814624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814624).length < 2 ^ (prefixWord ++ tailWord_814624).sum := by decide
  have hdescent : baseEnd_814624 < baseStart_814624 := by decide
  rcases family_descends (prefixWord ++ tailWord_814624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814626 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_814626 : Nat := 118140960795 + 814626 * 2 ^ 59
def prefixEnd_814626 : Nat := 4983230072969 + 3 ^ 40 * 814626 * 2
def baseEnd_814626 : Nat := 139431563883211668576203

theorem tailTrace_814626 : CollatzResearch.WordTrace tailWord_814626 prefixEnd_814626 139431563883211668576203 := by
  unfold tailWord_814626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427962786689150972359933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19807900764504402592959821 7427962786689150972359933)
  ·
    refine ⟨2785486045008431614634975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7427962786689150972359933 2785486045008431614634975)
    ·
      refine ⟨4178229067512647421952463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2785486045008431614634975 4178229067512647421952463)
      ·
        refine ⟨6267343601268971132928695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4178229067512647421952463 6267343601268971132928695)
        ·
          refine ⟨9401015401903456699393043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6267343601268971132928695 9401015401903456699393043)
          ·
            refine ⟨14101523102855185049089565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9401015401903456699393043 14101523102855185049089565)
            ·
              refine ⟨5288071163570694393408587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14101523102855185049089565 5288071163570694393408587)
              ·
                refine ⟨7932106745356041590112881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288071163570694393408587 7932106745356041590112881)
                ·
                  refine ⟨5949080059017031192584661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7932106745356041590112881 5949080059017031192584661)
                  ·
                    refine ⟨139431563883211668576203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5949080059017031192584661 139431563883211668576203)
                    ·
                      rfl

theorem cell23_814626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_814626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814626 prefixEnd_814626 := by exact prefixLift 814626
  have htrace : WordTrace (prefixWord ++ tailWord_814626) baseStart_814626 baseEnd_814626 := by
    simpa [prefixWord, tailWord_814626, baseEnd_814626] using wordTrace_append hprefix tailTrace_814626
  have hstable : (prefixWord ++ tailWord_814626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814626).length < 2 ^ (prefixWord ++ tailWord_814626).sum := by decide
  have hdescent : baseEnd_814626 < baseStart_814626 := by decide
  rcases family_descends (prefixWord ++ tailWord_814626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814650 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2]
def baseStart_814650 : Nat := 118140960795 + 814650 * 2 ^ 59
def prefixEnd_814650 : Nat := 4983230072969 + 3 ^ 40 * 814650 * 2
def baseEnd_814650 : Nat := 418307015185342911828499

theorem tailTrace_814650 : CollatzResearch.WordTrace tailWord_814650 prefixEnd_814650 418307015185342911828499 := by
  unfold tailWord_814650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7428181624667413997078351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19808484332446437325542269 7428181624667413997078351)
  ·
    refine ⟨11142272437001120995617527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7428181624667413997078351 11142272437001120995617527)
    ·
      refine ⟨16713408655501681493426291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11142272437001120995617527 16713408655501681493426291)
      ·
        refine ⟨25070112983252522240139437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16713408655501681493426291 25070112983252522240139437)
        ·
          refine ⟨9401292368719695840052289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25070112983252522240139437 9401292368719695840052289)
          ·
            refine ⟨7050969276539771880039217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9401292368719695840052289 7050969276539771880039217)
            ·
              refine ⟨5288226957404828910029413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7050969276539771880039217 5288226957404828910029413)
              ·
                refine ⟨991542554513405420630515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5288226957404828910029413 991542554513405420630515)
                ·
                  refine ⟨1487313831770108130945773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991542554513405420630515 1487313831770108130945773)
                  ·
                    refine ⟨557742686913790549104665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487313831770108130945773 557742686913790549104665)
                    ·
                      refine ⟨418307015185342911828499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 557742686913790549104665 418307015185342911828499)
                      ·
                        rfl

theorem cell23_814650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_814650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814650 prefixEnd_814650 := by exact prefixLift 814650
  have htrace : WordTrace (prefixWord ++ tailWord_814650) baseStart_814650 baseEnd_814650 := by
    simpa [prefixWord, tailWord_814650, baseEnd_814650] using wordTrace_append hprefix tailTrace_814650
  have hstable : (prefixWord ++ tailWord_814650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814650).length < 2 ^ (prefixWord ++ tailWord_814650).sum := by decide
  have hdescent : baseEnd_814650 < baseStart_814650 := by decide
  rcases family_descends (prefixWord ++ tailWord_814650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814666 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_814666 : Nat := 118140960795 + 814666 * 2 ^ 59
def prefixEnd_814666 : Nat := 4983230072969 + 3 ^ 40 * 814666 * 2
def baseEnd_814666 : Nat := 418315230875814849228425

theorem tailTrace_814666 : CollatzResearch.WordTrace tailWord_814666 prefixEnd_814666 418315230875814849228425 := by
  unfold tailWord_814666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7428327516652922680223963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19808873377741127147263901 7428327516652922680223963)
  ·
    refine ⟨11142491274979384020335945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7428327516652922680223963 11142491274979384020335945)
    ·
      refine ⟨8356868456234538015251959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11142491274979384020335945 8356868456234538015251959)
      ·
        refine ⟨12535302684351807022877939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8356868456234538015251959 12535302684351807022877939)
        ·
          refine ⟨18802954026527710534316909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12535302684351807022877939 18802954026527710534316909)
          ·
            refine ⟨7051107759947891450368841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18802954026527710534316909 7051107759947891450368841)
            ·
              refine ⟨5288330819960918587776631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7051107759947891450368841 5288330819960918587776631)
              ·
                refine ⟨7932496229941377881664947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288330819960918587776631 7932496229941377881664947)
                ·
                  refine ⟨11898744344912066822497421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7932496229941377881664947 11898744344912066822497421)
                  ·
                    refine ⟨4462029129342025058436533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11898744344912066822497421 4462029129342025058436533)
                    ·
                      refine ⟨418315230875814849228425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4462029129342025058436533 418315230875814849228425)
                      ·
                        rfl

theorem cell23_814666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_814666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814666 prefixEnd_814666 := by exact prefixLift 814666
  have htrace : WordTrace (prefixWord ++ tailWord_814666) baseStart_814666 baseEnd_814666 := by
    simpa [prefixWord, tailWord_814666, baseEnd_814666] using wordTrace_append hprefix tailTrace_814666
  have hstable : (prefixWord ++ tailWord_814666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814666).length < 2 ^ (prefixWord ++ tailWord_814666).sum := by decide
  have hdescent : baseEnd_814666 < baseStart_814666 := by decide
  rcases family_descends (prefixWord ++ tailWord_814666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814693 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_814693 : Nat := 118140960795 + 814693 * 2 ^ 59
def prefixEnd_814693 : Nat := 4983230072969 + 3 ^ 40 * 814693 * 2
def baseEnd_814693 : Nat := 418329094853486243590801

theorem tailTrace_814693 : CollatzResearch.WordTrace tailWord_814693 prefixEnd_814693 418329094853486243590801 := by
  unfold tailWord_814693
  simp only [CollatzResearch.WordTrace]
  refine ⟨29714294837513874332128733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19809529891675916221419155 29714294837513874332128733)
  ·
    refine ⟨11142860564067702874548275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29714294837513874332128733 11142860564067702874548275)
    ·
      refine ⟨16714290846101554311822413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11142860564067702874548275 16714290846101554311822413)
      ·
        refine ⟨6267859067288082866933405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16714290846101554311822413 6267859067288082866933405)
        ·
          refine ⟨2350447150233031075100027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6267859067288082866933405 2350447150233031075100027)
          ·
            refine ⟨3525670725349546612650041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350447150233031075100027 3525670725349546612650041)
            ·
              refine ⟨2644253044012159959487531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3525670725349546612650041 2644253044012159959487531)
              ·
                refine ⟨3966379566018239939231297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644253044012159959487531 3966379566018239939231297)
                ·
                  refine ⟨2974784674513679954423473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3966379566018239939231297 2974784674513679954423473)
                  ·
                    refine ⟨2231088505885259965817605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2974784674513679954423473 2231088505885259965817605)
                    ·
                      refine ⟨418329094853486243590801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2231088505885259965817605 418329094853486243590801)
                      ·
                        rfl

theorem cell23_814693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_814693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814693 prefixEnd_814693 := by exact prefixLift 814693
  have htrace : WordTrace (prefixWord ++ tailWord_814693) baseStart_814693 baseEnd_814693 := by
    simpa [prefixWord, tailWord_814693, baseEnd_814693] using wordTrace_append hprefix tailTrace_814693
  have hstable : (prefixWord ++ tailWord_814693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814693).length < 2 ^ (prefixWord ++ tailWord_814693).sum := by decide
  have hdescent : baseEnd_814693 < baseStart_814693 := by decide
  rcases family_descends (prefixWord ++ tailWord_814693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814723 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 1, 7, 2]
def baseStart_814723 : Nat := 118140960795 + 814723 * 2 ^ 59
def prefixEnd_814723 : Nat := 4983230072969 + 3 ^ 40 * 814723 * 2
def baseEnd_814723 : Nat := 418344499273121126215663

theorem tailTrace_814723 : CollatzResearch.WordTrace tailWord_814723 prefixEnd_814723 418344499273121126215663 := by
  unfold tailWord_814723
  simp only [CollatzResearch.WordTrace]
  refine ⟨29715389027405189455720823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19810259351603459637147215 29715389027405189455720823)
  ·
    refine ⟨44573083541107784183581235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29715389027405189455720823 44573083541107784183581235)
    ·
      refine ⟨66859625311661676275371853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44573083541107784183581235 66859625311661676275371853)
      ·
        refine ⟨25072359491873128603264445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66859625311661676275371853 25072359491873128603264445)
        ·
          refine ⟨9402134809452423226224167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25072359491873128603264445 9402134809452423226224167)
          ·
            refine ⟨14103202214178634839336251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9402134809452423226224167 14103202214178634839336251)
            ·
              refine ⟨21154803321267952259004377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14103202214178634839336251 21154803321267952259004377)
              ·
                refine ⟨15866102490950964194253283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21154803321267952259004377 15866102490950964194253283)
                ·
                  refine ⟨23799153736426446291379925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15866102490950964194253283 23799153736426446291379925)
                  ·
                    refine ⟨557792665697494834954217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23799153736426446291379925 557792665697494834954217)
                    ·
                      refine ⟨418344499273121126215663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 557792665697494834954217 418344499273121126215663)
                      ·
                        rfl

theorem cell23_814723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_814723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814723 prefixEnd_814723 := by exact prefixLift 814723
  have htrace : WordTrace (prefixWord ++ tailWord_814723) baseStart_814723 baseEnd_814723 := by
    simpa [prefixWord, tailWord_814723, baseEnd_814723] using wordTrace_append hprefix tailTrace_814723
  have hstable : (prefixWord ++ tailWord_814723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814723).length < 2 ^ (prefixWord ++ tailWord_814723).sum := by decide
  have hdescent : baseEnd_814723 < baseStart_814723 := by decide
  rcases family_descends (prefixWord ++ tailWord_814723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814743 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_814743 : Nat := 118140960795 + 814743 * 2 ^ 59
def prefixEnd_814743 : Nat := 4983230072969 + 3 ^ 40 * 814743 * 2
def baseEnd_814743 : Nat := 418354768886211047965571

theorem tailTrace_814743 : CollatzResearch.WordTrace tailWord_814743 prefixEnd_814743 418354768886211047965571 := by
  unfold tailWord_814743
  simp only [CollatzResearch.WordTrace]
  refine ⟨29716118487332732871448883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19810745658221821914299255 29716118487332732871448883)
  ·
    refine ⟨44574177730999099307173325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29716118487332732871448883 44574177730999099307173325)
    ·
      refine ⟨16715316649124662240189997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44574177730999099307173325 16715316649124662240189997)
      ·
        refine ⟨6268243743421748340071249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16715316649124662240189997 6268243743421748340071249)
        ·
          refine ⟨4701182807566311255053437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6268243743421748340071249 4701182807566311255053437)
          ·
            refine ⟨1762943552837366720645039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4701182807566311255053437 1762943552837366720645039)
            ·
              refine ⟨2644415329256050080967559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762943552837366720645039 2644415329256050080967559)
              ·
                refine ⟨3966622993884075121451339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644415329256050080967559 3966622993884075121451339)
                ·
                  refine ⟨5949934490826112682177009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966622993884075121451339 5949934490826112682177009)
                  ·
                    refine ⟨4462450868119584511632757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5949934490826112682177009 4462450868119584511632757)
                    ·
                      refine ⟨418354768886211047965571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4462450868119584511632757 418354768886211047965571)
                      ·
                        rfl

theorem cell23_814743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_814743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814743 prefixEnd_814743 := by exact prefixLift 814743
  have htrace : WordTrace (prefixWord ++ tailWord_814743) baseStart_814743 baseEnd_814743 := by
    simpa [prefixWord, tailWord_814743, baseEnd_814743] using wordTrace_append hprefix tailTrace_814743
  have hstable : (prefixWord ++ tailWord_814743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814743).length < 2 ^ (prefixWord ++ tailWord_814743).sum := by decide
  have hdescent : baseEnd_814743 < baseStart_814743 := by decide
  rcases family_descends (prefixWord ++ tailWord_814743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814748 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_814748 : Nat := 118140960795 + 814748 * 2 ^ 59
def prefixEnd_814748 : Nat := 4983230072969 + 3 ^ 40 * 814748 * 2
def baseEnd_814748 : Nat := 418357336289483528403049

theorem tailTrace_814748 : CollatzResearch.WordTrace tailWord_814748 prefixEnd_814748 418357336289483528403049 := by
  unfold tailWord_814748
  simp only [CollatzResearch.WordTrace]
  refine ⟨14858150426157309362690449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19810867234876412483587265 14858150426157309362690449)
  ·
    refine ⟨11143612819617982022017837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14858150426157309362690449 11143612819617982022017837)
    ·
      refine ⟨4178854807356743258256689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11143612819617982022017837 4178854807356743258256689)
      ·
        refine ⟨3134141105517557443692517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4178854807356743258256689 3134141105517557443692517)
        ·
          refine ⟨587651457284542020692347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3134141105517557443692517 587651457284542020692347)
          ·
            refine ⟨881477185926813031038521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587651457284542020692347 881477185926813031038521)
            ·
              refine ⟨661107889445109773278891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881477185926813031038521 661107889445109773278891)
              ·
                refine ⟨991661834167664659918337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661107889445109773278891 991661834167664659918337)
                ·
                  refine ⟨743746375625748494938753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 991661834167664659918337 743746375625748494938753)
                  ·
                    refine ⟨557809781719311371204065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 743746375625748494938753 557809781719311371204065)
                    ·
                      refine ⟨418357336289483528403049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 557809781719311371204065 418357336289483528403049)
                      ·
                        rfl

theorem cell23_814748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_814748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814748 prefixEnd_814748 := by exact prefixLift 814748
  have htrace : WordTrace (prefixWord ++ tailWord_814748) baseStart_814748 baseEnd_814748 := by
    simpa [prefixWord, tailWord_814748, baseEnd_814748] using wordTrace_append hprefix tailTrace_814748
  have hstable : (prefixWord ++ tailWord_814748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814748).length < 2 ^ (prefixWord ++ tailWord_814748).sum := by decide
  have hdescent : baseEnd_814748 < baseStart_814748 := by decide
  rcases family_descends (prefixWord ++ tailWord_814748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814776 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 10]
def baseStart_814776 : Nat := 118140960795 + 814776 * 2 ^ 59
def prefixEnd_814776 : Nat := 4983230072969 + 3 ^ 40 * 814776 * 2
def baseEnd_814776 : Nat := 46485745971978824316991

theorem tailTrace_814776 : CollatzResearch.WordTrace tailWord_814776 prefixEnd_814776 46485745971978824316991 := by
  unfold tailWord_814776
  simp only [CollatzResearch.WordTrace]
  refine ⟨14858661048106589753700091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19811548064142119671600121 14858661048106589753700091)
  ·
    refine ⟨22287991572159884630550137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14858661048106589753700091 22287991572159884630550137)
    ·
      refine ⟨16715993679119913472912603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22287991572159884630550137 16715993679119913472912603)
      ·
        refine ⟨25073990518679870209368905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16715993679119913472912603 25073990518679870209368905)
        ·
          refine ⟨18805492889009902657026679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25073990518679870209368905 18805492889009902657026679)
          ·
            refine ⟨28208239333514853985540019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18805492889009902657026679 28208239333514853985540019)
            ·
              refine ⟨42312359000272280978310029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28208239333514853985540019 42312359000272280978310029)
              ·
                refine ⟨15867134625102105366866261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42312359000272280978310029 15867134625102105366866261)
                ·
                  refine ⟨46485745971978824316991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 15867134625102105366866261 46485745971978824316991)
                  ·
                    rfl

theorem cell23_814776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 10].length) (baseStart_814776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814776 prefixEnd_814776 := by exact prefixLift 814776
  have htrace : WordTrace (prefixWord ++ tailWord_814776) baseStart_814776 baseEnd_814776 := by
    simpa [prefixWord, tailWord_814776, baseEnd_814776] using wordTrace_append hprefix tailTrace_814776
  have hstable : (prefixWord ++ tailWord_814776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814776).length < 2 ^ (prefixWord ++ tailWord_814776).sum := by decide
  have hdescent : baseEnd_814776 < baseStart_814776 := by decide
  rcases family_descends (prefixWord ++ tailWord_814776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814843 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 4]
def baseStart_814843 : Nat := 118140960795 + 814843 * 2 ^ 59
def prefixEnd_814843 : Nat := 4983230072969 + 3 ^ 40 * 814843 * 2
def baseEnd_814843 : Nat := 418406116951660656715111

theorem tailTrace_814843 : CollatzResearch.WordTrace tailWord_814843 prefixEnd_814843 418406116951660656715111 := by
  unfold tailWord_814843
  simp only [CollatzResearch.WordTrace]
  refine ⟨29719765786970449950089183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19813177191313633300059455 29719765786970449950089183)
  ·
    refine ⟨44579648680455674925133775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29719765786970449950089183 44579648680455674925133775)
    ·
      refine ⟨66869473020683512387700663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44579648680455674925133775 66869473020683512387700663)
      ·
        refine ⟨100304209531025268581550995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66869473020683512387700663 100304209531025268581550995)
        ·
          refine ⟨150456314296537902872326493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100304209531025268581550995 150456314296537902872326493)
          ·
            refine ⟨56421117861201713577122435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150456314296537902872326493 56421117861201713577122435)
            ·
              refine ⟨84631676791802570365683653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56421117861201713577122435 84631676791802570365683653)
              ·
                refine ⟨15868439398462981943565685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84631676791802570365683653 15868439398462981943565685)
                ·
                  refine ⟨1487666193605904557209283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15868439398462981943565685 1487666193605904557209283)
                  ·
                    refine ⟨2231499290408856835813925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1487666193605904557209283 2231499290408856835813925)
                    ·
                      refine ⟨418406116951660656715111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2231499290408856835813925 418406116951660656715111)
                      ·
                        rfl

theorem cell23_814843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 4].length) (baseStart_814843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814843 prefixEnd_814843 := by exact prefixLift 814843
  have htrace : WordTrace (prefixWord ++ tailWord_814843) baseStart_814843 baseEnd_814843 := by
    simpa [prefixWord, tailWord_814843, baseEnd_814843] using wordTrace_append hprefix tailTrace_814843
  have hstable : (prefixWord ++ tailWord_814843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814843).length < 2 ^ (prefixWord ++ tailWord_814843).sum := by decide
  have hdescent : baseEnd_814843 < baseStart_814843 := by decide
  rcases family_descends (prefixWord ++ tailWord_814843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814863 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 3]
def baseStart_814863 : Nat := 118140960795 + 814863 * 2 ^ 59
def prefixEnd_814863 : Nat := 4983230072969 + 3 ^ 40 * 814863 * 2
def baseEnd_814863 : Nat := 418416386564750578465019

theorem tailTrace_814863 : CollatzResearch.WordTrace tailWord_814863 prefixEnd_814863 418416386564750578465019 := by
  unfold tailWord_814863
  simp only [CollatzResearch.WordTrace]
  refine ⟨29720495246897993365817243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19813663497931995577211495 29720495246897993365817243)
  ·
    refine ⟨44580742870346990048725865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29720495246897993365817243 44580742870346990048725865)
    ·
      refine ⟨33435557152760242536544399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44580742870346990048725865 33435557152760242536544399)
      ·
        refine ⟨50153335729140363804816599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33435557152760242536544399 50153335729140363804816599)
        ·
          refine ⟨75230003593710545707224899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50153335729140363804816599 75230003593710545707224899)
          ·
            refine ⟨112845005390565818560837349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75230003593710545707224899 112845005390565818560837349)
            ·
              refine ⟨21158438510731090980157003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112845005390565818560837349 21158438510731090980157003)
              ·
                refine ⟨31737657766096636470235505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21158438510731090980157003 31737657766096636470235505)
                ·
                  refine ⟨23803243324572477352676629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31737657766096636470235505 23803243324572477352676629)
                  ·
                    refine ⟨1115777030839334875906717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23803243324572477352676629 1115777030839334875906717)
                    ·
                      refine ⟨418416386564750578465019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1115777030839334875906717 418416386564750578465019)
                      ·
                        rfl

theorem cell23_814863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 3].length) (baseStart_814863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814863 prefixEnd_814863 := by exact prefixLift 814863
  have htrace : WordTrace (prefixWord ++ tailWord_814863) baseStart_814863 baseEnd_814863 := by
    simpa [prefixWord, tailWord_814863, baseEnd_814863] using wordTrace_append hprefix tailTrace_814863
  have hstable : (prefixWord ++ tailWord_814863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814863).length < 2 ^ (prefixWord ++ tailWord_814863).sum := by decide
  have hdescent : baseEnd_814863 < baseStart_814863 := by decide
  rcases family_descends (prefixWord ++ tailWord_814863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814897 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 1, 2, 3]
def baseStart_814897 : Nat := 118140960795 + 814897 * 2 ^ 59
def prefixEnd_814897 : Nat := 4983230072969 + 3 ^ 40 * 814897 * 2
def baseEnd_814897 : Nat := 418433844907003445439863

theorem tailTrace_814897 : CollatzResearch.WordTrace tailWord_814897 prefixEnd_814897 418433844907003445439863 := by
  unfold tailWord_814897
  simp only [CollatzResearch.WordTrace]
  refine ⟨29721735328774817172554945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19814490219183211448369963 29721735328774817172554945)
  ·
    refine ⟨22291301496581112879416209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29721735328774817172554945 22291301496581112879416209)
    ·
      refine ⟨16718476122435834659562157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22291301496581112879416209 16718476122435834659562157)
      ·
        refine ⟨6269428545913437997335809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16718476122435834659562157 6269428545913437997335809)
        ·
          refine ⟨4702071409435078498001857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6269428545913437997335809 4702071409435078498001857)
          ·
            refine ⟨3526553557076308873501393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4702071409435078498001857 3526553557076308873501393)
            ·
              refine ⟨2644915167807231655126045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3526553557076308873501393 2644915167807231655126045)
              ·
                refine ⟨991843187927711870672267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2644915167807231655126045 991843187927711870672267)
                ·
                  refine ⟨1487764781891567806008401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991843187927711870672267 1487764781891567806008401)
                  ·
                    refine ⟨1115823586418675854506301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1487764781891567806008401 1115823586418675854506301)
                    ·
                      refine ⟨418433844907003445439863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1115823586418675854506301 418433844907003445439863)
                      ·
                        rfl

theorem cell23_814897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_814897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814897 prefixEnd_814897 := by exact prefixLift 814897
  have htrace : WordTrace (prefixWord ++ tailWord_814897) baseStart_814897 baseEnd_814897 := by
    simpa [prefixWord, tailWord_814897, baseEnd_814897] using wordTrace_append hprefix tailTrace_814897
  have hstable : (prefixWord ++ tailWord_814897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814897).length < 2 ^ (prefixWord ++ tailWord_814897).sum := by decide
  have hdescent : baseEnd_814897 < baseStart_814897 := by decide
  rcases family_descends (prefixWord ++ tailWord_814897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814900 : List Nat := [2, 5, 1, 1, 2, 1, 11]
def baseStart_814900 : Nat := 118140960795 + 814900 * 2 ^ 59
def prefixEnd_814900 : Nat := 4983230072969 + 3 ^ 40 * 814900 * 2
def baseEnd_814900 : Nat := 5165868954925517700029

theorem tailTrace_814900 : CollatzResearch.WordTrace tailWord_814900 prefixEnd_814900 5165868954925517700029 := by
  unfold tailWord_814900
  simp only [CollatzResearch.WordTrace]
  refine ⟨14860922373881974342457077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19814563165175965789942769 14860922373881974342457077)
  ·
    refine ⟨1393211472551435094605351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14860922373881974342457077 1393211472551435094605351)
    ·
      refine ⟨2089817208827152641908027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393211472551435094605351 2089817208827152641908027)
      ·
        refine ⟨3134725813240728962862041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089817208827152641908027 3134725813240728962862041)
        ·
          refine ⟨2351044359930546722146531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3134725813240728962862041 2351044359930546722146531)
          ·
            refine ⟨3526566539895820083219797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351044359930546722146531 3526566539895820083219797)
            ·
              refine ⟨5165868954925517700029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3526566539895820083219797 5165868954925517700029)
              ·
                rfl

theorem cell23_814900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 11].length) (baseStart_814900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814900 prefixEnd_814900 := by exact prefixLift 814900
  have htrace : WordTrace (prefixWord ++ tailWord_814900) baseStart_814900 baseEnd_814900 := by
    simpa [prefixWord, tailWord_814900, baseEnd_814900] using wordTrace_append hprefix tailTrace_814900
  have hstable : (prefixWord ++ tailWord_814900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814900).length < 2 ^ (prefixWord ++ tailWord_814900).sum := by decide
  have hdescent : baseEnd_814900 < baseStart_814900 := by decide
  rcases family_descends (prefixWord ++ tailWord_814900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814911 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 3, 2, 2]
def baseStart_814911 : Nat := 118140960795 + 814911 * 2 ^ 59
def prefixEnd_814911 : Nat := 4983230072969 + 3 ^ 40 * 814911 * 2
def baseEnd_814911 : Nat := 418441033636166390664799

theorem tailTrace_814911 : CollatzResearch.WordTrace tailWord_814911 prefixEnd_814911 418441033636166390664799 := by
  unfold tailWord_814911
  simp only [CollatzResearch.WordTrace]
  refine ⟨29722245950724097563564587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19814830633816065042376391 29722245950724097563564587)
  ·
    refine ⟨44583368926086146345346881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29722245950724097563564587 44583368926086146345346881)
    ·
      refine ⟨33437526694564609759010161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44583368926086146345346881 33437526694564609759010161)
      ·
        refine ⟨25078145020923457319257621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33437526694564609759010161 25078145020923457319257621)
        ·
          refine ⟨1175538047855787061840201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25078145020923457319257621 1175538047855787061840201)
          ·
            refine ⟨881653535891840296380151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1175538047855787061840201 881653535891840296380151)
            ·
              refine ⟨1322480303837760444570227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881653535891840296380151 1322480303837760444570227)
              ·
                refine ⟨1983720455756640666855341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322480303837760444570227 1983720455756640666855341)
                ·
                  refine ⟨743895170908740250070753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1983720455756640666855341 743895170908740250070753)
                  ·
                    refine ⟨557921378181555187553065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 743895170908740250070753 557921378181555187553065)
                    ·
                      refine ⟨418441033636166390664799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 557921378181555187553065 418441033636166390664799)
                      ·
                        rfl

theorem cell23_814911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_814911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814911 prefixEnd_814911 := by exact prefixLift 814911
  have htrace : WordTrace (prefixWord ++ tailWord_814911) baseStart_814911 baseEnd_814911 := by
    simpa [prefixWord, tailWord_814911, baseEnd_814911] using wordTrace_append hprefix tailTrace_814911
  have hstable : (prefixWord ++ tailWord_814911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814911).length < 2 ^ (prefixWord ++ tailWord_814911).sum := by decide
  have hdescent : baseEnd_814911 < baseStart_814911 := by decide
  rcases family_descends (prefixWord ++ tailWord_814911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814937 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 3, 3, 2]
def baseStart_814937 : Nat := 118140960795 + 814937 * 2 ^ 59
def prefixEnd_814937 : Nat := 4983230072969 + 3 ^ 40 * 814937 * 2
def baseEnd_814937 : Nat := 418454384133183288939679

theorem tailTrace_814937 : CollatzResearch.WordTrace tailWord_814937 prefixEnd_814937 418454384133183288939679 := by
  unfold tailWord_814937
  simp only [CollatzResearch.WordTrace]
  refine ⟨29723194248629904004011065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19815462832419936002674043 29723194248629904004011065)
  ·
    refine ⟨22292395686472428003008299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29723194248629904004011065 22292395686472428003008299)
    ·
      refine ⟨33438593529708642004512449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22292395686472428003008299 33438593529708642004512449)
      ·
        refine ⟨25078945147281481503384337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33438593529708642004512449 25078945147281481503384337)
        ·
          refine ⟨18809208860461111127538253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25078945147281481503384337 18809208860461111127538253)
          ·
            refine ⟨7053453322672916672826845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18809208860461111127538253 7053453322672916672826845)
            ·
              refine ⟨2645044996002343752310067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7053453322672916672826845 2645044996002343752310067)
              ·
                refine ⟨3967567494003515628465101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645044996002343752310067 3967567494003515628465101)
                ·
                  refine ⟨1487837810251318360674413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3967567494003515628465101 1487837810251318360674413)
                  ·
                    refine ⟨557939178844244385252905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487837810251318360674413 557939178844244385252905)
                    ·
                      refine ⟨418454384133183288939679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 557939178844244385252905 418454384133183288939679)
                      ·
                        rfl

theorem cell23_814937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_814937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814937 prefixEnd_814937 := by exact prefixLift 814937
  have htrace : WordTrace (prefixWord ++ tailWord_814937) baseStart_814937 baseEnd_814937 := by
    simpa [prefixWord, tailWord_814937, baseEnd_814937] using wordTrace_append hprefix tailTrace_814937
  have hstable : (prefixWord ++ tailWord_814937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814937).length < 2 ^ (prefixWord ++ tailWord_814937).sum := by decide
  have hdescent : baseEnd_814937 < baseStart_814937 := by decide
  rcases family_descends (prefixWord ++ tailWord_814937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814963 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 6]
def baseStart_814963 : Nat := 118140960795 + 814963 * 2 ^ 59
def prefixEnd_814963 : Nat := 4983230072969 + 3 ^ 40 * 814963 * 2
def baseEnd_814963 : Nat := 418467734630200187214559

theorem tailTrace_814963 : CollatzResearch.WordTrace tailWord_814963 prefixEnd_814963 418467734630200187214559 := by
  unfold tailWord_814963
  simp only [CollatzResearch.WordTrace]
  refine ⟨29724142546535710444457543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19816095031023806962971695 29724142546535710444457543)
  ·
    refine ⟨44586213819803565666686315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29724142546535710444457543 44586213819803565666686315)
    ·
      refine ⟨66879320729705348500029473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44586213819803565666686315 66879320729705348500029473)
      ·
        refine ⟨50159490547279011375022105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66879320729705348500029473 50159490547279011375022105)
        ·
          refine ⟨37619617910459258531266579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50159490547279011375022105 37619617910459258531266579)
          ·
            refine ⟨56429426865688887796899869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37619617910459258531266579 56429426865688887796899869)
            ·
              refine ⟨21161035074633332923837451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56429426865688887796899869 21161035074633332923837451)
              ·
                refine ⟨31741552611949999385756177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21161035074633332923837451 31741552611949999385756177)
                ·
                  refine ⟨23806164458962499539317133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31741552611949999385756177 23806164458962499539317133)
                  ·
                    refine ⟨8927311672110937327243925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23806164458962499539317133 8927311672110937327243925)
                    ·
                      refine ⟨418467734630200187214559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8927311672110937327243925 418467734630200187214559)
                      ·
                        rfl

theorem cell23_814963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_814963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814963 prefixEnd_814963 := by exact prefixLift 814963
  have htrace : WordTrace (prefixWord ++ tailWord_814963) baseStart_814963 baseEnd_814963 := by
    simpa [prefixWord, tailWord_814963, baseEnd_814963] using wordTrace_append hprefix tailTrace_814963
  have hstable : (prefixWord ++ tailWord_814963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814963).length < 2 ^ (prefixWord ++ tailWord_814963).sum := by decide
  have hdescent : baseEnd_814963 < baseStart_814963 := by decide
  rcases family_descends (prefixWord ++ tailWord_814963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814970 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3]
def baseStart_814970 : Nat := 118140960795 + 814970 * 2 ^ 59
def prefixEnd_814970 : Nat := 4983230072969 + 3 ^ 40 * 814970 * 2
def baseEnd_814970 : Nat := 418471328994781659827027

theorem tailTrace_814970 : CollatzResearch.WordTrace tailWord_814970 prefixEnd_814970 418471328994781659827027 := by
  unfold tailWord_814970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431099464377587659990591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19816265238340233759974909 7431099464377587659990591)
  ·
    refine ⟨11146649196566381489985887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7431099464377587659990591 11146649196566381489985887)
    ·
      refine ⟨16719973794849572234978831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11146649196566381489985887 16719973794849572234978831)
      ·
        refine ⟨25079960692274358352468247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16719973794849572234978831 25079960692274358352468247)
        ·
          refine ⟨37619941038411537528702371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25079960692274358352468247 37619941038411537528702371)
          ·
            refine ⟨56429911557617306293053557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37619941038411537528702371 56429911557617306293053557)
            ·
              refine ⟨5290304208526622464973771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56429911557617306293053557 5290304208526622464973771)
              ·
                refine ⟨7935456312789933697460657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290304208526622464973771 7935456312789933697460657)
                ·
                  refine ⟨5951592234592450273095493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7935456312789933697460657 5951592234592450273095493)
                  ·
                    refine ⟨1115923543986084426205405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5951592234592450273095493 1115923543986084426205405)
                    ·
                      refine ⟨418471328994781659827027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1115923543986084426205405 418471328994781659827027)
                      ·
                        rfl

theorem cell23_814970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_814970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814970 prefixEnd_814970 := by exact prefixLift 814970
  have htrace : WordTrace (prefixWord ++ tailWord_814970) baseStart_814970 baseEnd_814970 := by
    simpa [prefixWord, tailWord_814970, baseEnd_814970] using wordTrace_append hprefix tailTrace_814970
  have hstable : (prefixWord ++ tailWord_814970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814970).length < 2 ^ (prefixWord ++ tailWord_814970).sum := by decide
  have hdescent : baseEnd_814970 < baseStart_814970 := by decide
  rcases family_descends (prefixWord ++ tailWord_814970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814980 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_814980 : Nat := 118140960795 + 814980 * 2 ^ 59
def prefixEnd_814980 : Nat := 4983230072969 + 3 ^ 40 * 814980 * 2
def baseEnd_814980 : Nat := 418476463801326620701981

theorem tailTrace_814980 : CollatzResearch.WordTrace tailWord_814980 prefixEnd_814980 418476463801326620701981 := by
  unfold tailWord_814980
  simp only [CollatzResearch.WordTrace]
  refine ⟨14862381293737061173913197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19816508391649414898550929 14862381293737061173913197)
  ·
    refine ⟨5573392985151397940217449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14862381293737061173913197 5573392985151397940217449)
    ·
      refine ⟨4180044738863548455163087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5573392985151397940217449 4180044738863548455163087)
      ·
        refine ⟨6270067108295322682744631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4180044738863548455163087 6270067108295322682744631)
        ·
          refine ⟨9405100662442984024116947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6270067108295322682744631 9405100662442984024116947)
          ·
            refine ⟨14107650993664476036175421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9405100662442984024116947 14107650993664476036175421)
            ·
              refine ⟨5290369122624178513565783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14107650993664476036175421 5290369122624178513565783)
              ·
                refine ⟨7935553683936267770348675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290369122624178513565783 7935553683936267770348675)
                ·
                  refine ⟨11903330525904401655523013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935553683936267770348675 11903330525904401655523013)
                  ·
                    refine ⟨2231874473607075310410565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11903330525904401655523013 2231874473607075310410565)
                    ·
                      refine ⟨418476463801326620701981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2231874473607075310410565 418476463801326620701981)
                      ·
                        rfl

theorem cell23_814980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_814980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_814980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_814980 prefixEnd_814980 := by exact prefixLift 814980
  have htrace : WordTrace (prefixWord ++ tailWord_814980) baseStart_814980 baseEnd_814980 := by
    simpa [prefixWord, tailWord_814980, baseEnd_814980] using wordTrace_append hprefix tailTrace_814980
  have hstable : (prefixWord ++ tailWord_814980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814980).length < 2 ^ (prefixWord ++ tailWord_814980).sum := by decide
  have hdescent : baseEnd_814980 < baseStart_814980 := by decide
  rcases family_descends (prefixWord ++ tailWord_814980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815040 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_815040 : Nat := 118140960795 + 815040 * 2 ^ 59
def prefixEnd_815040 : Nat := 4983230072969 + 3 ^ 40 * 815040 * 2
def baseEnd_815040 : Nat := 418507272640596385951705

theorem tailTrace_815040 : CollatzResearch.WordTrace tailWord_815040 prefixEnd_815040 418507272640596385951705 := by
  unfold tailWord_815040
  simp only [CollatzResearch.WordTrace]
  refine ⟨14863475483628376297505287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19817967311504501730007049 14863475483628376297505287)
  ·
    refine ⟨22295213225442564446257931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14863475483628376297505287 22295213225442564446257931)
    ·
      refine ⟨33442819838163846669386897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22295213225442564446257931 33442819838163846669386897)
      ·
        refine ⟨25082114878622885002040173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33442819838163846669386897 25082114878622885002040173)
        ·
          refine ⟨9405793079483581875765065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25082114878622885002040173 9405793079483581875765065)
          ·
            refine ⟨7054344809612686406823799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9405793079483581875765065 7054344809612686406823799)
            ·
              refine ⟨10581517214419029610235699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7054344809612686406823799 10581517214419029610235699)
              ·
                refine ⟨15872275821628544415353549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10581517214419029610235699 15872275821628544415353549)
                ·
                  refine ⟨5952103433110704155757581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15872275821628544415353549 5952103433110704155757581)
                  ·
                    refine ⟨2232038787416514058409093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5952103433110704155757581 2232038787416514058409093)
                    ·
                      refine ⟨418507272640596385951705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2232038787416514058409093 418507272640596385951705)
                      ·
                        rfl

theorem cell23_815040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_815040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815040 prefixEnd_815040 := by exact prefixLift 815040
  have htrace : WordTrace (prefixWord ++ tailWord_815040) baseStart_815040 baseEnd_815040 := by
    simpa [prefixWord, tailWord_815040, baseEnd_815040] using wordTrace_append hprefix tailTrace_815040
  have hstable : (prefixWord ++ tailWord_815040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815040).length < 2 ^ (prefixWord ++ tailWord_815040).sum := by decide
  have hdescent : baseEnd_815040 < baseStart_815040 := by decide
  rcases family_descends (prefixWord ++ tailWord_815040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815057 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 4, 4, 2]
def baseStart_815057 : Nat := 118140960795 + 815057 * 2 ^ 59
def prefixEnd_815057 : Nat := 4983230072969 + 3 ^ 40 * 815057 * 2
def baseEnd_815057 : Nat := 418516001811722819439127

theorem tailTrace_815057 : CollatzResearch.WordTrace tailWord_815057 prefixEnd_815057 418516001811722819439127 := by
  unfold tailWord_815057
  simp only [CollatzResearch.WordTrace]
  refine ⟨29727571008195164498379425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19818380672130109665586283 29727571008195164498379425)
  ·
    refine ⟨22295678256146373373784569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29727571008195164498379425 22295678256146373373784569)
    ·
      refine ⟨16721758692109780030338427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22295678256146373373784569 16721758692109780030338427)
      ·
        refine ⟨25082638038164670045507641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16721758692109780030338427 25082638038164670045507641)
        ·
          refine ⟨18811978528623502534130731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25082638038164670045507641 18811978528623502534130731)
          ·
            refine ⟨28217967792935253801196097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18811978528623502534130731 28217967792935253801196097)
            ·
              refine ⟨21163475844701440350897073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28217967792935253801196097 21163475844701440350897073)
              ·
                refine ⟨15872606883526080263172805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21163475844701440350897073 15872606883526080263172805)
                ·
                  refine ⟨2976113790661140049344901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15872606883526080263172805 2976113790661140049344901)
                  ·
                    refine ⟨558021335748963759252169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2976113790661140049344901 558021335748963759252169)
                    ·
                      refine ⟨418516001811722819439127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558021335748963759252169 418516001811722819439127)
                      ·
                        rfl

theorem cell23_815057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_815057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815057 prefixEnd_815057 := by exact prefixLift 815057
  have htrace : WordTrace (prefixWord ++ tailWord_815057) baseStart_815057 baseEnd_815057 := by
    simpa [prefixWord, tailWord_815057, baseEnd_815057] using wordTrace_append hprefix tailTrace_815057
  have hstable : (prefixWord ++ tailWord_815057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815057).length < 2 ^ (prefixWord ++ tailWord_815057).sum := by decide
  have hdescent : baseEnd_815057 < baseStart_815057 := by decide
  rcases family_descends (prefixWord ++ tailWord_815057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815058 : List Nat := [3, 2, 2, 3, 3, 1, 1, 3, 5]
def baseStart_815058 : Nat := 118140960795 + 815058 * 2 ^ 59
def prefixEnd_815058 : Nat := 4983230072969 + 3 ^ 40 * 815058 * 2
def baseEnd_815058 : Nat := 46501835032486368391847

theorem tailTrace_815058 : CollatzResearch.WordTrace tailWord_815058 prefixEnd_815058 46501835032486368391847 := by
  unfold tailWord_815058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431901870297885417291457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19818404987461027779443885 7431901870297885417291457)
  ·
    refine ⟨5573926402723414062968593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7431901870297885417291457 5573926402723414062968593)
    ·
      refine ⟨4180444802042560547226445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5573926402723414062968593 4180444802042560547226445)
      ·
        refine ⟨1567666800765960205209917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4180444802042560547226445 1567666800765960205209917)
        ·
          refine ⟨587875050287235076953719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1567666800765960205209917 587875050287235076953719)
          ·
            refine ⟨881812575430852615430579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587875050287235076953719 881812575430852615430579)
            ·
              refine ⟨1322718863146278923145869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881812575430852615430579 1322718863146278923145869)
              ·
                refine ⟨496019573679854596179701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1322718863146278923145869 496019573679854596179701)
                ·
                  refine ⟨46501835032486368391847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 496019573679854596179701 46501835032486368391847)
                  ·
                    rfl

theorem cell23_815058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_815058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815058 prefixEnd_815058 := by exact prefixLift 815058
  have htrace : WordTrace (prefixWord ++ tailWord_815058) baseStart_815058 baseEnd_815058 := by
    simpa [prefixWord, tailWord_815058, baseEnd_815058] using wordTrace_append hprefix tailTrace_815058
  have hstable : (prefixWord ++ tailWord_815058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815058).length < 2 ^ (prefixWord ++ tailWord_815058).sum := by decide
  have hdescent : baseEnd_815058 < baseStart_815058 := by decide
  rcases family_descends (prefixWord ++ tailWord_815058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815084 : List Nat := [2, 2, 1, 1, 2, 1, 1, 8, 1, 4]
def baseStart_815084 : Nat := 118140960795 + 815084 * 2 ^ 59
def prefixEnd_815084 : Nat := 4983230072969 + 3 ^ 40 * 815084 * 2
def baseEnd_815084 : Nat := 139509955263131404600501

theorem tailTrace_815084 : CollatzResearch.WordTrace tailWord_815084 prefixEnd_815084 139509955263131404600501 := by
  unfold tailWord_815084
  simp only [CollatzResearch.WordTrace]
  refine ⟨14864277889548674054806153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19819037186064898739741537 14864277889548674054806153)
  ·
    refine ⟨11148208417161505541104615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14864277889548674054806153 11148208417161505541104615)
    ·
      refine ⟨16722312625742258311656923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11148208417161505541104615 16722312625742258311656923)
      ·
        refine ⟨25083468938613387467485385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16722312625742258311656923 25083468938613387467485385)
        ·
          refine ⟨18812601703960040600614039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25083468938613387467485385 18812601703960040600614039)
          ·
            refine ⟨28218902555940060900921059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18812601703960040600614039 28218902555940060900921059)
            ·
              refine ⟨42328353833910091351381589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28218902555940060900921059 42328353833910091351381589)
              ·
                refine ⟨496035396491133883024003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 42328353833910091351381589 496035396491133883024003)
                ·
                  refine ⟨744053094736700824536005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496035396491133883024003 744053094736700824536005)
                  ·
                    refine ⟨139509955263131404600501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 744053094736700824536005 139509955263131404600501)
                    ·
                      rfl

theorem cell23_815084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_815084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815084 prefixEnd_815084 := by exact prefixLift 815084
  have htrace : WordTrace (prefixWord ++ tailWord_815084) baseStart_815084 baseEnd_815084 := by
    simpa [prefixWord, tailWord_815084, baseEnd_815084] using wordTrace_append hprefix tailTrace_815084
  have hstable : (prefixWord ++ tailWord_815084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815084).length < 2 ^ (prefixWord ++ tailWord_815084).sum := by decide
  have hdescent : baseEnd_815084 < baseStart_815084 := by decide
  rcases family_descends (prefixWord ++ tailWord_815084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815097 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 6]
def baseStart_815097 : Nat := 118140960795 + 815097 * 2 ^ 59
def prefixEnd_815097 : Nat := 4983230072969 + 3 ^ 40 * 815097 * 2
def baseEnd_815097 : Nat := 46504060115322518104327

theorem tailTrace_815097 : CollatzResearch.WordTrace tailWord_815097 prefixEnd_815097 46504060115322518104327 := by
  unfold tailWord_815097
  simp only [CollatzResearch.WordTrace]
  refine ⟨29729029928050251329835545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19819353285366834219890363 29729029928050251329835545)
  ·
    refine ⟨22296772446037688497376659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29729029928050251329835545 22296772446037688497376659)
    ·
      refine ⟨33445158669056532746064989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22296772446037688497376659 33445158669056532746064989)
      ·
        refine ⟨12541934500896199779774371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33445158669056532746064989 12541934500896199779774371)
        ·
          refine ⟨18812901751344299669661557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12541934500896199779774371 18812901751344299669661557)
          ·
            refine ⟨1763709539188528094030771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18812901751344299669661557 1763709539188528094030771)
            ·
              refine ⟨2645564308782792141046157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763709539188528094030771 2645564308782792141046157)
              ·
                refine ⟨992086615793547052892309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2645564308782792141046157 992086615793547052892309)
                ·
                  refine ⟨46504060115322518104327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 992086615793547052892309 46504060115322518104327)
                  ·
                    rfl

theorem cell23_815097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 6].length) (baseStart_815097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815097 prefixEnd_815097 := by exact prefixLift 815097
  have htrace : WordTrace (prefixWord ++ tailWord_815097) baseStart_815097 baseEnd_815097 := by
    simpa [prefixWord, tailWord_815097, baseEnd_815097] using wordTrace_append hprefix tailTrace_815097
  have hstable : (prefixWord ++ tailWord_815097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815097).length < 2 ^ (prefixWord ++ tailWord_815097).sum := by decide
  have hdescent : baseEnd_815097 < baseStart_815097 := by decide
  rcases family_descends (prefixWord ++ tailWord_815097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815157 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_815157 : Nat := 118140960795 + 815157 * 2 ^ 59
def prefixEnd_815157 : Nat := 4983230072969 + 3 ^ 40 * 815157 * 2
def baseEnd_815157 : Nat := 139522449959057476062889

theorem tailTrace_815157 : CollatzResearch.WordTrace tailWord_815157 prefixEnd_815157 139522449959057476062889 := by
  unfold tailWord_815157
  simp only [CollatzResearch.WordTrace]
  refine ⟨29731218307832881577019725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19820812205221921051346483 29731218307832881577019725)
  ·
    refine ⟨11149206865437330591382397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29731218307832881577019725 11149206865437330591382397)
    ·
      refine ⟨4180952574538998971768399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11149206865437330591382397 4180952574538998971768399)
      ·
        refine ⟨6271428861808498457652599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4180952574538998971768399 6271428861808498457652599)
        ·
          refine ⟨9407143292712747686478899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6271428861808498457652599 9407143292712747686478899)
          ·
            refine ⟨14110714939069121529718349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9407143292712747686478899 14110714939069121529718349)
            ·
              refine ⟨5291518102150920573644381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14110714939069121529718349 5291518102150920573644381)
              ·
                refine ⟨1984319288306595215116643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5291518102150920573644381 1984319288306595215116643)
                ·
                  refine ⟨2976478932459892822674965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984319288306595215116643 2976478932459892822674965)
                  ·
                    refine ⟨139522449959057476062889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2976478932459892822674965 139522449959057476062889)
                    ·
                      rfl

theorem cell23_815157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_815157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815157 prefixEnd_815157 := by exact prefixLift 815157
  have htrace : WordTrace (prefixWord ++ tailWord_815157) baseStart_815157 baseEnd_815157 := by
    simpa [prefixWord, tailWord_815157, baseEnd_815157] using wordTrace_append hprefix tailTrace_815157
  have hstable : (prefixWord ++ tailWord_815157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815157).length < 2 ^ (prefixWord ++ tailWord_815157).sum := by decide
  have hdescent : baseEnd_815157 < baseStart_815157 := by decide
  rcases family_descends (prefixWord ++ tailWord_815157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815164 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_815164 : Nat := 118140960795 + 815164 * 2 ^ 59
def prefixEnd_815164 : Nat := 4983230072969 + 3 ^ 40 * 815164 * 2
def baseEnd_815164 : Nat := 418570944241753900801135

theorem tailTrace_815164 : CollatzResearch.WordTrace tailWord_815164 prefixEnd_815164 418570944241753900801135 := by
  unfold tailWord_815164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14865736809403760886262273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19820982412538347848349697 14865736809403760886262273)
  ·
    refine ⟨11149302607052820664696705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14865736809403760886262273 11149302607052820664696705)
    ·
      refine ⟨8361976955289615498522529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11149302607052820664696705 8361976955289615498522529)
      ·
        refine ⟨6271482716467211623891897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8361976955289615498522529 6271482716467211623891897)
        ·
          refine ⟨4703612037350408717918923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6271482716467211623891897 4703612037350408717918923)
          ·
            refine ⟨7055418056025613076878385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703612037350408717918923 7055418056025613076878385)
            ·
              refine ⟨5291563542019209807658789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7055418056025613076878385 5291563542019209807658789)
              ·
                refine ⟨992168164128601838936023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5291563542019209807658789 992168164128601838936023)
                ·
                  refine ⟨1488252246192902758404035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992168164128601838936023 1488252246192902758404035)
                  ·
                    refine ⟨2232378369289354137606053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1488252246192902758404035 2232378369289354137606053)
                    ·
                      refine ⟨418570944241753900801135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2232378369289354137606053 418570944241753900801135)
                      ·
                        rfl

theorem cell23_815164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_815164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815164 prefixEnd_815164 := by exact prefixLift 815164
  have htrace : WordTrace (prefixWord ++ tailWord_815164) baseStart_815164 baseEnd_815164 := by
    simpa [prefixWord, tailWord_815164, baseEnd_815164] using wordTrace_append hprefix tailTrace_815164
  have hstable : (prefixWord ++ tailWord_815164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815164).length < 2 ^ (prefixWord ++ tailWord_815164).sum := by decide
  have hdescent : baseEnd_815164 < baseStart_815164 := by decide
  rcases family_descends (prefixWord ++ tailWord_815164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815177 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 4]
def baseStart_815177 : Nat := 118140960795 + 815177 * 2 ^ 59
def prefixEnd_815177 : Nat := 4983230072969 + 3 ^ 40 * 815177 * 2
def baseEnd_815177 : Nat := 418577619490262349938575

theorem tailTrace_815177 : CollatzResearch.WordTrace tailWord_815177 prefixEnd_815177 418577619490262349938575 := by
  unfold tailWord_815177
  simp only [CollatzResearch.WordTrace]
  refine ⟨29731947767760424992747785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19821298511840283328498523 29731947767760424992747785)
  ·
    refine ⟨22298960825820318744560839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29731947767760424992747785 22298960825820318744560839)
    ·
      refine ⟨33448441238730478116841259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22298960825820318744560839 33448441238730478116841259)
      ·
        refine ⟨50172661858095717175261889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33448441238730478116841259 50172661858095717175261889)
        ·
          refine ⟨37629496393571787881446417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50172661858095717175261889 37629496393571787881446417)
          ·
            refine ⟨28222122295178840911084813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37629496393571787881446417 28222122295178840911084813)
            ·
              refine ⟨10583295860692065341656805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28222122295178840911084813 10583295860692065341656805)
              ·
                refine ⟨1984367973879762251560651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10583295860692065341656805 1984367973879762251560651)
                ·
                  refine ⟨2976551960819643377340977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984367973879762251560651 2976551960819643377340977)
                  ·
                    refine ⟨2232413970614732533005733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2976551960819643377340977 2232413970614732533005733)
                    ·
                      refine ⟨418577619490262349938575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2232413970614732533005733 418577619490262349938575)
                      ·
                        rfl

theorem cell23_815177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_815177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815177 prefixEnd_815177 := by exact prefixLift 815177
  have htrace : WordTrace (prefixWord ++ tailWord_815177) baseStart_815177 baseEnd_815177 := by
    simpa [prefixWord, tailWord_815177, baseEnd_815177] using wordTrace_append hprefix tailTrace_815177
  have hstable : (prefixWord ++ tailWord_815177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815177).length < 2 ^ (prefixWord ++ tailWord_815177).sum := by decide
  have hdescent : baseEnd_815177 < baseStart_815177 := by decide
  rcases family_descends (prefixWord ++ tailWord_815177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815181 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_815181 : Nat := 118140960795 + 815181 * 2 ^ 59
def prefixEnd_815181 : Nat := 4983230072969 + 3 ^ 40 * 815181 * 2
def baseEnd_815181 : Nat := 418579673412880334288557

theorem tailTrace_815181 : CollatzResearch.WordTrace tailWord_815181 prefixEnd_815181 418579673412880334288557 := by
  unfold tailWord_815181
  simp only [CollatzResearch.WordTrace]
  refine ⟨29732093659745933675893397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19821395773163955783928931 29732093659745933675893397)
  ·
    refine ⟨1393691890300590641057503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29732093659745933675893397 1393691890300590641057503)
    ·
      refine ⟨2090537835450885961586255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393691890300590641057503 2090537835450885961586255)
      ·
        refine ⟨3135806753176328942379383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090537835450885961586255 3135806753176328942379383)
        ·
          refine ⟨4703710129764493413569075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135806753176328942379383 4703710129764493413569075)
          ·
            refine ⟨7055565194646740120353613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703710129764493413569075 7055565194646740120353613)
            ·
              refine ⟨2645836947992527545132605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7055565194646740120353613 2645836947992527545132605)
              ·
                refine ⟨992188855497197829424727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2645836947992527545132605 992188855497197829424727)
                ·
                  refine ⟨1488283283245796744137091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992188855497197829424727 1488283283245796744137091)
                  ·
                    refine ⟨2232424924868695116205637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1488283283245796744137091 2232424924868695116205637)
                    ·
                      refine ⟨418579673412880334288557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2232424924868695116205637 418579673412880334288557)
                      ·
                        rfl

theorem cell23_815181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_815181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815181 prefixEnd_815181 := by exact prefixLift 815181
  have htrace : WordTrace (prefixWord ++ tailWord_815181) baseStart_815181 baseEnd_815181 := by
    simpa [prefixWord, tailWord_815181, baseEnd_815181] using wordTrace_append hprefix tailTrace_815181
  have hstable : (prefixWord ++ tailWord_815181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815181).length < 2 ^ (prefixWord ++ tailWord_815181).sum := by decide
  have hdescent : baseEnd_815181 < baseStart_815181 := by decide
  rcases family_descends (prefixWord ++ tailWord_815181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815241 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 1, 3, 2]
def baseStart_815241 : Nat := 118140960795 + 815241 * 2 ^ 59
def prefixEnd_815241 : Nat := 4983230072969 + 3 ^ 40 * 815241 * 2
def baseEnd_815241 : Nat := 418610482252150099538281

theorem tailTrace_815241 : CollatzResearch.WordTrace tailWord_815241 prefixEnd_815241 418610482252150099538281 := by
  unfold tailWord_815241
  simp only [CollatzResearch.WordTrace]
  refine ⟨29734282039528563923077577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19822854693019042615385051 29734282039528563923077577)
  ·
    refine ⟨22300711529646422942308183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29734282039528563923077577 22300711529646422942308183)
    ·
      refine ⟨33451067294469634413462275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22300711529646422942308183 33451067294469634413462275)
      ·
        refine ⟨50176600941704451620193413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33451067294469634413462275 50176600941704451620193413)
        ·
          refine ⟨9408112676569584678786265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50176600941704451620193413 9408112676569584678786265)
          ·
            refine ⟨7056084507427188509089699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9408112676569584678786265 7056084507427188509089699)
            ·
              refine ⟨10584126761140782763634549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7056084507427188509089699 10584126761140782763634549)
              ·
                refine ⟨992261883856948384090739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10584126761140782763634549 992261883856948384090739)
                ·
                  refine ⟨1488392825785422576136109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992261883856948384090739 1488392825785422576136109)
                  ·
                    refine ⟨558147309669533466051041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1488392825785422576136109 558147309669533466051041)
                    ·
                      refine ⟨418610482252150099538281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558147309669533466051041 418610482252150099538281)
                      ·
                        rfl

theorem cell23_815241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 3, 2].length) (baseStart_815241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815241 prefixEnd_815241 := by exact prefixLift 815241
  have htrace : WordTrace (prefixWord ++ tailWord_815241) baseStart_815241 baseEnd_815241 := by
    simpa [prefixWord, tailWord_815241, baseEnd_815241] using wordTrace_append hprefix tailTrace_815241
  have hstable : (prefixWord ++ tailWord_815241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815241).length < 2 ^ (prefixWord ++ tailWord_815241).sum := by decide
  have hdescent : baseEnd_815241 < baseStart_815241 := by decide
  rcases family_descends (prefixWord ++ tailWord_815241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815265 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 2, 1, 3]
def baseStart_815265 : Nat := 118140960795 + 815265 * 2 ^ 59
def prefixEnd_815265 : Nat := 4983230072969 + 3 ^ 40 * 815265 * 2
def baseEnd_815265 : Nat := 418622805787858005638171

theorem tailTrace_815265 : CollatzResearch.WordTrace tailWord_815265 prefixEnd_815265 418622805787858005638171 := by
  unfold tailWord_815265
  simp only [CollatzResearch.WordTrace]
  refine ⟨29735157391441616021951249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19823438260961077347967499 29735157391441616021951249)
  ·
    refine ⟨22301368043581212016463437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29735157391441616021951249 22301368043581212016463437)
    ·
      refine ⟨8363013016342954506173789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22301368043581212016463437 8363013016342954506173789)
      ·
        refine ⟨3136129881128607939815171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8363013016342954506173789 3136129881128607939815171)
        ·
          refine ⟨4704194821692911909722757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136129881128607939815171 4704194821692911909722757)
          ·
            refine ⟨882036529067420983073017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4704194821692911909722757 882036529067420983073017)
            ·
              refine ⟨661527396800565737304763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882036529067420983073017 661527396800565737304763)
              ·
                refine ⟨992291095200848605957145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661527396800565737304763 992291095200848605957145)
                ·
                  refine ⟨744218321400636454467859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 992291095200848605957145 744218321400636454467859)
                  ·
                    refine ⟨1116327482100954681701789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 744218321400636454467859 1116327482100954681701789)
                    ·
                      refine ⟨418622805787858005638171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1116327482100954681701789 418622805787858005638171)
                      ·
                        rfl

theorem cell23_815265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_815265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815265 prefixEnd_815265 := by exact prefixLift 815265
  have htrace : WordTrace (prefixWord ++ tailWord_815265) baseStart_815265 baseEnd_815265 := by
    simpa [prefixWord, tailWord_815265, baseEnd_815265] using wordTrace_append hprefix tailTrace_815265
  have hstable : (prefixWord ++ tailWord_815265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815265).length < 2 ^ (prefixWord ++ tailWord_815265).sum := by decide
  have hdescent : baseEnd_815265 < baseStart_815265 := by decide
  rcases family_descends (prefixWord ++ tailWord_815265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815304 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_815304 : Nat := 118140960795 + 815304 * 2 ^ 59
def prefixEnd_815304 : Nat := 4983230072969 + 3 ^ 40 * 815304 * 2
def baseEnd_815304 : Nat := 418642831533383353050491

theorem tailTrace_815304 : CollatzResearch.WordTrace tailWord_815304 prefixEnd_815304 418642831533383353050491 := by
  unfold tailWord_815304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14868289919150162841310483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19824386558866883788413977 14868289919150162841310483)
  ·
    refine ⟨22302434878725244261965725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14868289919150162841310483 22302434878725244261965725)
    ·
      refine ⟨8363413079521966598237147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22302434878725244261965725 8363413079521966598237147)
      ·
        refine ⟨12545119619282949897355721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8363413079521966598237147 12545119619282949897355721)
        ·
          refine ⟨9408839714462212423016791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12545119619282949897355721 9408839714462212423016791)
          ·
            refine ⟨14113259571693318634525187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9408839714462212423016791 14113259571693318634525187)
            ·
              refine ⟨21169889357539977951787781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14113259571693318634525187 21169889357539977951787781)
              ·
                refine ⟨3969354254538745865960209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21169889357539977951787781 3969354254538745865960209)
                ·
                  refine ⟨2977015690904059399470157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3969354254538745865960209 2977015690904059399470157)
                  ·
                    refine ⟨1116380884089022274801309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2977015690904059399470157 1116380884089022274801309)
                    ·
                      refine ⟨418642831533383353050491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1116380884089022274801309 418642831533383353050491)
                      ·
                        rfl

theorem cell23_815304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_815304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815304 prefixEnd_815304 := by exact prefixLift 815304
  have htrace : WordTrace (prefixWord ++ tailWord_815304) baseStart_815304 baseEnd_815304 := by
    simpa [prefixWord, tailWord_815304, baseEnd_815304] using wordTrace_append hprefix tailTrace_815304
  have hstable : (prefixWord ++ tailWord_815304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815304).length < 2 ^ (prefixWord ++ tailWord_815304).sum := by decide
  have hdescent : baseEnd_815304 < baseStart_815304 := by decide
  rcases family_descends (prefixWord ++ tailWord_815304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815318 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_815318 : Nat := 118140960795 + 815318 * 2 ^ 59
def prefixEnd_815318 : Nat := 4983230072969 + 3 ^ 40 * 815318 * 2
def baseEnd_815318 : Nat := 418650020262546298275427

theorem tailTrace_815318 : CollatzResearch.WordTrace tailWord_815318 prefixEnd_815318 418650020262546298275427 := by
  unfold tailWord_815318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858568153765600379601913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19824726973499737382420405 1858568153765600379601913)
  ·
    refine ⟨1393926115324200284701435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1858568153765600379601913 1393926115324200284701435)
    ·
      refine ⟨2090889172986300427052153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393926115324200284701435 2090889172986300427052153)
      ·
        refine ⟨1568166879739725320289115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2090889172986300427052153 1568166879739725320289115)
        ·
          refine ⟨2352250319609587980433673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568166879739725320289115 2352250319609587980433673)
          ·
            refine ⟨1764187739707190985325255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2352250319609587980433673 1764187739707190985325255)
            ·
              refine ⟨2646281609560786477987883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764187739707190985325255 2646281609560786477987883)
              ·
                refine ⟨3969422414341179716981825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646281609560786477987883 3969422414341179716981825)
                ·
                  refine ⟨2977066810755884787736369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3969422414341179716981825 2977066810755884787736369)
                  ·
                    refine ⟨2232800108066913590802277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2977066810755884787736369 2232800108066913590802277)
                    ·
                      refine ⟨418650020262546298275427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2232800108066913590802277 418650020262546298275427)
                      ·
                        rfl

theorem cell23_815318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_815318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815318 prefixEnd_815318 := by exact prefixLift 815318
  have htrace : WordTrace (prefixWord ++ tailWord_815318) baseStart_815318 baseEnd_815318 := by
    simpa [prefixWord, tailWord_815318, baseEnd_815318] using wordTrace_append hprefix tailTrace_815318
  have hstable : (prefixWord ++ tailWord_815318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815318).length < 2 ^ (prefixWord ++ tailWord_815318).sum := by decide
  have hdescent : baseEnd_815318 < baseStart_815318 := by decide
  rcases family_descends (prefixWord ++ tailWord_815318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815337 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 2, 8]
def baseStart_815337 : Nat := 118140960795 + 815337 * 2 ^ 59
def prefixEnd_815337 : Nat := 4983230072969 + 3 ^ 40 * 815337 * 2
def baseEnd_815337 : Nat := 139553258798327241312613

theorem tailTrace_815337 : CollatzResearch.WordTrace tailWord_815337 prefixEnd_815337 139553258798327241312613 := by
  unfold tailWord_815337
  simp only [CollatzResearch.WordTrace]
  refine ⟨29737783447180772318572265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19825188964787181545714843 29737783447180772318572265)
  ·
    refine ⟨22303337585385579238929199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29737783447180772318572265 22303337585385579238929199)
    ·
      refine ⟨33455006378078368858393799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22303337585385579238929199 33455006378078368858393799)
      ·
        refine ⟨50182509567117553287590699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33455006378078368858393799 50182509567117553287590699)
        ·
          refine ⟨75273764350676329931386049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50182509567117553287590699 75273764350676329931386049)
          ·
            refine ⟨56455323263007247448539537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75273764350676329931386049 56455323263007247448539537)
            ·
              refine ⟨42341492447255435586404653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56455323263007247448539537 42341492447255435586404653)
              ·
                refine ⟨15878059667720788344901745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42341492447255435586404653 15878059667720788344901745)
                ·
                  refine ⟨11908544750790591258676309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15878059667720788344901745 11908544750790591258676309)
                  ·
                    refine ⟨139553258798327241312613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11908544750790591258676309 139553258798327241312613)
                    ·
                      rfl

theorem cell23_815337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_815337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815337 prefixEnd_815337 := by exact prefixLift 815337
  have htrace : WordTrace (prefixWord ++ tailWord_815337) baseStart_815337 baseEnd_815337 := by
    simpa [prefixWord, tailWord_815337, baseEnd_815337] using wordTrace_append hprefix tailTrace_815337
  have hstable : (prefixWord ++ tailWord_815337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815337).length < 2 ^ (prefixWord ++ tailWord_815337).sum := by decide
  have hdescent : baseEnd_815337 < baseStart_815337 := by decide
  rcases family_descends (prefixWord ++ tailWord_815337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815341 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_815341 : Nat := 118140960795 + 815341 * 2 ^ 59
def prefixEnd_815341 : Nat := 4983230072969 + 3 ^ 40 * 815341 * 2
def baseEnd_815341 : Nat := 139553943439199902762607

theorem tailTrace_815341 : CollatzResearch.WordTrace tailWord_815341 prefixEnd_815341 139553943439199902762607 := by
  unfold tailWord_815341
  simp only [CollatzResearch.WordTrace]
  refine ⟨29737929339166281001717877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19825286226110854001145251 29737929339166281001717877)
  ·
    refine ⟨2787930875546838843911051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29737929339166281001717877 2787930875546838843911051)
    ·
      refine ⟨4181896313320258265866577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2787930875546838843911051 4181896313320258265866577)
      ·
        refine ⟨3136422234990193699399933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4181896313320258265866577 3136422234990193699399933)
        ·
          refine ⟨1176158338121322637274975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3136422234990193699399933 1176158338121322637274975)
          ·
            refine ⟨1764237507181983955912463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176158338121322637274975 1764237507181983955912463)
            ·
              refine ⟨2646356260772975933868695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764237507181983955912463 2646356260772975933868695)
              ·
                refine ⟨3969534391159463900803043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646356260772975933868695 3969534391159463900803043)
                ·
                  refine ⟨5954301586739195851204565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969534391159463900803043 5954301586739195851204565)
                  ·
                    refine ⟨139553943439199902762607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5954301586739195851204565 139553943439199902762607)
                    ·
                      rfl

theorem cell23_815341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_815341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815341 prefixEnd_815341 := by exact prefixLift 815341
  have htrace : WordTrace (prefixWord ++ tailWord_815341) baseStart_815341 baseEnd_815341 := by
    simpa [prefixWord, tailWord_815341, baseEnd_815341] using wordTrace_append hprefix tailTrace_815341
  have hstable : (prefixWord ++ tailWord_815341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815341).length < 2 ^ (prefixWord ++ tailWord_815341).sum := by decide
  have hdescent : baseEnd_815341 < baseStart_815341 := by decide
  rcases family_descends (prefixWord ++ tailWord_815341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815361 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_815361 : Nat := 118140960795 + 815361 * 2 ^ 59
def prefixEnd_815361 : Nat := 4983230072969 + 3 ^ 40 * 815361 * 2
def baseEnd_815361 : Nat := 418672099930689630037729

theorem tailTrace_815361 : CollatzResearch.WordTrace tailWord_815361 prefixEnd_815361 418672099930689630037729 := by
  unfold tailWord_815361
  simp only [CollatzResearch.WordTrace]
  refine ⟨29738658799093824417445937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19825772532729216278297291 29738658799093824417445937)
  ·
    refine ⟨22303994099320368313084453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29738658799093824417445937 22303994099320368313084453)
    ·
      refine ⟨4181998893622569058703335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22303994099320368313084453 4181998893622569058703335)
      ·
        refine ⟨6272998340433853588055003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4181998893622569058703335 6272998340433853588055003)
        ·
          refine ⟨9409497510650780382082505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6272998340433853588055003 9409497510650780382082505)
          ·
            refine ⟨7057123132988085286561879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9409497510650780382082505 7057123132988085286561879)
            ·
              refine ⟨10585684699482127929842819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7057123132988085286561879 10585684699482127929842819)
              ·
                refine ⟨15878527049223191894764229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10585684699482127929842819 15878527049223191894764229)
                ·
                  refine ⟨2977223821729348480268293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15878527049223191894764229 2977223821729348480268293)
                  ·
                    refine ⟨558229466574252840050305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2977223821729348480268293 558229466574252840050305)
                    ·
                      refine ⟨418672099930689630037729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558229466574252840050305 418672099930689630037729)
                      ·
                        rfl

theorem cell23_815361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_815361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815361 prefixEnd_815361 := by exact prefixLift 815361
  have htrace : WordTrace (prefixWord ++ tailWord_815361) baseStart_815361 baseEnd_815361 := by
    simpa [prefixWord, tailWord_815361, baseEnd_815361] using wordTrace_append hprefix tailTrace_815361
  have hstable : (prefixWord ++ tailWord_815361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815361).length < 2 ^ (prefixWord ++ tailWord_815361).sum := by decide
  have hdescent : baseEnd_815361 < baseStart_815361 := by decide
  rcases family_descends (prefixWord ++ tailWord_815361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815371 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 3, 4]
def baseStart_815371 : Nat := 118140960795 + 815371 * 2 ^ 59
def prefixEnd_815371 : Nat := 4983230072969 + 3 ^ 40 * 815371 * 2
def baseEnd_815371 : Nat := 139559078245744863637561

theorem tailTrace_815371 : CollatzResearch.WordTrace tailWord_815371 prefixEnd_815371 139559078245744863637561 := by
  unfold tailWord_815371
  simp only [CollatzResearch.WordTrace]
  refine ⟨29739023529057596125309967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19826015686038397416873311 29739023529057596125309967)
  ·
    refine ⟨44608535293586394187964951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29739023529057596125309967 44608535293586394187964951)
    ·
      refine ⟨66912802940379591281947427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44608535293586394187964951 66912802940379591281947427)
      ·
        refine ⟨100369204410569386922921141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66912802940379591281947427 100369204410569386922921141)
        ·
          refine ⟨9409612913490880024023857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100369204410569386922921141 9409612913490880024023857)
          ·
            refine ⟨7057209685118160018017893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9409612913490880024023857 7057209685118160018017893)
            ·
              refine ⟨1323226815959655003378355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7057209685118160018017893 1323226815959655003378355)
              ·
                refine ⟨1984840223939482505067533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323226815959655003378355 1984840223939482505067533)
                ·
                  refine ⟨744315083977305939400325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1984840223939482505067533 744315083977305939400325)
                  ·
                    refine ⟨139559078245744863637561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 744315083977305939400325 139559078245744863637561)
                    ·
                      rfl

theorem cell23_815371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 4].length) (baseStart_815371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815371 prefixEnd_815371 := by exact prefixLift 815371
  have htrace : WordTrace (prefixWord ++ tailWord_815371) baseStart_815371 baseEnd_815371 := by
    simpa [prefixWord, tailWord_815371, baseEnd_815371] using wordTrace_append hprefix tailTrace_815371
  have hstable : (prefixWord ++ tailWord_815371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815371).length < 2 ^ (prefixWord ++ tailWord_815371).sum := by decide
  have hdescent : baseEnd_815371 < baseStart_815371 := by decide
  rcases family_descends (prefixWord ++ tailWord_815371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815374 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_815374 : Nat := 118140960795 + 815374 * 2 ^ 59
def prefixEnd_815374 : Nat := 4983230072969 + 3 ^ 40 * 815374 * 2
def baseEnd_815374 : Nat := 418678775179198079175169

theorem tailTrace_815374 : CollatzResearch.WordTrace tailWord_815374 prefixEnd_815374 418678775179198079175169 := by
  unfold tailWord_815374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717391618505840954708647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19826088632031151758446117 3717391618505840954708647)
  ·
    refine ⟨5576087427758761432062971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3717391618505840954708647 5576087427758761432062971)
    ·
      refine ⟨8364131141638142148094457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5576087427758761432062971 8364131141638142148094457)
      ·
        refine ⟨6273098356228606611070843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8364131141638142148094457 6273098356228606611070843)
        ·
          refine ⟨9409647534342909916606265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6273098356228606611070843 9409647534342909916606265)
          ·
            refine ⟨7057235650757182437454699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9409647534342909916606265 7057235650757182437454699)
            ·
              refine ⟨10585853476135773656182049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7057235650757182437454699 10585853476135773656182049)
              ·
                refine ⟨7939390107101830242136537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10585853476135773656182049 7939390107101830242136537)
                ·
                  refine ⟨5954542580326372681602403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7939390107101830242136537 5954542580326372681602403)
                  ·
                    refine ⟨8931813870489559022403605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5954542580326372681602403 8931813870489559022403605)
                    ·
                      refine ⟨418678775179198079175169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8931813870489559022403605 418678775179198079175169)
                      ·
                        rfl

theorem cell23_815374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_815374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815374 prefixEnd_815374 := by exact prefixLift 815374
  have htrace : WordTrace (prefixWord ++ tailWord_815374) baseStart_815374 baseEnd_815374 := by
    simpa [prefixWord, tailWord_815374, baseEnd_815374] using wordTrace_append hprefix tailTrace_815374
  have hstable : (prefixWord ++ tailWord_815374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815374).length < 2 ^ (prefixWord ++ tailWord_815374).sum := by decide
  have hdescent : baseEnd_815374 < baseStart_815374 := by decide
  rcases family_descends (prefixWord ++ tailWord_815374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815422 : List Nat := [4, 2, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_815422 : Nat := 118140960795 + 815422 * 2 ^ 59
def prefixEnd_815422 : Nat := 4983230072969 + 3 ^ 40 * 815422 * 2
def baseEnd_815422 : Nat := 139567807416871297124983

theorem tailTrace_815422 : CollatzResearch.WordTrace tailWord_815422 prefixEnd_815422 139567807416871297124983 := by
  unfold tailWord_815422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717610456484103979427065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19827255767915221223611013 3717610456484103979427065)
  ·
    refine ⟨2788207842363077984570299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3717610456484103979427065 2788207842363077984570299)
    ·
      refine ⟨4182311763544616976855449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2788207842363077984570299 4182311763544616976855449)
      ·
        refine ⟨3136733822658462732641587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4182311763544616976855449 3136733822658462732641587)
        ·
          refine ⟨4705100733987694098962381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136733822658462732641587 4705100733987694098962381)
          ·
            refine ⟨1764412775245385287110893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4705100733987694098962381 1764412775245385287110893)
            ·
              refine ⟨661654790717019482666585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1764412775245385287110893 661654790717019482666585)
              ·
                refine ⟨496241093037764611999939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661654790717019482666585 496241093037764611999939)
                ·
                  refine ⟨744361639556646917999909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496241093037764611999939 744361639556646917999909)
                  ·
                    refine ⟨139567807416871297124983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 744361639556646917999909 139567807416871297124983)
                    ·
                      rfl

theorem cell23_815422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_815422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815422 prefixEnd_815422 := by exact prefixLift 815422
  have htrace : WordTrace (prefixWord ++ tailWord_815422) baseStart_815422 baseEnd_815422 := by
    simpa [prefixWord, tailWord_815422, baseEnd_815422] using wordTrace_append hprefix tailTrace_815422
  have hstable : (prefixWord ++ tailWord_815422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815422).length < 2 ^ (prefixWord ++ tailWord_815422).sum := by decide
  have hdescent : baseEnd_815422 < baseStart_815422 := by decide
  rcases family_descends (prefixWord ++ tailWord_815422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815434 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_815434 : Nat := 118140960795 + 815434 * 2 ^ 59
def prefixEnd_815434 : Nat := 4983230072969 + 3 ^ 40 * 815434 * 2
def baseEnd_815434 : Nat := 418709584018467844424893

theorem tailTrace_815434 : CollatzResearch.WordTrace tailWord_815434 prefixEnd_815434 418709584018467844424893 := by
  unfold tailWord_815434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7435330331957339471213339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19827547551886238589902237 7435330331957339471213339)
  ·
    refine ⟨11152995497936009206820009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7435330331957339471213339 11152995497936009206820009)
    ·
      refine ⟨8364746623452006905115007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11152995497936009206820009 8364746623452006905115007)
      ·
        refine ⟨12547119935178010357672511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8364746623452006905115007 12547119935178010357672511)
        ·
          refine ⟨18820679902767015536508767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12547119935178010357672511 18820679902767015536508767)
          ·
            refine ⟨28231019854150523304763151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18820679902767015536508767 28231019854150523304763151)
            ·
              refine ⟨42346529781225784957144727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28231019854150523304763151 42346529781225784957144727)
              ·
                refine ⟨63519794671838677435717091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42346529781225784957144727 63519794671838677435717091)
                ·
                  refine ⟨95279692007758016153575637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63519794671838677435717091 95279692007758016153575637)
                  ·
                    refine ⟨2233117781431828503599429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 95279692007758016153575637 2233117781431828503599429)
                    ·
                      refine ⟨418709584018467844424893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2233117781431828503599429 418709584018467844424893)
                      ·
                        rfl

theorem cell23_815434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_815434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815434 prefixEnd_815434 := by exact prefixLift 815434
  have htrace : WordTrace (prefixWord ++ tailWord_815434) baseStart_815434 baseEnd_815434 := by
    simpa [prefixWord, tailWord_815434, baseEnd_815434] using wordTrace_append hprefix tailTrace_815434
  have hstable : (prefixWord ++ tailWord_815434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815434).length < 2 ^ (prefixWord ++ tailWord_815434).sum := by decide
  have hdescent : baseEnd_815434 < baseStart_815434 := by decide
  rcases family_descends (prefixWord ++ tailWord_815434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815461 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_815461 : Nat := 118140960795 + 815461 * 2 ^ 59
def prefixEnd_815461 : Nat := 4983230072969 + 3 ^ 40 * 815461 * 2
def baseEnd_815461 : Nat := 139574482665379746262423

theorem tailTrace_815461 : CollatzResearch.WordTrace tailWord_815461 prefixEnd_815461 139574482665379746262423 := by
  unfold tailWord_815461
  simp only [CollatzResearch.WordTrace]
  refine ⟨29742306098731541496086237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19828204065821027664057491 29742306098731541496086237)
  ·
    refine ⟨11153364787024328061032339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29742306098731541496086237 11153364787024328061032339)
    ·
      refine ⟨16730047180536492091548509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11153364787024328061032339 16730047180536492091548509)
      ·
        refine ⟨6273767692701184534330691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16730047180536492091548509 6273767692701184534330691)
        ·
          refine ⟨9410651539051776801496037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6273767692701184534330691 9410651539051776801496037)
          ·
            refine ⟨1764497163572208150280507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9410651539051776801496037 1764497163572208150280507)
            ·
              refine ⟨2646745745358312225420761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764497163572208150280507 2646745745358312225420761)
              ·
                refine ⟨1985059309018734169065571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2646745745358312225420761 1985059309018734169065571)
                ·
                  refine ⟨2977588963528101253598357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985059309018734169065571 2977588963528101253598357)
                  ·
                    refine ⟨139574482665379746262423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2977588963528101253598357 139574482665379746262423)
                    ·
                      rfl

theorem cell23_815461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_815461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815461 prefixEnd_815461 := by exact prefixLift 815461
  have htrace : WordTrace (prefixWord ++ tailWord_815461) baseStart_815461 baseEnd_815461 := by
    simpa [prefixWord, tailWord_815461, baseEnd_815461] using wordTrace_append hprefix tailTrace_815461
  have hstable : (prefixWord ++ tailWord_815461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815461).length < 2 ^ (prefixWord ++ tailWord_815461).sum := by decide
  have hdescent : baseEnd_815461 < baseStart_815461 := by decide
  rcases family_descends (prefixWord ++ tailWord_815461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815474 : List Nat := [3, 2, 1, 2, 1, 14]
def baseStart_815474 : Nat := 118140960795 + 815474 * 2 ^ 59
def prefixEnd_815474 : Nat := 4983230072969 + 3 ^ 40 * 815474 * 2
def baseEnd_815474 : Nat := 1723169231459455505863

theorem tailTrace_815474 : CollatzResearch.WordTrace tailWord_815474 prefixEnd_815474 1723169231459455505863 := by
  unfold tailWord_815474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7435695061921111179077369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19828520165122963144206317 7435695061921111179077369)
  ·
    refine ⟨5576771296440833384308027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7435695061921111179077369 5576771296440833384308027)
    ·
      refine ⟨8365156944661250076462041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5576771296440833384308027 8365156944661250076462041)
      ·
        refine ⟨6273867708495937557346531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8365156944661250076462041 6273867708495937557346531)
        ·
          refine ⟨9410801562743906336019797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6273867708495937557346531 9410801562743906336019797)
          ·
            refine ⟨1723169231459455505863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 9410801562743906336019797 1723169231459455505863)
            ·
              rfl

theorem cell23_815474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 14].length) (baseStart_815474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815474 prefixEnd_815474 := by exact prefixLift 815474
  have htrace : WordTrace (prefixWord ++ tailWord_815474) baseStart_815474 baseEnd_815474 := by
    simpa [prefixWord, tailWord_815474, baseEnd_815474] using wordTrace_append hprefix tailTrace_815474
  have hstable : (prefixWord ++ tailWord_815474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815474).length < 2 ^ (prefixWord ++ tailWord_815474).sum := by decide
  have hdescent : baseEnd_815474 < baseStart_815474 := by decide
  rcases family_descends (prefixWord ++ tailWord_815474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815484 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_815484 : Nat := 118140960795 + 815484 * 2 ^ 59
def prefixEnd_815484 : Nat := 4983230072969 + 3 ^ 40 * 815484 * 2
def baseEnd_815484 : Nat := 418735258051192648799663

theorem tailTrace_815484 : CollatzResearch.WordTrace tailWord_815484 prefixEnd_815484 418735258051192648799663 := by
  unfold tailWord_815484
  simp only [CollatzResearch.WordTrace]
  refine ⟨14871572488824108212086753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19828763318432144282782337 14871572488824108212086753)
  ·
    refine ⟨11153679366618081159065065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14871572488824108212086753 11153679366618081159065065)
    ·
      refine ⟨8365259524963560869298799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11153679366618081159065065 8365259524963560869298799)
      ·
        refine ⟨12547889287445341303948199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8365259524963560869298799 12547889287445341303948199)
        ·
          refine ⟨18821833931168011955922299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12547889287445341303948199 18821833931168011955922299)
          ·
            refine ⟨28232750896752017933883449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18821833931168011955922299 28232750896752017933883449)
            ·
              refine ⟨21174563172564013450412587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28232750896752017933883449 21174563172564013450412587)
              ·
                refine ⟨31761844758846020175618881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21174563172564013450412587 31761844758846020175618881)
                ·
                  refine ⟨23821383569134515131714161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31761844758846020175618881 23821383569134515131714161)
                  ·
                    refine ⟨17866037676850886348785621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23821383569134515131714161 17866037676850886348785621)
                    ·
                      refine ⟨418735258051192648799663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17866037676850886348785621 418735258051192648799663)
                      ·
                        rfl

theorem cell23_815484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_815484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815484 prefixEnd_815484 := by exact prefixLift 815484
  have htrace : WordTrace (prefixWord ++ tailWord_815484) baseStart_815484 baseEnd_815484 := by
    simpa [prefixWord, tailWord_815484, baseEnd_815484] using wordTrace_append hprefix tailTrace_815484
  have hstable : (prefixWord ++ tailWord_815484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815484).length < 2 ^ (prefixWord ++ tailWord_815484).sum := by decide
  have hdescent : baseEnd_815484 < baseStart_815484 := by decide
  rcases family_descends (prefixWord ++ tailWord_815484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815502 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2]
def baseStart_815502 : Nat := 118140960795 + 815502 * 2 ^ 59
def prefixEnd_815502 : Nat := 4983230072969 + 3 ^ 40 * 815502 * 2
def baseEnd_815502 : Nat := 418744500702973578374581

theorem tailTrace_815502 : CollatzResearch.WordTrace tailWord_815502 prefixEnd_815502 418744500702973578374581 := by
  unfold tailWord_815502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717975186447875687291095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19829200994388670332219173 3717975186447875687291095)
  ·
    refine ⟨5576962779671813530936643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3717975186447875687291095 5576962779671813530936643)
    ·
      refine ⟨8365444169507720296404965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5576962779671813530936643 8365444169507720296404965)
      ·
        refine ⟨1568520781782697555575931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8365444169507720296404965 1568520781782697555575931)
        ·
          refine ⟨2352781172674046333363897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568520781782697555575931 2352781172674046333363897)
          ·
            refine ⟨1764585879505534750022923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2352781172674046333363897 1764585879505534750022923)
            ·
              refine ⟨2646878819258302125034385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764585879505534750022923 2646878819258302125034385)
              ·
                refine ⟨1985159114443726593775789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2646878819258302125034385 1985159114443726593775789)
                ·
                  refine ⟨744434667916397472665921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1985159114443726593775789 744434667916397472665921)
                  ·
                    refine ⟨558326000937298104499441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 744434667916397472665921 558326000937298104499441)
                    ·
                      refine ⟨418744500702973578374581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558326000937298104499441 418744500702973578374581)
                      ·
                        rfl

theorem cell23_815502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_815502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815502 prefixEnd_815502 := by exact prefixLift 815502
  have htrace : WordTrace (prefixWord ++ tailWord_815502) baseStart_815502 baseEnd_815502 := by
    simpa [prefixWord, tailWord_815502, baseEnd_815502] using wordTrace_append hprefix tailTrace_815502
  have hstable : (prefixWord ++ tailWord_815502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815502).length < 2 ^ (prefixWord ++ tailWord_815502).sum := by decide
  have hdescent : baseEnd_815502 < baseStart_815502 := by decide
  rcases family_descends (prefixWord ++ tailWord_815502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815561 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 2, 4, 3]
def baseStart_815561 : Nat := 118140960795 + 815561 * 2 ^ 59
def prefixEnd_815561 : Nat := 4983230072969 + 3 ^ 40 * 815561 * 2
def baseEnd_815561 : Nat := 418774796061588847536809

theorem tailTrace_815561 : CollatzResearch.WordTrace tailWord_815561 prefixEnd_815561 418774796061588847536809 := by
  unfold tailWord_815561
  simp only [CollatzResearch.WordTrace]
  refine ⟨29745953398369258574726537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19830635598912839049817691 29745953398369258574726537)
  ·
    refine ⟨22309465048776943931044903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29745953398369258574726537 22309465048776943931044903)
    ·
      refine ⟨33464197573165415896567355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22309465048776943931044903 33464197573165415896567355)
      ·
        refine ⟨50196296359748123844851033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33464197573165415896567355 50196296359748123844851033)
        ·
          refine ⟨37647222269811092883638275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50196296359748123844851033 37647222269811092883638275)
          ·
            refine ⟨56470833404716639325457413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37647222269811092883638275 56470833404716639325457413)
            ·
              refine ⟨10588281263384369873523265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56470833404716639325457413 10588281263384369873523265)
              ·
                refine ⟨7941210947538277405142449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10588281263384369873523265 7941210947538277405142449)
                ·
                  refine ⟨5955908210653708053856837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7941210947538277405142449 5955908210653708053856837)
                  ·
                    refine ⟨1116732789497570260098157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5955908210653708053856837 1116732789497570260098157)
                    ·
                      refine ⟨418774796061588847536809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1116732789497570260098157 418774796061588847536809)
                      ·
                        rfl

theorem cell23_815561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4, 3].length) (baseStart_815561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815561 prefixEnd_815561 := by exact prefixLift 815561
  have htrace : WordTrace (prefixWord ++ tailWord_815561) baseStart_815561 baseEnd_815561 := by
    simpa [prefixWord, tailWord_815561, baseEnd_815561] using wordTrace_append hprefix tailTrace_815561
  have hstable : (prefixWord ++ tailWord_815561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815561).length < 2 ^ (prefixWord ++ tailWord_815561).sum := by decide
  have hdescent : baseEnd_815561 < baseStart_815561 := by decide
  rcases family_descends (prefixWord ++ tailWord_815561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815591 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_815591 : Nat := 118140960795 + 815591 * 2 ^ 59
def prefixEnd_815591 : Nat := 4983230072969 + 3 ^ 40 * 815591 * 2
def baseEnd_815591 : Nat := 418790200481223730161671

theorem tailTrace_815591 : CollatzResearch.WordTrace tailWord_815591 prefixEnd_815591 418790200481223730161671 := by
  unfold tailWord_815591
  simp only [CollatzResearch.WordTrace]
  refine ⟨29747047588260573698318627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19831365058840382465545751 29747047588260573698318627)
  ·
    refine ⟨44620571382390860547477941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29747047588260573698318627 44620571382390860547477941)
    ·
      refine ⟨4183178567099143176326057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44620571382390860547477941 4183178567099143176326057)
      ·
        refine ⟨3137383925324357382244543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4183178567099143176326057 3137383925324357382244543)
        ·
          refine ⟨4706075887986536073366815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137383925324357382244543 4706075887986536073366815)
          ·
            refine ⟨7059113831979804110050223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706075887986536073366815 7059113831979804110050223)
            ·
              refine ⟨10588670747969706165075335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7059113831979804110050223 10588670747969706165075335)
              ·
                refine ⟨15883006121954559247613003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10588670747969706165075335 15883006121954559247613003)
                ·
                  refine ⟨23824509182931838871419505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15883006121954559247613003 23824509182931838871419505)
                  ·
                    refine ⟨17868381887198879153564629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23824509182931838871419505 17868381887198879153564629)
                    ·
                      refine ⟨418790200481223730161671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17868381887198879153564629 418790200481223730161671)
                      ·
                        rfl

theorem cell23_815591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_815591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815591 prefixEnd_815591 := by exact prefixLift 815591
  have htrace : WordTrace (prefixWord ++ tailWord_815591) baseStart_815591 baseEnd_815591 := by
    simpa [prefixWord, tailWord_815591, baseEnd_815591] using wordTrace_append hprefix tailTrace_815591
  have hstable : (prefixWord ++ tailWord_815591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815591).length < 2 ^ (prefixWord ++ tailWord_815591).sum := by decide
  have hdescent : baseEnd_815591 < baseStart_815591 := by decide
  rcases family_descends (prefixWord ++ tailWord_815591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815598 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_815598 : Nat := 118140960795 + 815598 * 2 ^ 59
def prefixEnd_815598 : Nat := 4983230072969 + 3 ^ 40 * 815598 * 2
def baseEnd_815598 : Nat := 46532643871756133641571

theorem tailTrace_815598 : CollatzResearch.WordTrace tailWord_815598 prefixEnd_815598 46532643871756133641571 := by
  unfold tailWord_815598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3718412862404401736727931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19831535266156809262548965 3718412862404401736727931)
  ·
    refine ⟨5577619293606602605091897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3718412862404401736727931 5577619293606602605091897)
    ·
      refine ⟨4183214470204951953818923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5577619293606602605091897 4183214470204951953818923)
      ·
        refine ⟨6274821705307427930728385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4183214470204951953818923 6274821705307427930728385)
        ·
          refine ⟨4706116278980570948046289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6274821705307427930728385 4706116278980570948046289)
          ·
            refine ⟨3529587209235428211034717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4706116278980570948046289 3529587209235428211034717)
            ·
              refine ⟨1323595203463285579138019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3529587209235428211034717 1323595203463285579138019)
              ·
                refine ⟨1985392805194928368707029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323595203463285579138019 1985392805194928368707029)
                ·
                  refine ⟨46532643871756133641571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1985392805194928368707029 46532643871756133641571)
                  ·
                    rfl

theorem cell23_815598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_815598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815598 prefixEnd_815598 := by exact prefixLift 815598
  have htrace : WordTrace (prefixWord ++ tailWord_815598) baseStart_815598 baseEnd_815598 := by
    simpa [prefixWord, tailWord_815598, baseEnd_815598] using wordTrace_append hprefix tailTrace_815598
  have hstable : (prefixWord ++ tailWord_815598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815598).length < 2 ^ (prefixWord ++ tailWord_815598).sum := by decide
  have hdescent : baseEnd_815598 < baseStart_815598 := by decide
  rcases family_descends (prefixWord ++ tailWord_815598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815628 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_815628 : Nat := 118140960795 + 815628 * 2 ^ 59
def prefixEnd_815628 : Nat := 4983230072969 + 3 ^ 40 * 815628 * 2
def baseEnd_815628 : Nat := 139603066421813361799667

theorem tailTrace_815628 : CollatzResearch.WordTrace tailWord_815628 prefixEnd_815628 139603066421813361799667 := by
  unfold tailWord_815628
  simp only [CollatzResearch.WordTrace]
  refine ⟨14874198544563264508707769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19832264726084352678277025 14874198544563264508707769)
  ·
    refine ⟨11155648908422448381530827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14874198544563264508707769 11155648908422448381530827)
    ·
      refine ⟨16733473362633672572296241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11155648908422448381530827 16733473362633672572296241)
      ·
        refine ⟨12550105021975254429222181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16733473362633672572296241 12550105021975254429222181)
        ·
          refine ⟨2353144691620360205479159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12550105021975254429222181 2353144691620360205479159)
          ·
            refine ⟨3529717037430540308218739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353144691620360205479159 3529717037430540308218739)
            ·
              refine ⟨5294575556145810462328109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529717037430540308218739 5294575556145810462328109)
              ·
                refine ⟨1985465833554678923373041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5294575556145810462328109 1985465833554678923373041)
                ·
                  refine ⟨1489099375166009192529781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1985465833554678923373041 1489099375166009192529781)
                  ·
                    refine ⟨139603066421813361799667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1489099375166009192529781 139603066421813361799667)
                    ·
                      rfl

theorem cell23_815628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_815628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815628 prefixEnd_815628 := by exact prefixLift 815628
  have htrace : WordTrace (prefixWord ++ tailWord_815628) baseStart_815628 baseEnd_815628 := by
    simpa [prefixWord, tailWord_815628, baseEnd_815628] using wordTrace_append hprefix tailTrace_815628
  have hstable : (prefixWord ++ tailWord_815628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815628).length < 2 ^ (prefixWord ++ tailWord_815628).sum := by decide
  have hdescent : baseEnd_815628 < baseStart_815628 := by decide
  rcases family_descends (prefixWord ++ tailWord_815628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815685 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 2, 2, 3]
def baseStart_815685 : Nat := 118140960795 + 815685 * 2 ^ 59
def prefixEnd_815685 : Nat := 4983230072969 + 3 ^ 40 * 815685 * 2
def baseEnd_815685 : Nat := 418838467662746362386239

theorem tailTrace_815685 : CollatzResearch.WordTrace tailWord_815685 prefixEnd_815685 418838467662746362386239 := by
  unfold tailWord_815685
  simp only [CollatzResearch.WordTrace]
  refine ⟨29750476049920027752240509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19833650699946685168160339 29750476049920027752240509)
  ·
    refine ⟨11156428518720010407090191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29750476049920027752240509 11156428518720010407090191)
    ·
      refine ⟨16734642778080015610635287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11156428518720010407090191 16734642778080015610635287)
      ·
        refine ⟨25101964167120023415952931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16734642778080015610635287 25101964167120023415952931)
        ·
          refine ⟨37652946250680035123929397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25101964167120023415952931 37652946250680035123929397)
          ·
            refine ⟨3529963711001253292868381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37652946250680035123929397 3529963711001253292868381)
            ·
              refine ⟨1323736391625469984825643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3529963711001253292868381 1323736391625469984825643)
              ·
                refine ⟨1985604587438204977238465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323736391625469984825643 1985604587438204977238465)
                ·
                  refine ⟨1489203440578653732928849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1985604587438204977238465 1489203440578653732928849)
                  ·
                    refine ⟨1116902580433990299696637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1489203440578653732928849 1116902580433990299696637)
                    ·
                      refine ⟨418838467662746362386239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1116902580433990299696637 418838467662746362386239)
                      ·
                        rfl

theorem cell23_815685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_815685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815685 prefixEnd_815685 := by exact prefixLift 815685
  have htrace : WordTrace (prefixWord ++ tailWord_815685) baseStart_815685 baseEnd_815685 := by
    simpa [prefixWord, tailWord_815685, baseEnd_815685] using wordTrace_append hprefix tailTrace_815685
  have hstable : (prefixWord ++ tailWord_815685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815685).length < 2 ^ (prefixWord ++ tailWord_815685).sum := by decide
  have hdescent : baseEnd_815685 < baseStart_815685 := by decide
  rcases family_descends (prefixWord ++ tailWord_815685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815692 : List Nat := [2, 2, 1, 3, 1, 2, 4, 3, 1, 4]
def baseStart_815692 : Nat := 118140960795 + 815692 * 2 ^ 59
def prefixEnd_815692 : Nat := 4983230072969 + 3 ^ 40 * 815692 * 2
def baseEnd_815692 : Nat := 139614020675775944999569

theorem tailTrace_815692 : CollatzResearch.WordTrace tailWord_815692 prefixEnd_815692 139614020675775944999569 := by
  unfold tailWord_815692
  simp only [CollatzResearch.WordTrace]
  refine ⟨14875365680447333973872665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19833820907263111965163553 14875365680447333973872665)
  ·
    refine ⟨11156524260335500480404499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14875365680447333973872665 11156524260335500480404499)
    ·
      refine ⟨16734786390503250720606749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11156524260335500480404499 16734786390503250720606749)
      ·
        refine ⟨6275544896438719020227531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16734786390503250720606749 6275544896438719020227531)
        ·
          refine ⟨9413317344658078530341297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6275544896438719020227531 9413317344658078530341297)
          ·
            refine ⟨7059988008493558897755973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9413317344658078530341297 7059988008493558897755973)
            ·
              refine ⟨1323747751592542293329245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7059988008493558897755973 1323747751592542293329245)
              ·
                refine ⟨496405406847203359998467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1323747751592542293329245 496405406847203359998467)
                ·
                  refine ⟨744608110270805039997701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496405406847203359998467 744608110270805039997701)
                  ·
                    refine ⟨139614020675775944999569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 744608110270805039997701 139614020675775944999569)
                    ·
                      rfl

theorem cell23_815692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_815692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815692 prefixEnd_815692 := by exact prefixLift 815692
  have htrace : WordTrace (prefixWord ++ tailWord_815692) baseStart_815692 baseEnd_815692 := by
    simpa [prefixWord, tailWord_815692, baseEnd_815692] using wordTrace_append hprefix tailTrace_815692
  have hstable : (prefixWord ++ tailWord_815692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815692).length < 2 ^ (prefixWord ++ tailWord_815692).sum := by decide
  have hdescent : baseEnd_815692 < baseStart_815692 := by decide
  rcases family_descends (prefixWord ++ tailWord_815692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815738 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_815738 : Nat := 118140960795 + 815738 * 2 ^ 59
def prefixEnd_815738 : Nat := 4983230072969 + 3 ^ 40 * 815738 * 2
def baseEnd_815738 : Nat := 418865682137434655023495

theorem tailTrace_815738 : CollatzResearch.WordTrace tailWord_815738 prefixEnd_815738 418865682137434655023495 := by
  unfold tailWord_815738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7438102279682004450979967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19834939412485345202613245 7438102279682004450979967)
  ·
    refine ⟨11157153419523006676469951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7438102279682004450979967 11157153419523006676469951)
    ·
      refine ⟨16735730129284510014704927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11157153419523006676469951 16735730129284510014704927)
      ·
        refine ⟨25103595193926765022057391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16735730129284510014704927 25103595193926765022057391)
        ·
          refine ⟨37655392790890147533086087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25103595193926765022057391 37655392790890147533086087)
          ·
            refine ⟨56483089186335221299629131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37655392790890147533086087 56483089186335221299629131)
            ·
              refine ⟨84724633779502831949443697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56483089186335221299629131 84724633779502831949443697)
              ·
                refine ⟨63543475334627123962082773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84724633779502831949443697 63543475334627123962082773)
                ·
                  refine ⟨1489300203155323217861315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 63543475334627123962082773 1489300203155323217861315)
                  ·
                    refine ⟨2233950304732984826791973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1489300203155323217861315 2233950304732984826791973)
                    ·
                      refine ⟨418865682137434655023495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2233950304732984826791973 418865682137434655023495)
                      ·
                        rfl

theorem cell23_815738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_815738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815738 prefixEnd_815738 := by exact prefixLift 815738
  have htrace : WordTrace (prefixWord ++ tailWord_815738) baseStart_815738 baseEnd_815738 := by
    simpa [prefixWord, tailWord_815738, baseEnd_815738] using wordTrace_append hprefix tailTrace_815738
  have hstable : (prefixWord ++ tailWord_815738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815738).length < 2 ^ (prefixWord ++ tailWord_815738).sum := by decide
  have hdescent : baseEnd_815738 < baseStart_815738 := by decide
  rcases family_descends (prefixWord ++ tailWord_815738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815749 : List Nat := [1, 3, 1, 1, 4, 2, 3, 3, 1, 1, 3]
def baseStart_815749 : Nat := 118140960795 + 815749 * 2 ^ 59
def prefixEnd_815749 : Nat := 4983230072969 + 3 ^ 40 * 815749 * 2
def baseEnd_815749 : Nat := 418871330424634111985945

theorem tailTrace_815749 : CollatzResearch.WordTrace tailWord_815749 prefixEnd_815749 418871330424634111985945 := by
  unfold tailWord_815749
  simp only [CollatzResearch.WordTrace]
  refine ⟨29752810321688166682570301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19835206881125444455046867 29752810321688166682570301)
  ·
    refine ⟨11157303870633062505963863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29752810321688166682570301 11157303870633062505963863)
    ·
      refine ⟨16735955805949593758945795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11157303870633062505963863 16735955805949593758945795)
      ·
        refine ⟨25103933708924390638418693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16735955805949593758945795 25103933708924390638418693)
        ·
          refine ⟨4706987570423323244703505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25103933708924390638418693 4706987570423323244703505)
          ·
            refine ⟨3530240677817492433527629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4706987570423323244703505 3530240677817492433527629)
            ·
              refine ⟨1323840254181559662572861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3530240677817492433527629 1323840254181559662572861)
              ·
                refine ⟨496440095318084873464823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1323840254181559662572861 496440095318084873464823)
                ·
                  refine ⟨744660142977127310197235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496440095318084873464823 744660142977127310197235)
                  ·
                    refine ⟨1116990214465690965295853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 744660142977127310197235 1116990214465690965295853)
                    ·
                      refine ⟨418871330424634111985945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1116990214465690965295853 418871330424634111985945)
                      ·
                        rfl

theorem cell23_815749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 1, 1, 3].length) (baseStart_815749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815749 prefixEnd_815749 := by exact prefixLift 815749
  have htrace : WordTrace (prefixWord ++ tailWord_815749) baseStart_815749 baseEnd_815749 := by
    simpa [prefixWord, tailWord_815749, baseEnd_815749] using wordTrace_append hprefix tailTrace_815749
  have hstable : (prefixWord ++ tailWord_815749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815749).length < 2 ^ (prefixWord ++ tailWord_815749).sum := by decide
  have hdescent : baseEnd_815749 < baseStart_815749 := by decide
  rcases family_descends (prefixWord ++ tailWord_815749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815768 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_815768 : Nat := 118140960795 + 815768 * 2 ^ 59
def prefixEnd_815768 : Nat := 4983230072969 + 3 ^ 40 * 815768 * 2
def baseEnd_815768 : Nat := 418881086557069537648357

theorem tailTrace_815768 : CollatzResearch.WordTrace tailWord_815768 prefixEnd_815768 418881086557069537648357 := by
  unfold tailWord_815768
  simp only [CollatzResearch.WordTrace]
  refine ⟨14876751654309666463755979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19835668872412888618341305 14876751654309666463755979)
  ·
    refine ⟨22315127481464499695633969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14876751654309666463755979 22315127481464499695633969)
    ·
      refine ⟨16736345611098374771725477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22315127481464499695633969 16736345611098374771725477)
      ·
        refine ⟨3138064802080945269698527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16736345611098374771725477 3138064802080945269698527)
        ·
          refine ⟨4707097203121417904547791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3138064802080945269698527 4707097203121417904547791)
          ·
            refine ⟨7060645804682126856821687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707097203121417904547791 7060645804682126856821687)
            ·
              refine ⟨10590968707023190285232531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7060645804682126856821687 10590968707023190285232531)
              ·
                refine ⟨15886453060534785427848797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10590968707023190285232531 15886453060534785427848797)
                ·
                  refine ⟨5957419897700544535443299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15886453060534785427848797 5957419897700544535443299)
                  ·
                    refine ⟨8936129846550816803164949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5957419897700544535443299 8936129846550816803164949)
                    ·
                      refine ⟨418881086557069537648357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8936129846550816803164949 418881086557069537648357)
                      ·
                        rfl

theorem cell23_815768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_815768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815768 prefixEnd_815768 := by exact prefixLift 815768
  have htrace : WordTrace (prefixWord ++ tailWord_815768) baseStart_815768 baseEnd_815768 := by
    simpa [prefixWord, tailWord_815768, baseEnd_815768] using wordTrace_append hprefix tailTrace_815768
  have hstable : (prefixWord ++ tailWord_815768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815768).length < 2 ^ (prefixWord ++ tailWord_815768).sum := by decide
  have hdescent : baseEnd_815768 < baseStart_815768 := by decide
  rcases family_descends (prefixWord ++ tailWord_815768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815786 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_815786 : Nat := 118140960795 + 815786 * 2 ^ 59
def prefixEnd_815786 : Nat := 4983230072969 + 3 ^ 40 * 815786 * 2
def baseEnd_815786 : Nat := 139630109736283489074425

theorem tailTrace_815786 : CollatzResearch.WordTrace tailWord_815786 prefixEnd_815786 139630109736283489074425 := by
  unfold tailWord_815786
  simp only [CollatzResearch.WordTrace]
  refine ⟨7438539955638530500416803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19836106548369414667778141 7438539955638530500416803)
  ·
    refine ⟨11157809933457795750625205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7438539955638530500416803 11157809933457795750625205)
    ·
      refine ⟨1046044681261668351621113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11157809933457795750625205 1046044681261668351621113)
      ·
        refine ⟨784533510946251263715835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1046044681261668351621113 784533510946251263715835)
        ·
          refine ⟨1176800266419376895573753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784533510946251263715835 1176800266419376895573753)
          ·
            refine ⟨882600199814532671680315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1176800266419376895573753 882600199814532671680315)
            ·
              refine ⟨1323900299721799007520473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882600199814532671680315 1323900299721799007520473)
              ·
                refine ⟨992925224791349255640355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323900299721799007520473 992925224791349255640355)
                ·
                  refine ⟨1489387837187023883460533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992925224791349255640355 1489387837187023883460533)
                  ·
                    refine ⟨139630109736283489074425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1489387837187023883460533 139630109736283489074425)
                    ·
                      rfl

theorem cell23_815786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_815786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815786 prefixEnd_815786 := by exact prefixLift 815786
  have htrace : WordTrace (prefixWord ++ tailWord_815786) baseStart_815786 baseEnd_815786 := by
    simpa [prefixWord, tailWord_815786, baseEnd_815786] using wordTrace_append hprefix tailTrace_815786
  have hstable : (prefixWord ++ tailWord_815786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815786).length < 2 ^ (prefixWord ++ tailWord_815786).sum := by decide
  have hdescent : baseEnd_815786 < baseStart_815786 := by decide
  rcases family_descends (prefixWord ++ tailWord_815786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815789 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_815789 : Nat := 118140960795 + 815789 * 2 ^ 59
def prefixEnd_815789 : Nat := 4983230072969 + 3 ^ 40 * 815789 * 2
def baseEnd_815789 : Nat := 418891869650813955485761

theorem tailTrace_815789 : CollatzResearch.WordTrace tailWord_815789 prefixEnd_815789 418891869650813955485761 := by
  unfold tailWord_815789
  simp only [CollatzResearch.WordTrace]
  refine ⟨29754269241543253514026421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19836179494362169009350947 29754269241543253514026421)
  ·
    refine ⟨2789462741394680016939977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29754269241543253514026421 2789462741394680016939977)
    ·
      refine ⟨2092097056046010012704983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2789462741394680016939977 2092097056046010012704983)
      ·
        refine ⟨3138145584069015019057475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2092097056046010012704983 3138145584069015019057475)
        ·
          refine ⟨4707218376103522528586213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3138145584069015019057475 4707218376103522528586213)
          ·
            refine ⟨882603445519410474109915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4707218376103522528586213 882603445519410474109915)
            ·
              refine ⟨1323905168279115711164873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882603445519410474109915 1323905168279115711164873)
              ·
                refine ⟨992928876209336783373655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323905168279115711164873 992928876209336783373655)
                ·
                  refine ⟨1489393314314005175060483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992928876209336783373655 1489393314314005175060483)
                  ·
                    refine ⟨2234089971471007762590725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1489393314314005175060483 2234089971471007762590725)
                    ·
                      refine ⟨418891869650813955485761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2234089971471007762590725 418891869650813955485761)
                      ·
                        rfl

theorem cell23_815789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_815789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815789 prefixEnd_815789 := by exact prefixLift 815789
  have htrace : WordTrace (prefixWord ++ tailWord_815789) baseStart_815789 baseEnd_815789 := by
    simpa [prefixWord, tailWord_815789, baseEnd_815789] using wordTrace_append hprefix tailTrace_815789
  have hstable : (prefixWord ++ tailWord_815789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815789).length < 2 ^ (prefixWord ++ tailWord_815789).sum := by decide
  have hdescent : baseEnd_815789 < baseStart_815789 := by decide
  rcases family_descends (prefixWord ++ tailWord_815789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815805 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_815805 : Nat := 118140960795 + 815805 * 2 ^ 59
def prefixEnd_815805 : Nat := 4983230072969 + 3 ^ 40 * 815805 * 2
def baseEnd_815805 : Nat := 418900085341285892885687

theorem tailTrace_815805 : CollatzResearch.WordTrace tailWord_815805 prefixEnd_815805 418900085341285892885687 := by
  unfold tailWord_815805
  simp only [CollatzResearch.WordTrace]
  refine ⟨29754852809485288246608869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19836568539656858831072579 29754852809485288246608869)
  ·
    refine ⟨5579034901778491546239163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29754852809485288246608869 5579034901778491546239163)
    ·
      refine ⟨8368552352667737319358745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5579034901778491546239163 8368552352667737319358745)
      ·
        refine ⟨6276414264500802989519059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8368552352667737319358745 6276414264500802989519059)
        ·
          refine ⟨9414621396751204484278589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6276414264500802989519059 9414621396751204484278589)
          ·
            refine ⟨3530483023781701681604471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9414621396751204484278589 3530483023781701681604471)
            ·
              refine ⟨5295724535672552522406707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530483023781701681604471 5295724535672552522406707)
              ·
                refine ⟨7943586803508828783610061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295724535672552522406707 7943586803508828783610061)
                ·
                  refine ⟨2978845051315810793853773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7943586803508828783610061 2978845051315810793853773)
                  ·
                    refine ⟨1117066894243429047695165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2978845051315810793853773 1117066894243429047695165)
                    ·
                      refine ⟨418900085341285892885687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1117066894243429047695165 418900085341285892885687)
                      ·
                        rfl

theorem cell23_815805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_815805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815805 prefixEnd_815805 := by exact prefixLift 815805
  have htrace : WordTrace (prefixWord ++ tailWord_815805) baseStart_815805 baseEnd_815805 := by
    simpa [prefixWord, tailWord_815805, baseEnd_815805] using wordTrace_append hprefix tailTrace_815805
  have hstable : (prefixWord ++ tailWord_815805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815805).length < 2 ^ (prefixWord ++ tailWord_815805).sum := by decide
  have hdescent : baseEnd_815805 < baseStart_815805 := by decide
  rcases family_descends (prefixWord ++ tailWord_815805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815806 : List Nat := [4, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_815806 : Nat := 118140960795 + 815806 * 2 ^ 59
def prefixEnd_815806 : Nat := 4983230072969 + 3 ^ 40 * 815806 * 2
def baseEnd_815806 : Nat := 418900598821940388973183

theorem tailTrace_815806 : CollatzResearch.WordTrace tailWord_815806 prefixEnd_815806 418900598821940388973183 := by
  unfold tailWord_815806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3719361160310208177174409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19836592854987776944930181 3719361160310208177174409)
  ·
    refine ⟨2789520870232656132880807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3719361160310208177174409 2789520870232656132880807)
    ·
      refine ⟨4184281305348984199321211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2789520870232656132880807 4184281305348984199321211)
      ·
        refine ⟨6276421958023476298981817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4184281305348984199321211 6276421958023476298981817)
        ·
          refine ⟨4707316468517607224236363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6276421958023476298981817 4707316468517607224236363)
          ·
            refine ⟨7060974702776410836354545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707316468517607224236363 7060974702776410836354545)
            ·
              refine ⟨5295731027082308127265909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7060974702776410836354545 5295731027082308127265909)
              ·
                refine ⟨496474783788966386931179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5295731027082308127265909 496474783788966386931179)
                ·
                  refine ⟨744712175683449580396769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496474783788966386931179 744712175683449580396769)
                  ·
                    refine ⟨558534131762587185297577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 744712175683449580396769 558534131762587185297577)
                    ·
                      refine ⟨418900598821940388973183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558534131762587185297577 418900598821940388973183)
                      ·
                        rfl

theorem cell23_815806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_815806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815806 prefixEnd_815806 := by exact prefixLift 815806
  have htrace : WordTrace (prefixWord ++ tailWord_815806) baseStart_815806 baseEnd_815806 := by
    simpa [prefixWord, tailWord_815806, baseEnd_815806] using wordTrace_append hprefix tailTrace_815806
  have hstable : (prefixWord ++ tailWord_815806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815806).length < 2 ^ (prefixWord ++ tailWord_815806).sum := by decide
  have hdescent : baseEnd_815806 < baseStart_815806 := by decide
  rcases family_descends (prefixWord ++ tailWord_815806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815829 : List Nat := [1, 3, 2, 5, 2, 1, 1, 8]
def baseStart_815829 : Nat := 118140960795 + 815829 * 2 ^ 59
def prefixEnd_815829 : Nat := 4983230072969 + 3 ^ 40 * 815829 * 2
def baseEnd_815829 : Nat := 15515274402851622184651

theorem tailTrace_815829 : CollatzResearch.WordTrace tailWord_815829 prefixEnd_815829 15515274402851622184651 := by
  unfold tailWord_815829
  simp only [CollatzResearch.WordTrace]
  refine ⟨29755728161398340345482541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19837152107598893563655027 29755728161398340345482541)
  ·
    refine ⟨11158398060524377629555953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29755728161398340345482541 11158398060524377629555953)
    ·
      refine ⟨8368798545393283222166965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11158398060524377629555953 8368798545393283222166965)
      ·
        refine ⟨784574863630620302078153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8368798545393283222166965 784574863630620302078153)
        ·
          refine ⟨588431147722965226558615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784574863630620302078153 588431147722965226558615)
          ·
            refine ⟨882646721584447839837923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588431147722965226558615 882646721584447839837923)
            ·
              refine ⟨1323970082376671759756885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882646721584447839837923 1323970082376671759756885)
              ·
                refine ⟨15515274402851622184651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1323970082376671759756885 15515274402851622184651)
                ·
                  rfl

theorem cell23_815829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 8].length) (baseStart_815829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815829 prefixEnd_815829 := by exact prefixLift 815829
  have htrace : WordTrace (prefixWord ++ tailWord_815829) baseStart_815829 baseEnd_815829 := by
    simpa [prefixWord, tailWord_815829, baseEnd_815829] using wordTrace_append hprefix tailTrace_815829
  have hstable : (prefixWord ++ tailWord_815829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815829).length < 2 ^ (prefixWord ++ tailWord_815829).sum := by decide
  have hdescent : baseEnd_815829 < baseStart_815829 := by decide
  rcases family_descends (prefixWord ++ tailWord_815829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815832 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 3, 3, 2]
def baseStart_815832 : Nat := 118140960795 + 815832 * 2 ^ 59
def prefixEnd_815832 : Nat := 4983230072969 + 3 ^ 40 * 815832 * 2
def baseEnd_815832 : Nat := 418913949318957287248063

theorem tailTrace_815832 : CollatzResearch.WordTrace tailWord_815832 prefixEnd_815832 418913949318957287248063 := by
  unfold tailWord_815832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14877918790193735928920875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19837225053591647905227833 14877918790193735928920875)
  ·
    refine ⟨22316878185290603893381313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14877918790193735928920875 22316878185290603893381313)
    ·
      refine ⟨16737658638967952920035985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22316878185290603893381313 16737658638967952920035985)
      ·
        refine ⟨12553243979225964690026989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16737658638967952920035985 12553243979225964690026989)
        ·
          refine ⟨4707466492209736758760121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12553243979225964690026989 4707466492209736758760121)
          ·
            refine ⟨3530599869157302569070091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4707466492209736758760121 3530599869157302569070091)
            ·
              refine ⟨5295899803735953853605137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530599869157302569070091 5295899803735953853605137)
              ·
                refine ⟨3971924852801965390203853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5295899803735953853605137 3971924852801965390203853)
                ·
                  refine ⟨1489471819800737021326445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3971924852801965390203853 1489471819800737021326445)
                  ·
                    refine ⟨558551932425276382997417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1489471819800737021326445 558551932425276382997417)
                    ·
                      refine ⟨418913949318957287248063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558551932425276382997417 418913949318957287248063)
                      ·
                        rfl

theorem cell23_815832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_815832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815832 prefixEnd_815832 := by exact prefixLift 815832
  have htrace : WordTrace (prefixWord ++ tailWord_815832) baseStart_815832 baseEnd_815832 := by
    simpa [prefixWord, tailWord_815832, baseEnd_815832] using wordTrace_append hprefix tailTrace_815832
  have hstable : (prefixWord ++ tailWord_815832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815832).length < 2 ^ (prefixWord ++ tailWord_815832).sum := by decide
  have hdescent : baseEnd_815832 < baseStart_815832 := by decide
  rcases family_descends (prefixWord ++ tailWord_815832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815860 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_815860 : Nat := 118140960795 + 815860 * 2 ^ 59
def prefixEnd_815860 : Nat := 4983230072969 + 3 ^ 40 * 815860 * 2
def baseEnd_815860 : Nat := 418928326777283177697935

theorem tailTrace_815860 : CollatzResearch.WordTrace tailWord_815860 prefixEnd_815860 418928326777283177697935 := by
  unfold tailWord_815860
  simp only [CollatzResearch.WordTrace]
  refine ⟨14878429412143016319930517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19837905882857355093240689 14878429412143016319930517)
  ·
    refine ⟨697426378694203889996743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14878429412143016319930517 697426378694203889996743)
    ·
      refine ⟨1046139568041305834995115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 697426378694203889996743 1046139568041305834995115)
      ·
        refine ⟨1569209352061958752492673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046139568041305834995115 1569209352061958752492673)
        ·
          refine ⟨1176907014046469064369505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1569209352061958752492673 1176907014046469064369505)
          ·
            refine ⟨882680260534851798277129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1176907014046469064369505 882680260534851798277129)
            ·
              refine ⟨662010195401138848707847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882680260534851798277129 662010195401138848707847)
              ·
                refine ⟨993015293101708273061771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662010195401138848707847 993015293101708273061771)
                ·
                  refine ⟨1489522939652562409592657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993015293101708273061771 1489522939652562409592657)
                  ·
                    refine ⟨1117142204739421807194493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1489522939652562409592657 1117142204739421807194493)
                    ·
                      refine ⟨418928326777283177697935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1117142204739421807194493 418928326777283177697935)
                      ·
                        rfl

theorem cell23_815860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_815860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815860 prefixEnd_815860 := by exact prefixLift 815860
  have htrace : WordTrace (prefixWord ++ tailWord_815860) baseStart_815860 baseEnd_815860 := by
    simpa [prefixWord, tailWord_815860, baseEnd_815860] using wordTrace_append hprefix tailTrace_815860
  have hstable : (prefixWord ++ tailWord_815860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815860).length < 2 ^ (prefixWord ++ tailWord_815860).sum := by decide
  have hdescent : baseEnd_815860 < baseStart_815860 := by decide
  rcases family_descends (prefixWord ++ tailWord_815860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815952 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 2, 4, 2]
def baseStart_815952 : Nat := 118140960795 + 815952 * 2 ^ 59
def prefixEnd_815952 : Nat := 4983230072969 + 3 ^ 40 * 815952 * 2
def baseEnd_815952 : Nat := 418975566997496817747511

theorem tailTrace_815952 : CollatzResearch.WordTrace tailWord_815952 prefixEnd_815952 418975566997496817747511 := by
  unfold tailWord_815952
  simp only [CollatzResearch.WordTrace]
  refine ⟨14880107169976366176105055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19840142893301821568140073 14880107169976366176105055)
  ·
    refine ⟨22320160754964549264157583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14880107169976366176105055 22320160754964549264157583)
    ·
      refine ⟨33480241132446823896236375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22320160754964549264157583 33480241132446823896236375)
      ·
        refine ⟨50220361698670235844354563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33480241132446823896236375 50220361698670235844354563)
        ·
          refine ⟨75330542548005353766531845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50220361698670235844354563 75330542548005353766531845)
          ·
            refine ⟨14124476727751003831224721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75330542548005353766531845 14124476727751003831224721)
            ·
              refine ⟨10593357545813252873418541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14124476727751003831224721 10593357545813252873418541)
              ·
                refine ⟨3972509079679969827531953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10593357545813252873418541 3972509079679969827531953)
                ·
                  refine ⟨2979381809759977370648965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3972509079679969827531953 2979381809759977370648965)
                  ·
                    refine ⟨558634089329995756996681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2979381809759977370648965 558634089329995756996681)
                    ·
                      refine ⟨418975566997496817747511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558634089329995756996681 418975566997496817747511)
                      ·
                        rfl

theorem cell23_815952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 4, 2].length) (baseStart_815952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815952 prefixEnd_815952 := by exact prefixLift 815952
  have htrace : WordTrace (prefixWord ++ tailWord_815952) baseStart_815952 baseEnd_815952 := by
    simpa [prefixWord, tailWord_815952, baseEnd_815952] using wordTrace_append hprefix tailTrace_815952
  have hstable : (prefixWord ++ tailWord_815952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815952).length < 2 ^ (prefixWord ++ tailWord_815952).sum := by decide
  have hdescent : baseEnd_815952 < baseStart_815952 := by decide
  rcases family_descends (prefixWord ++ tailWord_815952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815955 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 3]
def baseStart_815955 : Nat := 118140960795 + 815955 * 2 ^ 59
def prefixEnd_815955 : Nat := 4983230072969 + 3 ^ 40 * 815955 * 2
def baseEnd_815955 : Nat := 418977107439460306009997

theorem tailTrace_815955 : CollatzResearch.WordTrace tailWord_815955 prefixEnd_815955 418977107439460306009997 := by
  unfold tailWord_815955
  simp only [CollatzResearch.WordTrace]
  refine ⟨29760323758941863864569319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19840215839294575909712879 29760323758941863864569319)
  ·
    refine ⟨44640485638412795796853979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29760323758941863864569319 44640485638412795796853979)
    ·
      refine ⟨66960728457619193695280969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44640485638412795796853979 66960728457619193695280969)
      ·
        refine ⟨50220546343214395271460727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66960728457619193695280969 50220546343214395271460727)
        ·
          refine ⟨75330819514821592907191091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50220546343214395271460727 75330819514821592907191091)
          ·
            refine ⟨112996229272232389360786637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75330819514821592907191091 112996229272232389360786637)
            ·
              refine ⟨42373585977087146010294989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112996229272232389360786637 42373585977087146010294989)
              ·
                refine ⟨15890094741407679753860621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42373585977087146010294989 15890094741407679753860621)
                ·
                  refine ⟨5958785528027879907697733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15890094741407679753860621 5958785528027879907697733)
                  ·
                    refine ⟨1117272286505227482693325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5958785528027879907697733 1117272286505227482693325)
                    ·
                      refine ⟨418977107439460306009997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1117272286505227482693325 418977107439460306009997)
                      ·
                        rfl

theorem cell23_815955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 3].length) (baseStart_815955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815955 prefixEnd_815955 := by exact prefixLift 815955
  have htrace : WordTrace (prefixWord ++ tailWord_815955) baseStart_815955 baseEnd_815955 := by
    simpa [prefixWord, tailWord_815955, baseEnd_815955] using wordTrace_append hprefix tailTrace_815955
  have hstable : (prefixWord ++ tailWord_815955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815955).length < 2 ^ (prefixWord ++ tailWord_815955).sum := by decide
  have hdescent : baseEnd_815955 < baseStart_815955 := by decide
  rcases family_descends (prefixWord ++ tailWord_815955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815989 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_815989 : Nat := 118140960795 + 815989 * 2 ^ 59
def prefixEnd_815989 : Nat := 4983230072969 + 3 ^ 40 * 815989 * 2
def baseEnd_815989 : Nat := 418994565781713172984841

theorem tailTrace_815989 : CollatzResearch.WordTrace tailWord_815989 prefixEnd_815989 418994565781713172984841 := by
  unfold tailWord_815989
  simp only [CollatzResearch.WordTrace]
  refine ⟨29761563840818687671307021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19841042560545791780871347 29761563840818687671307021)
  ·
    refine ⟨11160586440307007876740133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29761563840818687671307021 11160586440307007876740133)
    ·
      refine ⟨2092609957557563976888775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11160586440307007876740133 2092609957557563976888775)
      ·
        refine ⟨3138914936336345965333163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2092609957557563976888775 3138914936336345965333163)
        ·
          refine ⟨4708372404504518947999745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3138914936336345965333163 4708372404504518947999745)
          ·
            refine ⟨3531279303378389210999809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4708372404504518947999745 3531279303378389210999809)
            ·
              refine ⟨2648459477533791908249857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3531279303378389210999809 2648459477533791908249857)
              ·
                refine ⟨1986344608150343931187393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648459477533791908249857 1986344608150343931187393)
                ·
                  refine ⟨1489758456112757948390545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1986344608150343931187393 1489758456112757948390545)
                  ·
                    refine ⟨1117318842084568461292909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1489758456112757948390545 1117318842084568461292909)
                    ·
                      refine ⟨418994565781713172984841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1117318842084568461292909 418994565781713172984841)
                      ·
                        rfl

theorem cell23_815989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_815989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_815989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_815989 prefixEnd_815989 := by exact prefixLift 815989
  have htrace : WordTrace (prefixWord ++ tailWord_815989) baseStart_815989 baseEnd_815989 := by
    simpa [prefixWord, tailWord_815989, baseEnd_815989] using wordTrace_append hprefix tailTrace_815989
  have hstable : (prefixWord ++ tailWord_815989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815989).length < 2 ^ (prefixWord ++ tailWord_815989).sum := by decide
  have hdescent : baseEnd_815989 < baseStart_815989 := by decide
  rcases family_descends (prefixWord ++ tailWord_815989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816029 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_816029 : Nat := 118140960795 + 816029 * 2 ^ 59
def prefixEnd_816029 : Nat := 4983230072969 + 3 ^ 40 * 816029 * 2
def baseEnd_816029 : Nat := 419015105007893016484657

theorem tailTrace_816029 : CollatzResearch.WordTrace tailWord_816029 prefixEnd_816029 419015105007893016484657 := by
  unfold tailWord_816029
  simp only [CollatzResearch.WordTrace]
  refine ⟨29763022760673774502763141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19842015173782516335175427 29763022760673774502763141)
  ·
    refine ⟨5580566767626332719268089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29763022760673774502763141 5580566767626332719268089)
    ·
      refine ⟨4185425075719749539451067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5580566767626332719268089 4185425075719749539451067)
      ·
        refine ⟨6278137613579624309176601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185425075719749539451067 6278137613579624309176601)
        ·
          refine ⟨4708603210184718231882451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6278137613579624309176601 4708603210184718231882451)
          ·
            refine ⟨7062904815277077347823677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4708603210184718231882451 7062904815277077347823677)
            ·
              refine ⟨2648589305728904005433879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7062904815277077347823677 2648589305728904005433879)
              ·
                refine ⟨3972883958593356008150819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648589305728904005433879 3972883958593356008150819)
                ·
                  refine ⟨5959325937890034012226229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972883958593356008150819 5959325937890034012226229)
                  ·
                    refine ⟨558686806677190688646209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5959325937890034012226229 558686806677190688646209)
                    ·
                      refine ⟨419015105007893016484657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558686806677190688646209 419015105007893016484657)
                      ·
                        rfl

theorem cell23_816029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_816029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816029 prefixEnd_816029 := by exact prefixLift 816029
  have htrace : WordTrace (prefixWord ++ tailWord_816029) baseStart_816029 baseEnd_816029 := by
    simpa [prefixWord, tailWord_816029, baseEnd_816029] using wordTrace_append hprefix tailTrace_816029
  have hstable : (prefixWord ++ tailWord_816029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816029).length < 2 ^ (prefixWord ++ tailWord_816029).sum := by decide
  have hdescent : baseEnd_816029 < baseStart_816029 := by decide
  rcases family_descends (prefixWord ++ tailWord_816029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816076 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 3, 2, 2]
def baseStart_816076 : Nat := 118140960795 + 816076 * 2 ^ 59
def prefixEnd_816076 : Nat := 4983230072969 + 3 ^ 40 * 816076 * 2
def baseEnd_816076 : Nat := 419039238598654332596941

theorem tailTrace_816076 : CollatzResearch.WordTrace tailWord_816076 prefixEnd_816076 419039238598654332596941 := by
  unfold tailWord_816076
  simp only [CollatzResearch.WordTrace]
  refine ⟨14882368495751750764862041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19843157994335667686482721 14882368495751750764862041)
  ·
    refine ⟨11161776371813813073646531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14882368495751750764862041 11161776371813813073646531)
    ·
      refine ⟨16742664557720719610469797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11161776371813813073646531 16742664557720719610469797)
      ·
        refine ⟨3139249604572634926963087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16742664557720719610469797 3139249604572634926963087)
        ·
          refine ⟨4708874406858952390444631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3139249604572634926963087 4708874406858952390444631)
          ·
            refine ⟨7063311610288428585666947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4708874406858952390444631 7063311610288428585666947)
            ·
              refine ⟨10594967415432642878500421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063311610288428585666947 10594967415432642878500421)
              ·
                refine ⟨1986556390393620539718829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10594967415432642878500421 1986556390393620539718829)
                ·
                  refine ⟨744958646397607702394561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1986556390393620539718829 744958646397607702394561)
                  ·
                    refine ⟨558718984798205776795921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 744958646397607702394561 558718984798205776795921)
                    ·
                      refine ⟨419039238598654332596941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558718984798205776795921 419039238598654332596941)
                      ·
                        rfl

theorem cell23_816076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_816076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816076 prefixEnd_816076 := by exact prefixLift 816076
  have htrace : WordTrace (prefixWord ++ tailWord_816076) baseStart_816076 baseEnd_816076 := by
    simpa [prefixWord, tailWord_816076, baseEnd_816076] using wordTrace_append hprefix tailTrace_816076
  have hstable : (prefixWord ++ tailWord_816076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816076).length < 2 ^ (prefixWord ++ tailWord_816076).sum := by decide
  have hdescent : baseEnd_816076 < baseStart_816076 := by decide
  rcases family_descends (prefixWord ++ tailWord_816076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816079 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 1, 2, 3]
def baseStart_816079 : Nat := 118140960795 + 816079 * 2 ^ 59
def prefixEnd_816079 : Nat := 4983230072969 + 3 ^ 40 * 816079 * 2
def baseEnd_816079 : Nat := 419040779040617820859427

theorem tailTrace_816079 : CollatzResearch.WordTrace tailWord_816079 prefixEnd_816079 419040779040617820859427 := by
  unfold tailWord_816079
  simp only [CollatzResearch.WordTrace]
  refine ⟨29764846410492633042083291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19843230940328422028055527 29764846410492633042083291)
  ·
    refine ⟨44647269615738949563124937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29764846410492633042083291 44647269615738949563124937)
    ·
      refine ⟨33485452211804212172343703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44647269615738949563124937 33485452211804212172343703)
      ·
        refine ⟨50228178317706318258515555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33485452211804212172343703 50228178317706318258515555)
        ·
          refine ⟨75342267476559477387773333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50228178317706318258515555 75342267476559477387773333)
          ·
            refine ⟨3531668787963725502551875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75342267476559477387773333 3531668787963725502551875)
            ·
              refine ⟨5297503181945588253827813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531668787963725502551875 5297503181945588253827813)
              ·
                refine ⟨993281846614797797592715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5297503181945588253827813 993281846614797797592715)
                ·
                  refine ⟨1489922769922196696389073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993281846614797797592715 1489922769922196696389073)
                  ·
                    refine ⟨1117442077441647522291805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1489922769922196696389073 1117442077441647522291805)
                    ·
                      refine ⟨419040779040617820859427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1117442077441647522291805 419040779040617820859427)
                      ·
                        rfl

theorem cell23_816079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 2, 3].length) (baseStart_816079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816079 prefixEnd_816079 := by exact prefixLift 816079
  have htrace : WordTrace (prefixWord ++ tailWord_816079) baseStart_816079 baseEnd_816079 := by
    simpa [prefixWord, tailWord_816079, baseEnd_816079] using wordTrace_append hprefix tailTrace_816079
  have hstable : (prefixWord ++ tailWord_816079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816079).length < 2 ^ (prefixWord ++ tailWord_816079).sum := by decide
  have hdescent : baseEnd_816079 < baseStart_816079 := by decide
  rcases family_descends (prefixWord ++ tailWord_816079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816086 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_816086 : Nat := 118140960795 + 816086 * 2 ^ 59
def prefixEnd_816086 : Nat := 4983230072969 + 3 ^ 40 * 816086 * 2
def baseEnd_816086 : Nat := 139681457801733097823965

theorem tailTrace_816086 : CollatzResearch.WordTrace tailWord_816086 prefixEnd_816086 139681457801733097823965 := by
  unfold tailWord_816086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860318857591704577349257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19843401147644848825058741 1860318857591704577349257)
  ·
    refine ⟨1395239143193778433011943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1860318857591704577349257 1395239143193778433011943)
    ·
      refine ⟨2092858714790667649517915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395239143193778433011943 2092858714790667649517915)
      ·
        refine ⟨3139288072186001474276873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2092858714790667649517915 3139288072186001474276873)
        ·
          refine ⟨2354466054139501105707655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3139288072186001474276873 2354466054139501105707655)
          ·
            refine ⟨3531699081209251658561483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354466054139501105707655 3531699081209251658561483)
            ·
              refine ⟨5297548621813877487842225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531699081209251658561483 5297548621813877487842225)
              ·
                refine ⟨3973161466360408115881669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5297548621813877487842225 3973161466360408115881669)
                ·
                  refine ⟨744967774942576521727813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3973161466360408115881669 744967774942576521727813)
                  ·
                    refine ⟨139681457801733097823965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 744967774942576521727813 139681457801733097823965)
                    ·
                      rfl

theorem cell23_816086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_816086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816086 prefixEnd_816086 := by exact prefixLift 816086
  have htrace : WordTrace (prefixWord ++ tailWord_816086) baseStart_816086 baseEnd_816086 := by
    simpa [prefixWord, tailWord_816086, baseEnd_816086] using wordTrace_append hprefix tailTrace_816086
  have hstable : (prefixWord ++ tailWord_816086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816086).length < 2 ^ (prefixWord ++ tailWord_816086).sum := by decide
  have hdescent : baseEnd_816086 < baseStart_816086 := by decide
  rcases family_descends (prefixWord ++ tailWord_816086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816110 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_816110 : Nat := 118140960795 + 816110 * 2 ^ 59
def prefixEnd_816110 : Nat := 4983230072969 + 3 ^ 40 * 816110 * 2
def baseEnd_816110 : Nat := 419056696940907199571785

theorem tailTrace_816110 : CollatzResearch.WordTrace tailWord_816110 prefixEnd_816110 419056696940907199571785 := by
  unfold tailWord_816110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720747134172540667057723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19843984715586883557641189 3720747134172540667057723)
  ·
    refine ⟨5581120701258811000586585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3720747134172540667057723 5581120701258811000586585)
    ·
      refine ⟨4185840525944108250439939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5581120701258811000586585 4185840525944108250439939)
      ·
        refine ⟨6278760788916162375659909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185840525944108250439939 6278760788916162375659909)
        ·
          refine ⟨1177267647921780445436233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6278760788916162375659909 1177267647921780445436233)
          ·
            refine ⟨882950735941335334077175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1177267647921780445436233 882950735941335334077175)
            ·
              refine ⟨1324426103912003001115763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882950735941335334077175 1324426103912003001115763)
              ·
                refine ⟨1986639155868004501673645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324426103912003001115763 1986639155868004501673645)
                ·
                  refine ⟨744989683450501688127617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1986639155868004501673645 744989683450501688127617)
                  ·
                    refine ⟨558742262587876266095713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 744989683450501688127617 558742262587876266095713)
                    ·
                      refine ⟨419056696940907199571785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558742262587876266095713 419056696940907199571785)
                      ·
                        rfl

theorem cell23_816110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_816110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816110 prefixEnd_816110 := by exact prefixLift 816110
  have htrace : WordTrace (prefixWord ++ tailWord_816110) baseStart_816110 baseEnd_816110 := by
    simpa [prefixWord, tailWord_816110, baseEnd_816110] using wordTrace_append hprefix tailTrace_816110
  have hstable : (prefixWord ++ tailWord_816110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816110).length < 2 ^ (prefixWord ++ tailWord_816110).sum := by decide
  have hdescent : baseEnd_816110 < baseStart_816110 := by decide
  rcases family_descends (prefixWord ++ tailWord_816110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816136 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 3, 3, 2]
def baseStart_816136 : Nat := 118140960795 + 816136 * 2 ^ 59
def prefixEnd_816136 : Nat := 4983230072969 + 3 ^ 40 * 816136 * 2
def baseEnd_816136 : Nat := 419070047437924097846665

theorem tailTrace_816136 : CollatzResearch.WordTrace tailWord_816136 prefixEnd_816136 419070047437924097846665 := by
  unfold tailWord_816136
  simp only [CollatzResearch.WordTrace]
  refine ⟨14883462685643065888454131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19844616914190754517938841 14883462685643065888454131)
  ·
    refine ⟨22325194028464598832681197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14883462685643065888454131 22325194028464598832681197)
    ·
      refine ⟨8371947760674224562255449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22325194028464598832681197 8371947760674224562255449)
      ·
        refine ⟨6278960820505668421691587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8371947760674224562255449 6278960820505668421691587)
        ·
          refine ⟨9418441230758502632537381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6278960820505668421691587 9418441230758502632537381)
          ·
            refine ⟨1765957730767219243600759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9418441230758502632537381 1765957730767219243600759)
            ·
              refine ⟨2648936596150828865401139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765957730767219243600759 2648936596150828865401139)
              ·
                refine ⟨3973404894226243298101709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648936596150828865401139 3973404894226243298101709)
                ·
                  refine ⟨1490026835334841236788141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3973404894226243298101709 1490026835334841236788141)
                  ·
                    refine ⟨558760063250565463795553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490026835334841236788141 558760063250565463795553)
                    ·
                      refine ⟨419070047437924097846665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558760063250565463795553 419070047437924097846665)
                      ·
                        rfl

theorem cell23_816136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_816136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816136 prefixEnd_816136 := by exact prefixLift 816136
  have htrace : WordTrace (prefixWord ++ tailWord_816136) baseStart_816136 baseEnd_816136 := by
    simpa [prefixWord, tailWord_816136, baseEnd_816136] using wordTrace_append hprefix tailTrace_816136
  have hstable : (prefixWord ++ tailWord_816136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816136).length < 2 ^ (prefixWord ++ tailWord_816136).sum := by decide
  have hdescent : baseEnd_816136 < baseStart_816136 := by decide
  rcases family_descends (prefixWord ++ tailWord_816136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816160 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 2, 1, 3]
def baseStart_816160 : Nat := 118140960795 + 816160 * 2 ^ 59
def prefixEnd_816160 : Nat := 4983230072969 + 3 ^ 40 * 816160 * 2
def baseEnd_816160 : Nat := 419082370973632003946555

theorem tailTrace_816160 : CollatzResearch.WordTrace tailWord_816160 prefixEnd_816160 419082370973632003946555 := by
  unfold tailWord_816160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14883900361599591937890967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19845200482132789250521289 14883900361599591937890967)
  ·
    refine ⟨22325850542399387906836451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14883900361599591937890967 22325850542399387906836451)
    ·
      refine ⟨33488775813599081860254677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22325850542399387906836451 33488775813599081860254677)
      ·
        refine ⟨784893183131228481099719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33488775813599081860254677 784893183131228481099719)
        ·
          refine ⟨1177339774696842721649579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784893183131228481099719 1177339774696842721649579)
          ·
            refine ⟨1766009662045264082474369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177339774696842721649579 1766009662045264082474369)
            ·
              refine ⟨1324507246533948061855777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766009662045264082474369 1324507246533948061855777)
              ·
                refine ⟨993380434900461046391833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1324507246533948061855777 993380434900461046391833)
                ·
                  refine ⟨745035326175345784793875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 993380434900461046391833 745035326175345784793875)
                  ·
                    refine ⟨1117552989263018677190813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 745035326175345784793875 1117552989263018677190813)
                    ·
                      refine ⟨419082370973632003946555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1117552989263018677190813 419082370973632003946555)
                      ·
                        rfl

theorem cell23_816160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_816160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816160 prefixEnd_816160 := by exact prefixLift 816160
  have htrace : WordTrace (prefixWord ++ tailWord_816160) baseStart_816160 baseEnd_816160 := by
    simpa [prefixWord, tailWord_816160, baseEnd_816160] using wordTrace_append hprefix tailTrace_816160
  have hstable : (prefixWord ++ tailWord_816160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816160).length < 2 ^ (prefixWord ++ tailWord_816160).sum := by decide
  have hdescent : baseEnd_816160 < baseStart_816160 := by decide
  rcases family_descends (prefixWord ++ tailWord_816160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816172 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 7]
def baseStart_816172 : Nat := 118140960795 + 816172 * 2 ^ 59
def prefixEnd_816172 : Nat := 4983230072969 + 3 ^ 40 * 816172 * 2
def baseEnd_816172 : Nat := 46565392526831772999611

theorem tailTrace_816172 : CollatzResearch.WordTrace tailWord_816172 prefixEnd_816172 46565392526831772999611 := by
  unfold tailWord_816172
  simp only [CollatzResearch.WordTrace]
  refine ⟨14884119199577854962609385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19845492266103806616812513 14884119199577854962609385)
  ·
    refine ⟨11163089399683391221957039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14884119199577854962609385 11163089399683391221957039)
    ·
      refine ⟨16744634099525086832935559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11163089399683391221957039 16744634099525086832935559)
      ·
        refine ⟨25116951149287630249403339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16744634099525086832935559 25116951149287630249403339)
        ·
          refine ⟨37675426723931445374105009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25116951149287630249403339 37675426723931445374105009)
          ·
            refine ⟨28256570042948584030578757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37675426723931445374105009 28256570042948584030578757)
            ·
              refine ⟨5298106883052859505733517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28256570042948584030578757 5298106883052859505733517)
              ·
                refine ⟨1986790081144822314650069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5298106883052859505733517 1986790081144822314650069)
                ·
                  refine ⟨46565392526831772999611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1986790081144822314650069 46565392526831772999611)
                  ·
                    rfl

theorem cell23_816172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_816172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816172 prefixEnd_816172 := by exact prefixLift 816172
  have htrace : WordTrace (prefixWord ++ tailWord_816172) baseStart_816172 baseEnd_816172 := by
    simpa [prefixWord, tailWord_816172, baseEnd_816172] using wordTrace_append hprefix tailTrace_816172
  have hstable : (prefixWord ++ tailWord_816172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816172).length < 2 ^ (prefixWord ++ tailWord_816172).sum := by decide
  have hdescent : baseEnd_816172 < baseStart_816172 := by decide
  rcases family_descends (prefixWord ++ tailWord_816172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816189 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 7]
def baseStart_816189 : Nat := 118140960795 + 816189 * 2 ^ 59
def prefixEnd_816189 : Nat := 4983230072969 + 3 ^ 40 * 816189 * 2
def baseEnd_816189 : Nat := 46566362434734710053769

theorem tailTrace_816189 : CollatzResearch.WordTrace tailWord_816189 prefixEnd_816189 46566362434734710053769 := by
  unfold tailWord_816189
  simp only [CollatzResearch.WordTrace]
  refine ⟨29768858440094121828587621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19845905626729414552391747 29768858440094121828587621)
  ·
    refine ⟨5581660957517647842860179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29768858440094121828587621 5581660957517647842860179)
    ·
      refine ⟨8372491436276471764290269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5581660957517647842860179 8372491436276471764290269)
      ·
        refine ⟨3139684288603676911608851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8372491436276471764290269 3139684288603676911608851)
        ·
          refine ⟨4709526432905515367413277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3139684288603676911608851 4709526432905515367413277)
          ·
            refine ⟨1766072412339568262779979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4709526432905515367413277 1766072412339568262779979)
            ·
              refine ⟨2649108618509352394169969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766072412339568262779979 2649108618509352394169969)
              ·
                refine ⟨1986831463882014295627477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649108618509352394169969 1986831463882014295627477)
                ·
                  refine ⟨46566362434734710053769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1986831463882014295627477 46566362434734710053769)
                  ·
                    rfl

theorem cell23_816189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_816189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816189 prefixEnd_816189 := by exact prefixLift 816189
  have htrace : WordTrace (prefixWord ++ tailWord_816189) baseStart_816189 baseEnd_816189 := by
    simpa [prefixWord, tailWord_816189, baseEnd_816189] using wordTrace_append hprefix tailTrace_816189
  have hstable : (prefixWord ++ tailWord_816189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816189).length < 2 ^ (prefixWord ++ tailWord_816189).sum := by decide
  have hdescent : baseEnd_816189 < baseStart_816189 := by decide
  rcases family_descends (prefixWord ++ tailWord_816189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816206 : List Nat := [4, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_816206 : Nat := 118140960795 + 816206 * 2 ^ 59
def prefixEnd_816206 : Nat := 4983230072969 + 3 ^ 40 * 816206 * 2
def baseEnd_816206 : Nat := 46567332342637647107927

theorem tailTrace_816206 : CollatzResearch.WordTrace tailWord_816206 prefixEnd_816206 46567332342637647107927 := by
  unfold tailWord_816206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3721184810129066716494559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19846318987355022487970981 3721184810129066716494559)
  ·
    refine ⟨5581777215193600074741839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3721184810129066716494559 5581777215193600074741839)
    ·
      refine ⟨8372665822790400112112759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5581777215193600074741839 8372665822790400112112759)
      ·
        refine ⟨12558998734185600168169139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8372665822790400112112759 12558998734185600168169139)
        ·
          refine ⟨18838498101278400252253709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12558998734185600168169139 18838498101278400252253709)
          ·
            refine ⟨7064436787979400094595141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18838498101278400252253709 7064436787979400094595141)
            ·
              refine ⟨1324581897746137517736589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7064436787979400094595141 1324581897746137517736589)
              ·
                refine ⟨496718211654801569151221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1324581897746137517736589 496718211654801569151221)
                ·
                  refine ⟨46567332342637647107927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 496718211654801569151221 46567332342637647107927)
                  ·
                    rfl

theorem cell23_816206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_816206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816206 prefixEnd_816206 := by exact prefixLift 816206
  have htrace : WordTrace (prefixWord ++ tailWord_816206) baseStart_816206 baseEnd_816206 := by
    simpa [prefixWord, tailWord_816206, baseEnd_816206] using wordTrace_append hprefix tailTrace_816206
  have hstable : (prefixWord ++ tailWord_816206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816206).length < 2 ^ (prefixWord ++ tailWord_816206).sum := by decide
  have hdescent : baseEnd_816206 < baseStart_816206 := by decide
  rcases family_descends (prefixWord ++ tailWord_816206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816259 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 3]
def baseStart_816259 : Nat := 118140960795 + 816259 * 2 ^ 59
def prefixEnd_816259 : Nat := 4983230072969 + 3 ^ 40 * 816259 * 2
def baseEnd_816259 : Nat := 419133205558427116608599

theorem tailTrace_816259 : CollatzResearch.WordTrace tailWord_816259 prefixEnd_816259 419133205558427116608599 := by
  unfold tailWord_816259
  simp only [CollatzResearch.WordTrace]
  refine ⟨29771411549840523783635831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19847607699893682522423887 29771411549840523783635831)
  ·
    refine ⟨44657117324760785675453747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29771411549840523783635831 44657117324760785675453747)
    ·
      refine ⟨66985675987141178513180621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44657117324760785675453747 66985675987141178513180621)
      ·
        refine ⟨25119628495177941942442733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66985675987141178513180621 25119628495177941942442733)
        ·
          refine ⟨9419860685691728228416025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25119628495177941942442733 9419860685691728228416025)
          ·
            refine ⟨7064895514268796171312019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9419860685691728228416025 7064895514268796171312019)
            ·
              refine ⟨10597343271403194256968029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064895514268796171312019 10597343271403194256968029)
              ·
                refine ⟨3974003726776197846363011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10597343271403194256968029 3974003726776197846363011)
                ·
                  refine ⟨5961005590164296769544517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974003726776197846363011 5961005590164296769544517)
                  ·
                    refine ⟨1117688548155805644289597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5961005590164296769544517 1117688548155805644289597)
                    ·
                      refine ⟨419133205558427116608599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1117688548155805644289597 419133205558427116608599)
                      ·
                        rfl

theorem cell23_816259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_816259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816259 prefixEnd_816259 := by exact prefixLift 816259
  have htrace : WordTrace (prefixWord ++ tailWord_816259) baseStart_816259 baseEnd_816259 := by
    simpa [prefixWord, tailWord_816259, baseEnd_816259] using wordTrace_append hprefix tailTrace_816259
  have hstable : (prefixWord ++ tailWord_816259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816259).length < 2 ^ (prefixWord ++ tailWord_816259).sum := by decide
  have hdescent : baseEnd_816259 < baseStart_816259 := by decide
  rcases family_descends (prefixWord ++ tailWord_816259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816279 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 8]
def baseStart_816279 : Nat := 118140960795 + 816279 * 2 ^ 59
def prefixEnd_816279 : Nat := 4983230072969 + 3 ^ 40 * 816279 * 2
def baseEnd_816279 : Nat := 46571497241279670928723

theorem tailTrace_816279 : CollatzResearch.WordTrace tailWord_816279 prefixEnd_816279 46571497241279670928723 := by
  unfold tailWord_816279
  simp only [CollatzResearch.WordTrace]
  refine ⟨29772141009768067199363891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19848094006512044799575927 29772141009768067199363891)
  ·
    refine ⟨44658211514652100799045837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29772141009768067199363891 44658211514652100799045837)
    ·
      refine ⟨16746829317994537799642189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44658211514652100799045837 16746829317994537799642189)
      ·
        refine ⟨6280060994247951674865821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16746829317994537799642189 6280060994247951674865821)
        ·
          refine ⟨2355022872842981878074683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6280060994247951674865821 2355022872842981878074683)
          ·
            refine ⟨3532534309264472817112025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355022872842981878074683 3532534309264472817112025)
            ·
              refine ⟨2649400731948354612834019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3532534309264472817112025 2649400731948354612834019)
              ·
                refine ⟨3974101097922531919251029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649400731948354612834019 3974101097922531919251029)
                ·
                  refine ⟨46571497241279670928723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3974101097922531919251029 46571497241279670928723)
                  ·
                    rfl

theorem cell23_816279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 8].length) (baseStart_816279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816279 prefixEnd_816279 := by exact prefixLift 816279
  have htrace : WordTrace (prefixWord ++ tailWord_816279) baseStart_816279 baseEnd_816279 := by
    simpa [prefixWord, tailWord_816279, baseEnd_816279] using wordTrace_append hprefix tailTrace_816279
  have hstable : (prefixWord ++ tailWord_816279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816279).length < 2 ^ (prefixWord ++ tailWord_816279).sum := by decide
  have hdescent : baseEnd_816279 < baseStart_816279 := by decide
  rcases family_descends (prefixWord ++ tailWord_816279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816334 : List Nat := [4, 1, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_816334 : Nat := 118140960795 + 816334 * 2 ^ 59
def prefixEnd_816334 : Nat := 4983230072969 + 3 ^ 40 * 816334 * 2
def baseEnd_816334 : Nat := 139723905535838107723585

theorem tailTrace_816334 : CollatzResearch.WordTrace tailWord_816334 prefixEnd_816334 139723905535838107723585 := by
  unfold tailWord_816334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3721768378071101449077007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19849431349712541061744037 3721768378071101449077007)
  ·
    refine ⟨5582652567106652173615511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3721768378071101449077007 5582652567106652173615511)
    ·
      refine ⟨8373978850659978260423267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5582652567106652173615511 8373978850659978260423267)
      ·
        refine ⟨12560968275989967390634901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8373978850659978260423267 12560968275989967390634901)
        ·
          refine ⟨588795387937029721436011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12560968275989967390634901 588795387937029721436011)
          ·
            refine ⟨883193081905544582154017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588795387937029721436011 883193081905544582154017)
            ·
              refine ⟨662394811429158436615513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883193081905544582154017 662394811429158436615513)
              ·
                refine ⟨496796108571868827461635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662394811429158436615513 496796108571868827461635)
                ·
                  refine ⟨745194162857803241192453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496796108571868827461635 745194162857803241192453)
                  ·
                    refine ⟨139723905535838107723585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 745194162857803241192453 139723905535838107723585)
                    ·
                      rfl

theorem cell23_816334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_816334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816334 prefixEnd_816334 := by exact prefixLift 816334
  have htrace : WordTrace (prefixWord ++ tailWord_816334) baseStart_816334 baseEnd_816334 := by
    simpa [prefixWord, tailWord_816334, baseEnd_816334] using wordTrace_append hprefix tailTrace_816334
  have hstable : (prefixWord ++ tailWord_816334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816334).length < 2 ^ (prefixWord ++ tailWord_816334).sum := by decide
  have hdescent : baseEnd_816334 < baseStart_816334 := by decide
  rcases family_descends (prefixWord ++ tailWord_816334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816346 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2]
def baseStart_816346 : Nat := 118140960795 + 816346 * 2 ^ 59
def prefixEnd_816346 : Nat := 4983230072969 + 3 ^ 40 * 816346 * 2
def baseEnd_816346 : Nat := 419177878375368276220699

theorem tailTrace_816346 : CollatzResearch.WordTrace tailWord_816346 prefixEnd_816346 419177878375368276220699 := by
  unfold tailWord_816346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443646175131334410513223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19849723133683558428035261 7443646175131334410513223)
  ·
    refine ⟨11165469262697001615769835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7443646175131334410513223 11165469262697001615769835)
    ·
      refine ⟨16748203894045502423654753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11165469262697001615769835 16748203894045502423654753)
      ·
        refine ⟨12561152920534126817741065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16748203894045502423654753 12561152920534126817741065)
        ·
          refine ⟨9420864690400595113305799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12561152920534126817741065 9420864690400595113305799)
          ·
            refine ⟨14131297035600892669958699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9420864690400595113305799 14131297035600892669958699)
            ·
              refine ⟨21196945553401339004938049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14131297035600892669958699 21196945553401339004938049)
              ·
                refine ⟨15897709165051004253703537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21196945553401339004938049 15897709165051004253703537)
                ·
                  refine ⟨11923281873788253190277653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15897709165051004253703537 11923281873788253190277653)
                  ·
                    refine ⟨558903837833824368294265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11923281873788253190277653 558903837833824368294265)
                    ·
                      refine ⟨419177878375368276220699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558903837833824368294265 419177878375368276220699)
                      ·
                        rfl

theorem cell23_816346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_816346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816346 prefixEnd_816346 := by exact prefixLift 816346
  have htrace : WordTrace (prefixWord ++ tailWord_816346) baseStart_816346 baseEnd_816346 := by
    simpa [prefixWord, tailWord_816346, baseEnd_816346] using wordTrace_append hprefix tailTrace_816346
  have hstable : (prefixWord ++ tailWord_816346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816346).length < 2 ^ (prefixWord ++ tailWord_816346).sum := by decide
  have hdescent : baseEnd_816346 < baseStart_816346 := by decide
  rcases family_descends (prefixWord ++ tailWord_816346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816363 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 5, 2, 2]
def baseStart_816363 : Nat := 118140960795 + 816363 * 2 ^ 59
def prefixEnd_816363 : Nat := 4983230072969 + 3 ^ 40 * 816363 * 2
def baseEnd_816363 : Nat := 419186607546494709708121

theorem tailTrace_816363 : CollatzResearch.WordTrace tailWord_816363 prefixEnd_816363 419186607546494709708121 := by
  unfold tailWord_816363
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775204741463749545421743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19850136494309166363614495 29775204741463749545421743)
  ·
    refine ⟨44662807112195624318132615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29775204741463749545421743 44662807112195624318132615)
    ·
      refine ⟨66994210668293436477198923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44662807112195624318132615 66994210668293436477198923)
      ·
        refine ⟨100491316002440154715798385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66994210668293436477198923 100491316002440154715798385)
        ·
          refine ⟨75368487001830116036848789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100491316002440154715798385 75368487001830116036848789)
          ·
            refine ⟨3532897828210786689227287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75368487001830116036848789 3532897828210786689227287)
            ·
              refine ⟨5299346742316180033840931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532897828210786689227287 5299346742316180033840931)
              ·
                refine ⟨7949020113474270050761397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299346742316180033840931 7949020113474270050761397)
                ·
                  refine ⟨745220635638212817258881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7949020113474270050761397 745220635638212817258881)
                  ·
                    refine ⟨558915476728659612944161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 745220635638212817258881 558915476728659612944161)
                    ·
                      refine ⟨419186607546494709708121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558915476728659612944161 419186607546494709708121)
                      ·
                        rfl

theorem cell23_816363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 2, 2].length) (baseStart_816363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816363 prefixEnd_816363 := by exact prefixLift 816363
  have htrace : WordTrace (prefixWord ++ tailWord_816363) baseStart_816363 baseEnd_816363 := by
    simpa [prefixWord, tailWord_816363, baseEnd_816363] using wordTrace_append hprefix tailTrace_816363
  have hstable : (prefixWord ++ tailWord_816363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816363).length < 2 ^ (prefixWord ++ tailWord_816363).sum := by decide
  have hdescent : baseEnd_816363 < baseStart_816363 := by decide
  rcases family_descends (prefixWord ++ tailWord_816363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816367 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 2, 3, 2]
def baseStart_816367 : Nat := 118140960795 + 816367 * 2 ^ 59
def prefixEnd_816367 : Nat := 4983230072969 + 3 ^ 40 * 816367 * 2
def baseEnd_816367 : Nat := 419188661469112694058103

theorem tailTrace_816367 : CollatzResearch.WordTrace tailWord_816367 prefixEnd_816367 419188661469112694058103 := by
  unfold tailWord_816367
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775350633449258228567355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19850233755632838819044903 29775350633449258228567355)
  ·
    refine ⟨44663025950173887342851033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29775350633449258228567355 44663025950173887342851033)
    ·
      refine ⟨33497269462630415507138275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44663025950173887342851033 33497269462630415507138275)
      ·
        refine ⟨50245904193945623260707413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33497269462630415507138275 50245904193945623260707413)
        ·
          refine ⟨588819189772800272586415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 50245904193945623260707413 588819189772800272586415)
          ·
            refine ⟨883228784659200408879623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588819189772800272586415 883228784659200408879623)
            ·
              refine ⟨1324843176988800613319435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883228784659200408879623 1324843176988800613319435)
              ·
                refine ⟨1987264765483200919979153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324843176988800613319435 1987264765483200919979153)
                ·
                  refine ⟨1490448574112400689984365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1987264765483200919979153 1490448574112400689984365)
                  ·
                    refine ⟨558918215292150258744137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490448574112400689984365 558918215292150258744137)
                    ·
                      refine ⟨419188661469112694058103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 558918215292150258744137 419188661469112694058103)
                      ·
                        rfl

theorem cell23_816367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 2, 3, 2].length) (baseStart_816367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816367 prefixEnd_816367 := by exact prefixLift 816367
  have htrace : WordTrace (prefixWord ++ tailWord_816367) baseStart_816367 baseEnd_816367 := by
    simpa [prefixWord, tailWord_816367, baseEnd_816367] using wordTrace_append hprefix tailTrace_816367
  have hstable : (prefixWord ++ tailWord_816367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816367).length < 2 ^ (prefixWord ++ tailWord_816367).sum := by decide
  have hdescent : baseEnd_816367 < baseStart_816367 := by decide
  rcases family_descends (prefixWord ++ tailWord_816367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816383 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 1, 2, 3]
def baseStart_816383 : Nat := 118140960795 + 816383 * 2 ^ 59
def prefixEnd_816383 : Nat := 4983230072969 + 3 ^ 40 * 816383 * 2
def baseEnd_816383 : Nat := 419196877159584631458029

theorem tailTrace_816383 : CollatzResearch.WordTrace tailWord_816383 prefixEnd_816383 419196877159584631458029 := by
  unfold tailWord_816383
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775934201391292961149803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19850622800927528640766535 29775934201391292961149803)
  ·
    refine ⟨44663901302086939441724705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29775934201391292961149803 44663901302086939441724705)
    ·
      refine ⟨33497925976565204581293529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44663901302086939441724705 33497925976565204581293529)
      ·
        refine ⟨25123444482423903435970147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33497925976565204581293529 25123444482423903435970147)
        ·
          refine ⟨37685166723635855153955221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25123444482423903435970147 37685166723635855153955221)
          ·
            refine ⟨1766492190170430710341651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37685166723635855153955221 1766492190170430710341651)
            ·
              refine ⟨2649738285255646065512477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766492190170430710341651 2649738285255646065512477)
              ·
                refine ⟨993651856970867274567179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2649738285255646065512477 993651856970867274567179)
                ·
                  refine ⟨1490477785456300911850769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993651856970867274567179 1490477785456300911850769)
                  ·
                    refine ⟨1117858339092225683888077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1490477785456300911850769 1117858339092225683888077)
                    ·
                      refine ⟨419196877159584631458029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1117858339092225683888077 419196877159584631458029)
                      ·
                        rfl

theorem cell23_816383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_816383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816383 prefixEnd_816383 := by exact prefixLift 816383
  have htrace : WordTrace (prefixWord ++ tailWord_816383) baseStart_816383 baseEnd_816383 := by
    simpa [prefixWord, tailWord_816383, baseEnd_816383] using wordTrace_append hprefix tailTrace_816383
  have hstable : (prefixWord ++ tailWord_816383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816383).length < 2 ^ (prefixWord ++ tailWord_816383).sum := by decide
  have hdescent : baseEnd_816383 < baseStart_816383 := by decide
  rcases family_descends (prefixWord ++ tailWord_816383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816409 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_816409 : Nat := 118140960795 + 816409 * 2 ^ 59
def prefixEnd_816409 : Nat := 4983230072969 + 3 ^ 40 * 816409 * 2
def baseEnd_816409 : Nat := 419210227656601529732909

theorem tailTrace_816409 : CollatzResearch.WordTrace tailWord_816409 prefixEnd_816409 419210227656601529732909 := by
  unfold tailWord_816409
  simp only [CollatzResearch.WordTrace]
  refine ⟨29776882499297099401596281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19851254999531399601064187 29776882499297099401596281)
  ·
    refine ⟨22332661874472824551197211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29776882499297099401596281 22332661874472824551197211)
    ·
      refine ⟨33498992811709236826795817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22332661874472824551197211 33498992811709236826795817)
      ·
        refine ⟨25124244608781927620096863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33498992811709236826795817 25124244608781927620096863)
        ·
          refine ⟨37686366913172891430145295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25124244608781927620096863 37686366913172891430145295)
          ·
            refine ⟨56529550369759337145217943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37686366913172891430145295 56529550369759337145217943)
            ·
              refine ⟨84794325554639005717826915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56529550369759337145217943 84794325554639005717826915)
              ·
                refine ⟨127191488331958508576740373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84794325554639005717826915 127191488331958508576740373)
                ·
                  refine ⟨5962101015560555089534705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127191488331958508576740373 5962101015560555089534705)
                  ·
                    refine ⟨4471575761670416317151029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5962101015560555089534705 4471575761670416317151029)
                    ·
                      refine ⟨419210227656601529732909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4471575761670416317151029 419210227656601529732909)
                      ·
                        rfl

theorem cell23_816409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_816409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816409 prefixEnd_816409 := by exact prefixLift 816409
  have htrace : WordTrace (prefixWord ++ tailWord_816409) baseStart_816409 baseEnd_816409 := by
    simpa [prefixWord, tailWord_816409, baseEnd_816409] using wordTrace_append hprefix tailTrace_816409
  have hstable : (prefixWord ++ tailWord_816409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816409).length < 2 ^ (prefixWord ++ tailWord_816409).sum := by decide
  have hdescent : baseEnd_816409 < baseStart_816409 := by decide
  rcases family_descends (prefixWord ++ tailWord_816409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816456 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_816456 : Nat := 118140960795 + 816456 * 2 ^ 59
def prefixEnd_816456 : Nat := 4983230072969 + 3 ^ 40 * 816456 * 2
def baseEnd_816456 : Nat := 419234361247362845845193

theorem tailTrace_816456 : CollatzResearch.WordTrace tailWord_816456 prefixEnd_816456 419234361247362845845193 := by
  unfold tailWord_816456
  simp only [CollatzResearch.WordTrace]
  refine ⟨14889298365063413214278611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19852397820084550952371481 14889298365063413214278611)
  ·
    refine ⟨22333947547595119821417917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14889298365063413214278611 22333947547595119821417917)
    ·
      refine ⟨8375230330348169933031719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22333947547595119821417917 8375230330348169933031719)
      ·
        refine ⟨12562845495522254899547579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8375230330348169933031719 12562845495522254899547579)
        ·
          refine ⟨18844268243283382349321369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12562845495522254899547579 18844268243283382349321369)
          ·
            refine ⟨14133201182462536761991027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18844268243283382349321369 14133201182462536761991027)
            ·
              refine ⟨21199801773693805142986541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14133201182462536761991027 21199801773693805142986541)
              ·
                refine ⟨7949925665135176928619953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21199801773693805142986541 7949925665135176928619953)
                ·
                  refine ⟨5962444248851382696464965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7949925665135176928619953 5962444248851382696464965)
                  ·
                    refine ⟨1117958296659634255587181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5962444248851382696464965 1117958296659634255587181)
                    ·
                      refine ⟨419234361247362845845193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1117958296659634255587181 419234361247362845845193)
                      ·
                        rfl

theorem cell23_816456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_816456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816456 prefixEnd_816456 := by exact prefixLift 816456
  have htrace : WordTrace (prefixWord ++ tailWord_816456) baseStart_816456 baseEnd_816456 := by
    simpa [prefixWord, tailWord_816456, baseEnd_816456] using wordTrace_append hprefix tailTrace_816456
  have hstable : (prefixWord ++ tailWord_816456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816456).length < 2 ^ (prefixWord ++ tailWord_816456).sum := by decide
  have hdescent : baseEnd_816456 < baseStart_816456 := by decide
  rcases family_descends (prefixWord ++ tailWord_816456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816466 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_816466 : Nat := 118140960795 + 816466 * 2 ^ 59
def prefixEnd_816466 : Nat := 4983230072969 + 3 ^ 40 * 816466 * 2
def baseEnd_816466 : Nat := 419239496053907806720147

theorem tailTrace_816466 : CollatzResearch.WordTrace tailWord_816466 prefixEnd_816466 419239496053907806720147 := by
  unfold tailWord_816466
  simp only [CollatzResearch.WordTrace]
  refine ⟨7444740365022649534105313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19852640973393732090947501 7444740365022649534105313)
  ·
    refine ⟨5583555273766987150578985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7444740365022649534105313 5583555273766987150578985)
    ·
      refine ⟨4187666455325240362934239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5583555273766987150578985 4187666455325240362934239)
      ·
        refine ⟨6281499682987860544401359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4187666455325240362934239 6281499682987860544401359)
        ·
          refine ⟨9422249524481790816602039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6281499682987860544401359 9422249524481790816602039)
          ·
            refine ⟨14133374286722686224903059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9422249524481790816602039 14133374286722686224903059)
            ·
              refine ⟨21200061430084029337354589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14133374286722686224903059 21200061430084029337354589)
              ·
                refine ⟨7950023036281511001507971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21200061430084029337354589 7950023036281511001507971)
                ·
                  refine ⟨11925034554422266502261957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7950023036281511001507971 11925034554422266502261957)
                  ·
                    refine ⟨2235943978954174969174117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11925034554422266502261957 2235943978954174969174117)
                    ·
                      refine ⟨419239496053907806720147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2235943978954174969174117 419239496053907806720147)
                      ·
                        rfl

theorem cell23_816466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_816466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816466 prefixEnd_816466 := by exact prefixLift 816466
  have htrace : WordTrace (prefixWord ++ tailWord_816466) baseStart_816466 baseEnd_816466 := by
    simpa [prefixWord, tailWord_816466, baseEnd_816466] using wordTrace_append hprefix tailTrace_816466
  have hstable : (prefixWord ++ tailWord_816466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816466).length < 2 ^ (prefixWord ++ tailWord_816466).sum := by decide
  have hdescent : baseEnd_816466 < baseStart_816466 := by decide
  rcases family_descends (prefixWord ++ tailWord_816466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816540 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_816540 : Nat := 118140960795 + 816540 * 2 ^ 59
def prefixEnd_816540 : Nat := 4983230072969 + 3 ^ 40 * 816540 * 2
def baseEnd_816540 : Nat := 139759164540780172398269

theorem tailTrace_816540 : CollatzResearch.WordTrace tailWord_816540 prefixEnd_816540 139759164540780172398269 := by
  unfold tailWord_816540
  simp only [CollatzResearch.WordTrace]
  refine ⟨14890830230911254387307537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19854440307881672516410049 14890830230911254387307537)
  ·
    refine ⟨11168122673183440790480653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14890830230911254387307537 11168122673183440790480653)
    ·
      refine ⟨4188046002443790296430245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11168122673183440790480653 4188046002443790296430245)
      ·
        refine ⟨785258625458210680580671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4188046002443790296430245 785258625458210680580671)
        ·
          refine ⟨1177887938187316020871007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785258625458210680580671 1177887938187316020871007)
          ·
            refine ⟨1766831907280974031306511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177887938187316020871007 1766831907280974031306511)
            ·
              refine ⟨2650247860921461046959767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766831907280974031306511 2650247860921461046959767)
              ·
                refine ⟨3975371791382191570439651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650247860921461046959767 3975371791382191570439651)
                ·
                  refine ⟨5963057687073287355659477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975371791382191570439651 5963057687073287355659477)
                  ·
                    refine ⟨139759164540780172398269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5963057687073287355659477 139759164540780172398269)
                    ·
                      rfl

theorem cell23_816540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_816540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816540 prefixEnd_816540 := by exact prefixLift 816540
  have htrace : WordTrace (prefixWord ++ tailWord_816540) baseStart_816540 baseEnd_816540 := by
    simpa [prefixWord, tailWord_816540, baseEnd_816540] using wordTrace_append hprefix tailTrace_816540
  have hstable : (prefixWord ++ tailWord_816540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816540).length < 2 ^ (prefixWord ++ tailWord_816540).sum := by decide
  have hdescent : baseEnd_816540 < baseStart_816540 := by decide
  rcases family_descends (prefixWord ++ tailWord_816540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816543 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 4]
def baseStart_816543 : Nat := 118140960795 + 816543 * 2 ^ 59
def prefixEnd_816543 : Nat := 4983230072969 + 3 ^ 40 * 816543 * 2
def baseEnd_816543 : Nat := 419279034064304005457293

theorem tailTrace_816543 : CollatzResearch.WordTrace tailWord_816543 prefixEnd_816543 419279034064304005457293 := by
  unfold tailWord_816543
  simp only [CollatzResearch.WordTrace]
  refine ⟨29781769880811640286974283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19854513253874426857982855 29781769880811640286974283)
  ·
    refine ⟨44672654821217460430461425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29781769880811640286974283 44672654821217460430461425)
    ·
      refine ⟨33504491115913095322846069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44672654821217460430461425 33504491115913095322846069)
      ·
        refine ⟨3141046042116852686516819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33504491115913095322846069 3141046042116852686516819)
        ·
          refine ⟨4711569063175279029775229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3141046042116852686516819 4711569063175279029775229)
          ·
            refine ⟨1766838398690729636165711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4711569063175279029775229 1766838398690729636165711)
            ·
              refine ⟨2650257598036094454248567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766838398690729636165711 2650257598036094454248567)
              ·
                refine ⟨3975386397054141681372851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650257598036094454248567 3975386397054141681372851)
                ·
                  refine ⟨5963079595581212522059277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975386397054141681372851 5963079595581212522059277)
                  ·
                    refine ⟨2236154848342954695772229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5963079595581212522059277 2236154848342954695772229)
                    ·
                      refine ⟨419279034064304005457293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2236154848342954695772229 419279034064304005457293)
                      ·
                        rfl

theorem cell23_816543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_816543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816543 prefixEnd_816543 := by exact prefixLift 816543
  have htrace : WordTrace (prefixWord ++ tailWord_816543) baseStart_816543 baseEnd_816543 := by
    simpa [prefixWord, tailWord_816543, baseEnd_816543] using wordTrace_append hprefix tailTrace_816543
  have hstable : (prefixWord ++ tailWord_816543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816543).length < 2 ^ (prefixWord ++ tailWord_816543).sum := by decide
  have hdescent : baseEnd_816543 < baseStart_816543 := by decide
  rcases family_descends (prefixWord ++ tailWord_816543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816556 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_816556 : Nat := 118140960795 + 816556 * 2 ^ 59
def prefixEnd_816556 : Nat := 4983230072969 + 3 ^ 40 * 816556 * 2
def baseEnd_816556 : Nat := 419285709312812454594733

theorem tailTrace_816556 : CollatzResearch.WordTrace tailWord_816556 prefixEnd_816556 419285709312812454594733 := by
  unfold tailWord_816556
  simp only [CollatzResearch.WordTrace]
  refine ⟨14891122014882271753598761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19854829353176362338131681 14891122014882271753598761)
  ·
    refine ⟨11168341511161703815199071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14891122014882271753598761 11168341511161703815199071)
    ·
      refine ⟨16752512266742555722798607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11168341511161703815199071 16752512266742555722798607)
      ·
        refine ⟨25128768400113833584197911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16752512266742555722798607 25128768400113833584197911)
        ·
          refine ⟨37693152600170750376296867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25128768400113833584197911 37693152600170750376296867)
          ·
            refine ⟨56539728900256125564445301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37693152600170750376296867 56539728900256125564445301)
            ·
              refine ⟨5300599584399011771666747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56539728900256125564445301 5300599584399011771666747)
              ·
                refine ⟨7950899376598517657500121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5300599584399011771666747 7950899376598517657500121)
                ·
                  refine ⟨5963174532448888243125091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7950899376598517657500121 5963174532448888243125091)
                  ·
                    refine ⟨8944761798673332364687637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5963174532448888243125091 8944761798673332364687637)
                    ·
                      refine ⟨419285709312812454594733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8944761798673332364687637 419285709312812454594733)
                      ·
                        rfl

theorem cell23_816556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_816556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816556 prefixEnd_816556 := by exact prefixLift 816556
  have htrace : WordTrace (prefixWord ++ tailWord_816556) baseStart_816556 baseEnd_816556 := by
    simpa [prefixWord, tailWord_816556, baseEnd_816556] using wordTrace_append hprefix tailTrace_816556
  have hstable : (prefixWord ++ tailWord_816556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816556).length < 2 ^ (prefixWord ++ tailWord_816556).sum := by decide
  have hdescent : baseEnd_816556 < baseStart_816556 := by decide
  rcases family_descends (prefixWord ++ tailWord_816556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816563 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 3]
def baseStart_816563 : Nat := 118140960795 + 816563 * 2 ^ 59
def prefixEnd_816563 : Nat := 4983230072969 + 3 ^ 40 * 816563 * 2
def baseEnd_816563 : Nat := 419289303677393927207201

theorem tailTrace_816563 : CollatzResearch.WordTrace tailWord_816563 prefixEnd_816563 419289303677393927207201 := by
  unfold tailWord_816563
  simp only [CollatzResearch.WordTrace]
  refine ⟨29782499340739183702702343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19854999560492789135134895 29782499340739183702702343)
  ·
    refine ⟨44673749011108775554053515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29782499340739183702702343 44673749011108775554053515)
    ·
      refine ⟨67010623516663163331080273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44673749011108775554053515 67010623516663163331080273)
      ·
        refine ⟨50257967637497372498310205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67010623516663163331080273 50257967637497372498310205)
        ·
          refine ⟨18846737864061514686866327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50257967637497372498310205 18846737864061514686866327)
          ·
            refine ⟨28270106796092272030299491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18846737864061514686866327 28270106796092272030299491)
            ·
              refine ⟨42405160194138408045449237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28270106796092272030299491 42405160194138408045449237)
              ·
                refine ⟨1987741884100237877130433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42405160194138408045449237 1987741884100237877130433)
                ·
                  refine ⟨1490806413075178407847825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1987741884100237877130433 1490806413075178407847825)
                  ·
                    refine ⟨1118104809806383805885869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1490806413075178407847825 1118104809806383805885869)
                    ·
                      refine ⟨419289303677393927207201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1118104809806383805885869 419289303677393927207201)
                      ·
                        rfl

theorem cell23_816563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 3].length) (baseStart_816563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816563 prefixEnd_816563 := by exact prefixLift 816563
  have htrace : WordTrace (prefixWord ++ tailWord_816563) baseStart_816563 baseEnd_816563 := by
    simpa [prefixWord, tailWord_816563, baseEnd_816563] using wordTrace_append hprefix tailTrace_816563
  have hstable : (prefixWord ++ tailWord_816563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816563).length < 2 ^ (prefixWord ++ tailWord_816563).sum := by decide
  have hdescent : baseEnd_816563 < baseStart_816563 := by decide
  rcases family_descends (prefixWord ++ tailWord_816563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816580 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_816580 : Nat := 118140960795 + 816580 * 2 ^ 59
def prefixEnd_816580 : Nat := 4983230072969 + 3 ^ 40 * 816580 * 2
def baseEnd_816580 : Nat := 419298032848520360694623

theorem tailTrace_816580 : CollatzResearch.WordTrace tailWord_816580 prefixEnd_816580 419298032848520360694623 := by
  unfold tailWord_816580
  simp only [CollatzResearch.WordTrace]
  refine ⟨14891559690838797803035597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19855412921118397070714129 14891559690838797803035597)
  ·
    refine ⟨5584334884064549176138349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14891559690838797803035597 5584334884064549176138349)
    ·
      refine ⟨2094125581524205941051881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5584334884064549176138349 2094125581524205941051881)
      ·
        refine ⟨1570594186143154455788911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2094125581524205941051881 1570594186143154455788911)
        ·
          refine ⟨2355891279214731683683367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570594186143154455788911 2355891279214731683683367)
          ·
            refine ⟨3533836918822097525525051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355891279214731683683367 3533836918822097525525051)
            ·
              refine ⟨5300755378233146288287577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533836918822097525525051 5300755378233146288287577)
              ·
                refine ⟨3975566533674859716215683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5300755378233146288287577 3975566533674859716215683)
                ·
                  refine ⟨5963349800512289574323525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975566533674859716215683 5963349800512289574323525)
                  ·
                    refine ⟨1118128087596054295185661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5963349800512289574323525 1118128087596054295185661)
                    ·
                      refine ⟨419298032848520360694623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1118128087596054295185661 419298032848520360694623)
                      ·
                        rfl

theorem cell23_816580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_816580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816580 prefixEnd_816580 := by exact prefixLift 816580
  have htrace : WordTrace (prefixWord ++ tailWord_816580) baseStart_816580 baseEnd_816580 := by
    simpa [prefixWord, tailWord_816580, baseEnd_816580] using wordTrace_append hprefix tailTrace_816580
  have hstable : (prefixWord ++ tailWord_816580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816580).length < 2 ^ (prefixWord ++ tailWord_816580).sum := by decide
  have hdescent : baseEnd_816580 < baseStart_816580 := by decide
  rcases family_descends (prefixWord ++ tailWord_816580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816621 : List Nat := [1, 5, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_816621 : Nat := 118140960795 + 816621 * 2 ^ 59
def prefixEnd_816621 : Nat := 4983230072969 + 3 ^ 40 * 816621 * 2
def baseEnd_816621 : Nat := 139773028518451566760645

theorem tailTrace_816621 : CollatzResearch.WordTrace tailWord_816621 prefixEnd_816621 139773028518451566760645 := by
  unfold tailWord_816621
  simp only [CollatzResearch.WordTrace]
  refine ⟨29784614774529059608313717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19856409849686039738875811 29784614774529059608313717)
  ·
    refine ⟨2792307635112099338279411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29784614774529059608313717 2792307635112099338279411)
    ·
      refine ⟨4188461452668149007419117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2792307635112099338279411 4188461452668149007419117)
      ·
        refine ⟨1570673044750555877782169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4188461452668149007419117 1570673044750555877782169)
        ·
          refine ⟨1178004783562916908336627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1570673044750555877782169 1178004783562916908336627)
          ·
            refine ⟨1767007175344375362504941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178004783562916908336627 1767007175344375362504941)
            ·
              refine ⟨662627690754140760939353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1767007175344375362504941 662627690754140760939353)
              ·
                refine ⟨496970768065605570704515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662627690754140760939353 496970768065605570704515)
                ·
                  refine ⟨745456152098408356056773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496970768065605570704515 745456152098408356056773)
                  ·
                    refine ⟨139773028518451566760645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 745456152098408356056773 139773028518451566760645)
                    ·
                      rfl

theorem cell23_816621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_816621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816621 prefixEnd_816621 := by exact prefixLift 816621
  have htrace : WordTrace (prefixWord ++ tailWord_816621) baseStart_816621 baseEnd_816621 := by
    simpa [prefixWord, tailWord_816621, baseEnd_816621] using wordTrace_append hprefix tailTrace_816621
  have hstable : (prefixWord ++ tailWord_816621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816621).length < 2 ^ (prefixWord ++ tailWord_816621).sum := by decide
  have hdescent : baseEnd_816621 < baseStart_816621 := by decide
  rcases family_descends (prefixWord ++ tailWord_816621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816633 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 4]
def baseStart_816633 : Nat := 118140960795 + 816633 * 2 ^ 59
def prefixEnd_816633 : Nat := 4983230072969 + 3 ^ 40 * 816633 * 2
def baseEnd_816633 : Nat := 419325247323208653331879

theorem tailTrace_816633 : CollatzResearch.WordTrace tailWord_816633 prefixEnd_816633 419325247323208653331879 := by
  unfold tailWord_816633
  simp only [CollatzResearch.WordTrace]
  refine ⟨29785052450485585657750553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19856701633657057105167035 29785052450485585657750553)
  ·
    refine ⟨22338789337864189243312915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29785052450485585657750553 22338789337864189243312915)
    ·
      refine ⟨33508184006796283864969373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22338789337864189243312915 33508184006796283864969373)
      ·
        refine ⟨12565569002548606449363515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33508184006796283864969373 12565569002548606449363515)
        ·
          refine ⟨18848353503822909674045273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12565569002548606449363515 18848353503822909674045273)
          ·
            refine ⟨14136265127867182255533955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18848353503822909674045273 14136265127867182255533955)
            ·
              refine ⟨21204397691800773383300933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14136265127867182255533955 21204397691800773383300933)
              ·
                refine ⟨3975824567212645009368925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21204397691800773383300933 3975824567212645009368925)
                ·
                  refine ⟨1490934212704741878513347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3975824567212645009368925 1490934212704741878513347)
                  ·
                    refine ⟨2236401319057112817770021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1490934212704741878513347 2236401319057112817770021)
                    ·
                      refine ⟨419325247323208653331879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2236401319057112817770021 419325247323208653331879)
                      ·
                        rfl

theorem cell23_816633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_816633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816633 prefixEnd_816633 := by exact prefixLift 816633
  have htrace : WordTrace (prefixWord ++ tailWord_816633) baseStart_816633 baseEnd_816633 := by
    simpa [prefixWord, tailWord_816633, baseEnd_816633] using wordTrace_append hprefix tailTrace_816633
  have hstable : (prefixWord ++ tailWord_816633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816633).length < 2 ^ (prefixWord ++ tailWord_816633).sum := by decide
  have hdescent : baseEnd_816633 < baseStart_816633 := by decide
  rcases family_descends (prefixWord ++ tailWord_816633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816643 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 6, 4]
def baseStart_816643 : Nat := 118140960795 + 816643 * 2 ^ 59
def prefixEnd_816643 : Nat := 4983230072969 + 3 ^ 40 * 816643 * 2
def baseEnd_816643 : Nat := 139776794043251204735611

theorem tailTrace_816643 : CollatzResearch.WordTrace tailWord_816643 prefixEnd_816643 139776794043251204735611 := by
  unfold tailWord_816643
  simp only [CollatzResearch.WordTrace]
  refine ⟨29785417180449357365614583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19856944786966238243743055 29785417180449357365614583)
  ·
    refine ⟨44678125770674036048421875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29785417180449357365614583 44678125770674036048421875)
    ·
      refine ⟨67017188656011054072632813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44678125770674036048421875 67017188656011054072632813)
      ·
        refine ⟨25131445746004145277237305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67017188656011054072632813 25131445746004145277237305)
        ·
          refine ⟨18848584309503108957927979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25131445746004145277237305 18848584309503108957927979)
          ·
            refine ⟨28272876464254663436891969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18848584309503108957927979 28272876464254663436891969)
            ·
              refine ⟨21204657348190997577668977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28272876464254663436891969 21204657348190997577668977)
              ·
                refine ⟨15903493011143248183251733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21204657348190997577668977 15903493011143248183251733)
                ·
                  refine ⟨745476234897339758589925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15903493011143248183251733 745476234897339758589925)
                  ·
                    refine ⟨139776794043251204735611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 745476234897339758589925 139776794043251204735611)
                    ·
                      rfl

theorem cell23_816643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 4].length) (baseStart_816643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816643 prefixEnd_816643 := by exact prefixLift 816643
  have htrace : WordTrace (prefixWord ++ tailWord_816643) baseStart_816643 baseEnd_816643 := by
    simpa [prefixWord, tailWord_816643, baseEnd_816643] using wordTrace_append hprefix tailTrace_816643
  have hstable : (prefixWord ++ tailWord_816643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816643).length < 2 ^ (prefixWord ++ tailWord_816643).sum := by decide
  have hdescent : baseEnd_816643 < baseStart_816643 := by decide
  rcases family_descends (prefixWord ++ tailWord_816643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816647 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 1, 5]
def baseStart_816647 : Nat := 118140960795 + 816647 * 2 ^ 59
def prefixEnd_816647 : Nat := 4983230072969 + 3 ^ 40 * 816647 * 2
def baseEnd_816647 : Nat := 139777478684123866185605

theorem tailTrace_816647 : CollatzResearch.WordTrace tailWord_816647 prefixEnd_816647 139777478684123866185605 := by
  unfold tailWord_816647
  simp only [CollatzResearch.WordTrace]
  refine ⟨29785563072434866048760195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19857042048289910699173463 29785563072434866048760195)
  ·
    refine ⟨44678344608652299073140293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29785563072434866048760195 44678344608652299073140293)
    ·
      refine ⟨8377189614122306076213805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44678344608652299073140293 8377189614122306076213805)
      ·
        refine ⟨3141446105295864778580177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8377189614122306076213805 3141446105295864778580177)
        ·
          refine ⟨2356084578971898583935133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3141446105295864778580177 2356084578971898583935133)
          ·
            refine ⟨883531717114461968975675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2356084578971898583935133 883531717114461968975675)
            ·
              refine ⟨1325297575671692953463513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883531717114461968975675 1325297575671692953463513)
              ·
                refine ⟨993973181753769715097635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325297575671692953463513 993973181753769715097635)
                ·
                  refine ⟨1490959772630654572646453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993973181753769715097635 1490959772630654572646453)
                  ·
                    refine ⟨139777478684123866185605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1490959772630654572646453 139777478684123866185605)
                    ·
                      rfl

theorem cell23_816647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_816647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816647 prefixEnd_816647 := by exact prefixLift 816647
  have htrace : WordTrace (prefixWord ++ tailWord_816647) baseStart_816647 baseEnd_816647 := by
    simpa [prefixWord, tailWord_816647, baseEnd_816647] using wordTrace_append hprefix tailTrace_816647
  have hstable : (prefixWord ++ tailWord_816647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816647).length < 2 ^ (prefixWord ++ tailWord_816647).sum := by decide
  have hdescent : baseEnd_816647 < baseStart_816647 := by decide
  rcases family_descends (prefixWord ++ tailWord_816647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816650 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_816650 : Nat := 118140960795 + 816650 * 2 ^ 59
def prefixEnd_816650 : Nat := 4983230072969 + 3 ^ 40 * 816650 * 2
def baseEnd_816650 : Nat := 419333976494335086819301

theorem tailTrace_816650 : CollatzResearch.WordTrace tailWord_816650 prefixEnd_816650 419333976494335086819301 := by
  unfold tailWord_816650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7446418122855999390279851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19857114994282665040746269 7446418122855999390279851)
  ·
    refine ⟨11169627184283999085419777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7446418122855999390279851 11169627184283999085419777)
    ·
      refine ⟨8377220388212999314064833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11169627184283999085419777 8377220388212999314064833)
      ·
        refine ⟨6282915291159749485548625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8377220388212999314064833 6282915291159749485548625)
        ·
          refine ⟨4712186468369812114161469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6282915291159749485548625 4712186468369812114161469)
          ·
            refine ⟨1767069925638679542810551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4712186468369812114161469 1767069925638679542810551)
            ·
              refine ⟨2650604888458019314215827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767069925638679542810551 2650604888458019314215827)
              ·
                refine ⟨3975907332687028971323741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650604888458019314215827 3975907332687028971323741)
                ·
                  refine ⟨1490965249757635864246403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3975907332687028971323741 1490965249757635864246403)
                  ·
                    refine ⟨2236447874636453796369605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1490965249757635864246403 2236447874636453796369605)
                    ·
                      refine ⟨419333976494335086819301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2236447874636453796369605 419333976494335086819301)
                      ·
                        rfl

theorem cell23_816650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_816650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816650 prefixEnd_816650 := by exact prefixLift 816650
  have htrace : WordTrace (prefixWord ++ tailWord_816650) baseStart_816650 baseEnd_816650 := by
    simpa [prefixWord, tailWord_816650, baseEnd_816650] using wordTrace_append hprefix tailTrace_816650
  have hstable : (prefixWord ++ tailWord_816650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816650).length < 2 ^ (prefixWord ++ tailWord_816650).sum := by decide
  have hdescent : baseEnd_816650 < baseStart_816650 := by decide
  rcases family_descends (prefixWord ++ tailWord_816650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816654 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2]
def baseStart_816654 : Nat := 118140960795 + 816654 * 2 ^ 59
def prefixEnd_816654 : Nat := 4983230072969 + 3 ^ 40 * 816654 * 2
def baseEnd_816654 : Nat := 419336030416953071169283

theorem tailTrace_816654 : CollatzResearch.WordTrace tailWord_816654 prefixEnd_816654 419336030416953071169283 := by
  unfold tailWord_816654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723227297926188280533127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19857212255606337496176677 3723227297926188280533127)
  ·
    refine ⟨5584840946889282420799691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3723227297926188280533127 5584840946889282420799691)
    ·
      refine ⟨8377261420333923631199537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5584840946889282420799691 8377261420333923631199537)
      ·
        refine ⟨6282946065250442723399653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8377261420333923631199537 6282946065250442723399653)
        ·
          refine ⟨1178052387234458010637435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6282946065250442723399653 1178052387234458010637435)
          ·
            refine ⟨1767078580851687015956153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178052387234458010637435 1767078580851687015956153)
            ·
              refine ⟨1325308935638765261967115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767078580851687015956153 1325308935638765261967115)
              ·
                refine ⟨1987963403458147892950673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325308935638765261967115 1987963403458147892950673)
                ·
                  refine ⟨1490972552593610919713005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1987963403458147892950673 1490972552593610919713005)
                  ·
                    refine ⟨559114707222604094892377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490972552593610919713005 559114707222604094892377)
                    ·
                      refine ⟨419336030416953071169283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 559114707222604094892377 419336030416953071169283)
                      ·
                        rfl

theorem cell23_816654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_816654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816654 prefixEnd_816654 := by exact prefixLift 816654
  have htrace : WordTrace (prefixWord ++ tailWord_816654) baseStart_816654 baseEnd_816654 := by
    simpa [prefixWord, tailWord_816654, baseEnd_816654] using wordTrace_append hprefix tailTrace_816654
  have hstable : (prefixWord ++ tailWord_816654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816654).length < 2 ^ (prefixWord ++ tailWord_816654).sum := by decide
  have hdescent : baseEnd_816654 < baseStart_816654 := by decide
  rcases family_descends (prefixWord ++ tailWord_816654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816763 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 7]
def baseStart_816763 : Nat := 118140960795 + 816763 * 2 ^ 59
def prefixEnd_816763 : Nat := 4983230072969 + 3 ^ 40 * 816763 * 2
def baseEnd_816763 : Nat := 46599111089810349411809

theorem tailTrace_816763 : CollatzResearch.WordTrace tailWord_816763 prefixEnd_816763 46599111089810349411809 := by
  unfold tailWord_816763
  simp only [CollatzResearch.WordTrace]
  refine ⟨29789793940014617859982943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19859862626676411906655295 29789793940014617859982943)
  ·
    refine ⟨44684690910021926789974415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29789793940014617859982943 44684690910021926789974415)
    ·
      refine ⟨67027036365032890184961623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44684690910021926789974415 67027036365032890184961623)
      ·
        refine ⟨100540554547549335277442435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67027036365032890184961623 100540554547549335277442435)
        ·
          refine ⟨150810831821324002916163653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100540554547549335277442435 150810831821324002916163653)
          ·
            refine ⟨28277030966498250546780685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150810831821324002916163653 28277030966498250546780685)
            ·
              refine ⟨10603886612436843955042757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28277030966498250546780685 10603886612436843955042757)
              ·
                refine ⟨1988228739831908241570517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10603886612436843955042757 1988228739831908241570517)
                ·
                  refine ⟨46599111089810349411809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1988228739831908241570517 46599111089810349411809)
                  ·
                    rfl

theorem cell23_816763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 7].length) (baseStart_816763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816763 prefixEnd_816763 := by exact prefixLift 816763
  have htrace : WordTrace (prefixWord ++ tailWord_816763) baseStart_816763 baseEnd_816763 := by
    simpa [prefixWord, tailWord_816763, baseEnd_816763] using wordTrace_append hprefix tailTrace_816763
  have hstable : (prefixWord ++ tailWord_816763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816763).length < 2 ^ (prefixWord ++ tailWord_816763).sum := by decide
  have hdescent : baseEnd_816763 < baseStart_816763 := by decide
  rcases family_descends (prefixWord ++ tailWord_816763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816793 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 3, 7]
def baseStart_816793 : Nat := 118140960795 + 816793 * 2 ^ 59
def prefixEnd_816793 : Nat := 4983230072969 + 3 ^ 40 * 816793 * 2
def baseEnd_816793 : Nat := 139802468075976009110381

theorem tailTrace_816793 : CollatzResearch.WordTrace tailWord_816793 prefixEnd_816793 139802468075976009110381 := by
  unfold tailWord_816793
  simp only [CollatzResearch.WordTrace]
  refine ⟨29790888129905932983575033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19860592086603955322383355 29790888129905932983575033)
  ·
    refine ⟨22343166097429449737681275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29790888129905932983575033 22343166097429449737681275)
    ·
      refine ⟨33514749146144174606521913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22343166097429449737681275 33514749146144174606521913)
      ·
        refine ⟨25136061859608130954891435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33514749146144174606521913 25136061859608130954891435)
        ·
          refine ⟨37704092789412196432337153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25136061859608130954891435 37704092789412196432337153)
          ·
            refine ⟨28278069592059147324252865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37704092789412196432337153 28278069592059147324252865)
            ·
              refine ⟨21208552194044360493189649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28278069592059147324252865 21208552194044360493189649)
              ·
                refine ⟨15906414145533270369892237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21208552194044360493189649 15906414145533270369892237)
                ·
                  refine ⟨5964905304574976388709589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15906414145533270369892237 5964905304574976388709589)
                  ·
                    refine ⟨139802468075976009110381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5964905304574976388709589 139802468075976009110381)
                    ·
                      rfl

theorem cell23_816793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_816793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816793 prefixEnd_816793 := by exact prefixLift 816793
  have htrace : WordTrace (prefixWord ++ tailWord_816793) baseStart_816793 baseEnd_816793 := by
    simpa [prefixWord, tailWord_816793, baseEnd_816793] using wordTrace_append hprefix tailTrace_816793
  have hstable : (prefixWord ++ tailWord_816793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816793).length < 2 ^ (prefixWord ++ tailWord_816793).sum := by decide
  have hdescent : baseEnd_816793 < baseStart_816793 := by decide
  rcases family_descends (prefixWord ++ tailWord_816793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816880 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 3]
def baseStart_816880 : Nat := 118140960795 + 816880 * 2 ^ 59
def prefixEnd_816880 : Nat := 4983230072969 + 3 ^ 40 * 816880 * 2
def baseEnd_816880 : Nat := 419452077044869186943243

theorem tailTrace_816880 : CollatzResearch.WordTrace tailWord_816880 prefixEnd_816880 419452077044869186943243 := by
  unfold tailWord_816880
  simp only [CollatzResearch.WordTrace]
  refine ⟨14897030640295373420996047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19862707520393831227994729 14897030640295373420996047)
  ·
    refine ⟨22345545960443060131494071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14897030640295373420996047 22345545960443060131494071)
    ·
      refine ⟨33518318940664590197241107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22345545960443060131494071 33518318940664590197241107)
      ·
        refine ⟨50277478410996885295861661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33518318940664590197241107 50277478410996885295861661)
        ·
          refine ⟨18854054404123831985948123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50277478410996885295861661 18854054404123831985948123)
          ·
            refine ⟨28281081606185747978922185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18854054404123831985948123 28281081606185747978922185)
            ·
              refine ⟨21210811204639310984191639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28281081606185747978922185 21210811204639310984191639)
              ·
                refine ⟨31816216806958966476287459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21210811204639310984191639 31816216806958966476287459)
                ·
                  refine ⟨47724325210438449714431189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31816216806958966476287459 47724325210438449714431189)
                  ·
                    refine ⟨1118538872119651165181981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47724325210438449714431189 1118538872119651165181981)
                    ·
                      refine ⟨419452077044869186943243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1118538872119651165181981 419452077044869186943243)
                      ·
                        rfl

theorem cell23_816880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 3].length) (baseStart_816880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816880 prefixEnd_816880 := by exact prefixLift 816880
  have htrace : WordTrace (prefixWord ++ tailWord_816880) baseStart_816880 baseEnd_816880 := by
    simpa [prefixWord, tailWord_816880, baseEnd_816880] using wordTrace_append hprefix tailTrace_816880
  have hstable : (prefixWord ++ tailWord_816880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816880).length < 2 ^ (prefixWord ++ tailWord_816880).sum := by decide
  have hdescent : baseEnd_816880 < baseStart_816880 := by decide
  rcases family_descends (prefixWord ++ tailWord_816880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816954 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4]
def baseStart_816954 : Nat := 118140960795 + 816954 * 2 ^ 59
def prefixEnd_816954 : Nat := 4983230072969 + 3 ^ 40 * 816954 * 2
def baseEnd_816954 : Nat := 419490074613301897417903

theorem tailTrace_816954 : CollatzResearch.WordTrace tailWord_816954 prefixEnd_816954 419490074613301897417903 := by
  unfold tailWord_816954
  simp only [CollatzResearch.WordTrace]
  refine ⟨7449190070580664370046479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19864506854881771653457277 7449190070580664370046479)
  ·
    refine ⟨11173785105870996555069719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7449190070580664370046479 11173785105870996555069719)
    ·
      refine ⟨16760677658806494832604579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11173785105870996555069719 16760677658806494832604579)
      ·
        refine ⟨25141016488209742248906869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16760677658806494832604579 25141016488209742248906869)
        ·
          refine ⟨2356970295769663335835019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25141016488209742248906869 2356970295769663335835019)
          ·
            refine ⟨3535455443654495003752529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356970295769663335835019 3535455443654495003752529)
            ·
              refine ⟨2651591582740871252814397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3535455443654495003752529 2651591582740871252814397)
              ·
                refine ⟨994346843527826719805399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2651591582740871252814397 994346843527826719805399)
                ·
                  refine ⟨1491520265291740079708099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994346843527826719805399 1491520265291740079708099)
                  ·
                    refine ⟨2237280397937610119562149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1491520265291740079708099 2237280397937610119562149)
                    ·
                      refine ⟨419490074613301897417903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2237280397937610119562149 419490074613301897417903)
                      ·
                        rfl

theorem cell23_816954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_816954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_816954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_816954 prefixEnd_816954 := by exact prefixLift 816954
  have htrace : WordTrace (prefixWord ++ tailWord_816954) baseStart_816954 baseEnd_816954 := by
    simpa [prefixWord, tailWord_816954, baseEnd_816954] using wordTrace_append hprefix tailTrace_816954
  have hstable : (prefixWord ++ tailWord_816954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816954).length < 2 ^ (prefixWord ++ tailWord_816954).sum := by decide
  have hdescent : baseEnd_816954 < baseStart_816954 := by decide
  rcases family_descends (prefixWord ++ tailWord_816954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
