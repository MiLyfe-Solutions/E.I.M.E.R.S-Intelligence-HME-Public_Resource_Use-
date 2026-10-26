import V185TrunkScan22Chunk256

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2291592 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 3, 3]
def baseStart_2291592 : Nat := 118140960795 + 2291592 * 2 ^ 59
def prefixEnd_2291592 : Nat := 4983230072969 + 3 ^ 40 * 2291592 * 2
def baseEnd_2291592 : Nat := 784458773332068912974111

theorem tailTrace_2291592 : CollatzResearch.WordTrace tailWord_2291592 prefixEnd_2291592 784458773332068912974111 := by
  unfold tailWord_2291592
  simp only [CollatzResearch.WordTrace]
  refine ⟨41790613356980515799966515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55720817809307354399955353 41790613356980515799966515)
  ·
    refine ⟨62685920035470773699949773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41790613356980515799966515 62685920035470773699949773)
    ·
      refine ⟨23507220013301540137481165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62685920035470773699949773 23507220013301540137481165)
      ·
        refine ⟨8815207504988077551555437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23507220013301540137481165 8815207504988077551555437)
        ·
          refine ⟨3305702814370529081833289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8815207504988077551555437 3305702814370529081833289)
          ·
            refine ⟨2479277110777896811374967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3305702814370529081833289 2479277110777896811374967)
            ·
              refine ⟨3718915666166845217062451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2479277110777896811374967 3718915666166845217062451)
              ·
                refine ⟨5578373499250267825593677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718915666166845217062451 5578373499250267825593677)
                ·
                  refine ⟨2091890062218850434597629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5578373499250267825593677 2091890062218850434597629)
                  ·
                    refine ⟨784458773332068912974111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2091890062218850434597629 784458773332068912974111)
                    ·
                      rfl

theorem cell22_2291592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_2291592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291592 prefixEnd_2291592 := by exact prefixLift 2291592
  have htrace : WordTrace (prefixWord ++ tailWord_2291592) baseStart_2291592 baseEnd_2291592 := by
    simpa [prefixWord, tailWord_2291592, baseEnd_2291592] using wordTrace_append hprefix tailTrace_2291592
  have hstable : (prefixWord ++ tailWord_2291592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291592).length < 2 ^ (prefixWord ++ tailWord_2291592).sum := by decide
  have hdescent : baseEnd_2291592 < baseStart_2291592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291616 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 8]
def baseStart_2291616 : Nat := 118140960795 + 2291616 * 2 ^ 59
def prefixEnd_2291616 : Nat := 4983230072969 + 3 ^ 40 * 2291616 * 2
def baseEnd_2291616 : Nat := 261488996340846950124679

theorem tailTrace_2291616 : CollatzResearch.WordTrace tailWord_2291616 prefixEnd_2291616 261488996340846950124679 := by
  unfold tailWord_2291616
  simp only [CollatzResearch.WordTrace]
  refine ⟨41791051032937041849403351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55721401377249389132537801 41791051032937041849403351)
  ·
    refine ⟨62686576549405562774105027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41791051032937041849403351 62686576549405562774105027)
    ·
      refine ⟨94029864824108344161157541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62686576549405562774105027 94029864824108344161157541)
      ·
        refine ⟨17630599654520314530217039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94029864824108344161157541 17630599654520314530217039)
        ·
          refine ⟨26445899481780471795325559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17630599654520314530217039 26445899481780471795325559)
          ·
            refine ⟨39668849222670707692988339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26445899481780471795325559 39668849222670707692988339)
            ·
              refine ⟨59503273834006061539482509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39668849222670707692988339 59503273834006061539482509)
              ·
                refine ⟨22313727687752273077305941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59503273834006061539482509 22313727687752273077305941)
                ·
                  refine ⟨261488996340846950124679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22313727687752273077305941 261488996340846950124679)
                  ·
                    rfl

theorem cell22_2291616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_2291616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291616 prefixEnd_2291616 := by exact prefixLift 2291616
  have htrace : WordTrace (prefixWord ++ tailWord_2291616) baseStart_2291616 baseEnd_2291616 := by
    simpa [prefixWord, tailWord_2291616, baseEnd_2291616] using wordTrace_append hprefix tailTrace_2291616
  have hstable : (prefixWord ++ tailWord_2291616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291616).length < 2 ^ (prefixWord ++ tailWord_2291616).sum := by decide
  have hdescent : baseEnd_2291616 < baseStart_2291616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291635 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 1, 4]
def baseStart_2291635 : Nat := 118140960795 + 2291635 * 2 ^ 59
def prefixEnd_2291635 : Nat := 4983230072969 + 3 ^ 40 * 2291635 * 2
def baseEnd_2291635 : Nat := 784473493110831134148979

theorem tailTrace_2291635 : CollatzResearch.WordTrace tailWord_2291635 prefixEnd_2291635 784473493110831134148979 := by
  unfold tailWord_2291635
  simp only [CollatzResearch.WordTrace]
  refine ⟨83582795052805249943748359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55721863368536833295832239 83582795052805249943748359)
  ·
    refine ⟨125374192579207874915622539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83582795052805249943748359 125374192579207874915622539)
    ·
      refine ⟨188061288868811812373433809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125374192579207874915622539 188061288868811812373433809)
      ·
        refine ⟨141045966651608859280075357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188061288868811812373433809 141045966651608859280075357)
        ·
          refine ⟨52892237494353322230028259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141045966651608859280075357 52892237494353322230028259)
          ·
            refine ⟨79338356241529983345042389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52892237494353322230028259 79338356241529983345042389)
            ·
              refine ⟨1859492724410858984649431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 79338356241529983345042389 1859492724410858984649431)
              ·
                refine ⟨2789239086616288476974147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859492724410858984649431 2789239086616288476974147)
                ·
                  refine ⟨4183858629924432715461221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2789239086616288476974147 4183858629924432715461221)
                  ·
                    refine ⟨784473493110831134148979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4183858629924432715461221 784473493110831134148979)
                    ·
                      rfl

theorem cell22_2291635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 4].length) (baseStart_2291635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291635 prefixEnd_2291635 := by exact prefixLift 2291635
  have htrace : WordTrace (prefixWord ++ tailWord_2291635) baseStart_2291635 baseEnd_2291635 := by
    simpa [prefixWord, tailWord_2291635, baseEnd_2291635] using wordTrace_append hprefix tailTrace_2291635
  have hstable : (prefixWord ++ tailWord_2291635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291635).length < 2 ^ (prefixWord ++ tailWord_2291635).sum := by decide
  have hdescent : baseEnd_2291635 < baseStart_2291635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291716 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_2291716 : Nat := 118140960795 + 2291716 * 2 ^ 59
def prefixEnd_2291716 : Nat := 4983230072969 + 3 ^ 40 * 2291716 * 2
def baseEnd_2291716 : Nat := 784501221066173922873731

theorem tailTrace_2291716 : CollatzResearch.WordTrace tailWord_2291716 prefixEnd_2291716 784501221066173922873731 := by
  unfold tailWord_2291716
  simp only [CollatzResearch.WordTrace]
  refine ⟨41792874682755900388723501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55723832910341200518298001 41792874682755900388723501)
  ·
    refine ⟨15672328006033462645771313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41792874682755900388723501 15672328006033462645771313)
    ·
      refine ⟨11754246004525096984328485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15672328006033462645771313 11754246004525096984328485)
      ·
        refine ⟨2203921125848455684561591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11754246004525096984328485 2203921125848455684561591)
        ·
          refine ⟨3305881688772683526842387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2203921125848455684561591 3305881688772683526842387)
          ·
            refine ⟨4958822533159025290263581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305881688772683526842387 4958822533159025290263581)
            ·
              refine ⟨1859558449934634483848843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4958822533159025290263581 1859558449934634483848843)
              ·
                refine ⟨2789337674901951725773265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859558449934634483848843 2789337674901951725773265)
                ·
                  refine ⟨2092003256176463794329949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2789337674901951725773265 2092003256176463794329949)
                  ·
                    refine ⟨784501221066173922873731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2092003256176463794329949 784501221066173922873731)
                    ·
                      rfl

theorem cell22_2291716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_2291716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291716 prefixEnd_2291716 := by exact prefixLift 2291716
  have htrace : WordTrace (prefixWord ++ tailWord_2291716) baseStart_2291716 baseEnd_2291716 := by
    simpa [prefixWord, tailWord_2291716, baseEnd_2291716] using wordTrace_append hprefix tailTrace_2291716
  have hstable : (prefixWord ++ tailWord_2291716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291716).length < 2 ^ (prefixWord ++ tailWord_2291716).sum := by decide
  have hdescent : baseEnd_2291716 < baseStart_2291716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291800 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_2291800 : Nat := 118140960795 + 2291800 * 2 ^ 59
def prefixEnd_2291800 : Nat := 4983230072969 + 3 ^ 40 * 2291800 * 2
def baseEnd_2291800 : Nat := 784529975982825703773473

theorem tailTrace_2291800 : CollatzResearch.WordTrace tailWord_2291800 prefixEnd_2291800 784529975982825703773473 := by
  unfold tailWord_2291800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41794406548603741561752427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55725875398138322082336569 41794406548603741561752427)
  ·
    refine ⟨62691609822905612342628641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41794406548603741561752427 62691609822905612342628641)
    ·
      refine ⟨47018707367179209256971481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62691609822905612342628641 47018707367179209256971481)
      ·
        refine ⟨35264030525384406942728611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47018707367179209256971481 35264030525384406942728611)
        ·
          refine ⟨52896045788076610414092917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35264030525384406942728611 52896045788076610414092917)
          ·
            refine ⟨4959004292632182226321211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52896045788076610414092917 4959004292632182226321211)
            ·
              refine ⟨7438506438948273339481817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959004292632182226321211 7438506438948273339481817)
              ·
                refine ⟨5578879829211205004611363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7438506438948273339481817 5578879829211205004611363)
                ·
                  refine ⟨8368319743816807506917045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5578879829211205004611363 8368319743816807506917045)
                  ·
                    refine ⟨784529975982825703773473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8368319743816807506917045 784529975982825703773473)
                    ·
                      rfl

theorem cell22_2291800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_2291800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291800 prefixEnd_2291800 := by exact prefixLift 2291800
  have htrace : WordTrace (prefixWord ++ tailWord_2291800) baseStart_2291800 baseEnd_2291800 := by
    simpa [prefixWord, tailWord_2291800, baseEnd_2291800] using wordTrace_append hprefix tailTrace_2291800
  have hstable : (prefixWord ++ tailWord_2291800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291800).length < 2 ^ (prefixWord ++ tailWord_2291800).sum := by decide
  have hdescent : baseEnd_2291800 < baseStart_2291800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291804 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 1, 4]
def baseStart_2291804 : Nat := 118140960795 + 2291804 * 2 ^ 59
def prefixEnd_2291804 : Nat := 4983230072969 + 3 ^ 40 * 2291804 * 2
def baseEnd_2291804 : Nat := 784531345264571026673461

theorem tailTrace_2291804 : CollatzResearch.WordTrace tailWord_2291804 prefixEnd_2291804 784531345264571026673461 := by
  unfold tailWord_2291804
  simp only [CollatzResearch.WordTrace]
  refine ⟨41794479494596495903325233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55725972659461994537766977 41794479494596495903325233)
  ·
    refine ⟨31345859620947371927493925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41794479494596495903325233 31345859620947371927493925)
    ·
      refine ⟨5877348678927632236405111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31345859620947371927493925 5877348678927632236405111)
      ·
        refine ⟨8816023018391448354607667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5877348678927632236405111 8816023018391448354607667)
        ·
          refine ⟨13224034527587172531911501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8816023018391448354607667 13224034527587172531911501)
          ·
            refine ⟨4959012947845189699466813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13224034527587172531911501 4959012947845189699466813)
            ·
              refine ⟨1859629855441946137300055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4959012947845189699466813 1859629855441946137300055)
              ·
                refine ⟨2789444783162919205950083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859629855441946137300055 2789444783162919205950083)
                ·
                  refine ⟨4184167174744378808925125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2789444783162919205950083 4184167174744378808925125)
                  ·
                    refine ⟨784531345264571026673461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4184167174744378808925125 784531345264571026673461)
                    ·
                      rfl

theorem cell22_2291804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_2291804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291804 prefixEnd_2291804 := by exact prefixLift 2291804
  have htrace : WordTrace (prefixWord ++ tailWord_2291804) baseStart_2291804 baseEnd_2291804 := by
    simpa [prefixWord, tailWord_2291804, baseEnd_2291804] using wordTrace_append hprefix tailTrace_2291804
  have hstable : (prefixWord ++ tailWord_2291804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291804).length < 2 ^ (prefixWord ++ tailWord_2291804).sum := by decide
  have hdescent : baseEnd_2291804 < baseStart_2291804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291813 : List Nat := [1, 3, 1, 3, 2, 12]
def baseStart_2291813 : Nat := 118140960795 + 2291813 * 2 ^ 59
def prefixEnd_2291813 : Nat := 4983230072969 + 3 ^ 40 * 2291813 * 2
def baseEnd_2291813 : Nat := 9685610199364172878993

theorem tailTrace_2291813 : CollatzResearch.WordTrace tailWord_2291813 prefixEnd_2291813 9685610199364172878993 := by
  unfold tailWord_2291813
  simp only [CollatzResearch.WordTrace]
  refine ⟨83589287246160386343728093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55726191497440257562485395 83589287246160386343728093)
  ·
    refine ⟨31345982717310144878898035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83589287246160386343728093 31345982717310144878898035)
    ·
      refine ⟨47018974075965217318347053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31345982717310144878898035 47018974075965217318347053)
      ·
        refine ⟨17632115278486956494380145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47018974075965217318347053 17632115278486956494380145)
        ·
          refine ⟨13224086458865217370785109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17632115278486956494380145 13224086458865217370785109)
          ·
            refine ⟨9685610199364172878993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13224086458865217370785109 9685610199364172878993)
            ·
              rfl

theorem cell22_2291813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 12].length) (baseStart_2291813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291813 prefixEnd_2291813 := by exact prefixLift 2291813
  have htrace : WordTrace (prefixWord ++ tailWord_2291813) baseStart_2291813 baseEnd_2291813 := by
    simpa [prefixWord, tailWord_2291813, baseEnd_2291813] using wordTrace_append hprefix tailTrace_2291813
  have hstable : (prefixWord ++ tailWord_2291813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291813).length < 2 ^ (prefixWord ++ tailWord_2291813).sum := by decide
  have hdescent : baseEnd_2291813 < baseStart_2291813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291815 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2291815 : Nat := 118140960795 + 2291815 * 2 ^ 59
def prefixEnd_2291815 : Nat := 4983230072969 + 3 ^ 40 * 2291815 * 2
def baseEnd_2291815 : Nat := 784535110789370664648427

theorem tailTrace_2291815 : CollatzResearch.WordTrace tailWord_2291815 prefixEnd_2291815 784535110789370664648427 := by
  unfold tailWord_2291815
  simp only [CollatzResearch.WordTrace]
  refine ⟨83589360192153140685300899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55726240128102093790200599 83589360192153140685300899)
  ·
    refine ⟨125384040288229711027951349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83589360192153140685300899 125384040288229711027951349)
    ·
      refine ⟨11754753777021535408870439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125384040288229711027951349 11754753777021535408870439)
      ·
        refine ⟨17632130665532303113305659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11754753777021535408870439 17632130665532303113305659)
        ·
          refine ⟨26448195998298454669958489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17632130665532303113305659 26448195998298454669958489)
          ·
            refine ⟨19836146998723841002468867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26448195998298454669958489 19836146998723841002468867)
            ·
              refine ⟨29754220498085761503703301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19836146998723841002468867 29754220498085761503703301)
              ·
                refine ⟨5578916343391080281944369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29754220498085761503703301 5578916343391080281944369)
                ·
                  refine ⟨4184187257543310211458277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5578916343391080281944369 4184187257543310211458277)
                  ·
                    refine ⟨784535110789370664648427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4184187257543310211458277 784535110789370664648427)
                    ·
                      rfl

theorem cell22_2291815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2291815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291815 prefixEnd_2291815 := by exact prefixLift 2291815
  have htrace : WordTrace (prefixWord ++ tailWord_2291815) baseStart_2291815 baseEnd_2291815 := by
    simpa [prefixWord, tailWord_2291815, baseEnd_2291815] using wordTrace_append hprefix tailTrace_2291815
  have hstable : (prefixWord ++ tailWord_2291815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291815).length < 2 ^ (prefixWord ++ tailWord_2291815).sum := by decide
  have hdescent : baseEnd_2291815 < baseStart_2291815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291817 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 2, 3]
def baseStart_2291817 : Nat := 118140960795 + 2291817 * 2 ^ 59
def prefixEnd_2291817 : Nat := 4983230072969 + 3 ^ 40 * 2291817 * 2
def baseEnd_2291817 : Nat := 784535795430243326098421

theorem tailTrace_2291817 : CollatzResearch.WordTrace tailWord_2291817 prefixEnd_2291817 784535795430243326098421 := by
  unfold tailWord_2291817
  simp only [CollatzResearch.WordTrace]
  refine ⟨83589433138145895026873705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55726288758763930017915803 83589433138145895026873705)
  ·
    refine ⟨62692074853609421270155279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83589433138145895026873705 62692074853609421270155279)
    ·
      refine ⟨94038112280414131905232919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62692074853609421270155279 94038112280414131905232919)
      ·
        refine ⟨141057168420621197857849379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94038112280414131905232919 141057168420621197857849379)
        ·
          refine ⟨211585752630931796786774069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141057168420621197857849379 211585752630931796786774069)
          ·
            refine ⟨19836164309149855948760069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211585752630931796786774069 19836164309149855948760069)
            ·
              refine ⟨3719280807965597990392513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19836164309149855948760069 3719280807965597990392513)
              ·
                refine ⟨2789460605974198492794385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3719280807965597990392513 2789460605974198492794385)
                ·
                  refine ⟨2092095454480648869595789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2789460605974198492794385 2092095454480648869595789)
                  ·
                    refine ⟨784535795430243326098421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2092095454480648869595789 784535795430243326098421)
                    ·
                      rfl

theorem cell22_2291817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 3].length) (baseStart_2291817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291817 prefixEnd_2291817 := by exact prefixLift 2291817
  have htrace : WordTrace (prefixWord ++ tailWord_2291817) baseStart_2291817 baseEnd_2291817 := by
    simpa [prefixWord, tailWord_2291817, baseEnd_2291817] using wordTrace_append hprefix tailTrace_2291817
  have hstable : (prefixWord ++ tailWord_2291817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291817).length < 2 ^ (prefixWord ++ tailWord_2291817).sum := by decide
  have hdescent : baseEnd_2291817 < baseStart_2291817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291890 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_2291890 : Nat := 118140960795 + 2291890 * 2 ^ 59
def prefixEnd_2291890 : Nat := 4983230072969 + 3 ^ 40 * 2291890 * 2
def baseEnd_2291890 : Nat := 784560784822095469023197

theorem tailTrace_2291890 : CollatzResearch.WordTrace tailWord_2291890 prefixEnd_2291890 784560784822095469023197 := by
  unfold tailWord_2291890
  simp only [CollatzResearch.WordTrace]
  refine ⟨20898023916720357123570281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55728063777920952329520749 20898023916720357123570281)
  ·
    refine ⟨15673517937540267842677711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20898023916720357123570281 15673517937540267842677711)
    ·
      refine ⟨23510276906310401764016567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15673517937540267842677711 23510276906310401764016567)
      ·
        refine ⟨35265415359465602646024851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23510276906310401764016567 35265415359465602646024851)
        ·
          refine ⟨52898123039198403969037277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35265415359465602646024851 52898123039198403969037277)
          ·
            refine ⟨19836796139699401488388979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52898123039198403969037277 19836796139699401488388979)
            ·
              refine ⟨29755194209549102232583469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19836796139699401488388979 29755194209549102232583469)
              ·
                refine ⟨11158197828580913337218801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29755194209549102232583469 11158197828580913337218801)
                ·
                  refine ⟨8368648371435685002914101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11158197828580913337218801 8368648371435685002914101)
                  ·
                    refine ⟨784560784822095469023197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8368648371435685002914101 784560784822095469023197)
                    ·
                      rfl

theorem cell22_2291890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_2291890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291890 prefixEnd_2291890 := by exact prefixLift 2291890
  have htrace : WordTrace (prefixWord ++ tailWord_2291890) baseStart_2291890 baseEnd_2291890 := by
    simpa [prefixWord, tailWord_2291890, baseEnd_2291890] using wordTrace_append hprefix tailTrace_2291890
  have hstable : (prefixWord ++ tailWord_2291890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291890).length < 2 ^ (prefixWord ++ tailWord_2291890).sum := by decide
  have hdescent : baseEnd_2291890 < baseStart_2291890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291967 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 2, 4]
def baseStart_2291967 : Nat := 118140960795 + 2291967 * 2 ^ 59
def prefixEnd_2291967 : Nat := 4983230072969 + 3 ^ 40 * 2291967 * 2
def baseEnd_2291967 : Nat := 784587143495692934847961

theorem tailTrace_2291967 : CollatzResearch.WordTrace tailWord_2291967 prefixEnd_2291967 784587143495692934847961 := by
  unfold tailWord_2291967
  simp only [CollatzResearch.WordTrace]
  refine ⟨83594904087602470644834155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55729936058401647096556103 83594904087602470644834155)
  ·
    refine ⟨125392356131403705967251233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83594904087602470644834155 125392356131403705967251233)
    ·
      refine ⟨94044267098552779475438425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125392356131403705967251233 94044267098552779475438425)
      ·
        refine ⟨70533200323914584606578819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94044267098552779475438425 70533200323914584606578819)
        ·
          refine ⟨105799800485871876909868229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70533200323914584606578819 105799800485871876909868229)
          ·
            refine ⟨19837462591100976920600293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105799800485871876909868229 19837462591100976920600293)
            ·
              refine ⟨3719524235831433172612555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19837462591100976920600293 3719524235831433172612555)
              ·
                refine ⟨5579286353747149758918833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3719524235831433172612555 5579286353747149758918833)
                ·
                  refine ⟨4184464765310362319189125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5579286353747149758918833 4184464765310362319189125)
                  ·
                    refine ⟨784587143495692934847961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4184464765310362319189125 784587143495692934847961)
                    ·
                      rfl

theorem cell22_2291967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_2291967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291967 prefixEnd_2291967 := by exact prefixLift 2291967
  have htrace : WordTrace (prefixWord ++ tailWord_2291967) baseStart_2291967 baseEnd_2291967 := by
    simpa [prefixWord, tailWord_2291967, baseEnd_2291967] using wordTrace_append hprefix tailTrace_2291967
  have hstable : (prefixWord ++ tailWord_2291967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291967).length < 2 ^ (prefixWord ++ tailWord_2291967).sum := by decide
  have hdescent : baseEnd_2291967 < baseStart_2291967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291995 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 2, 6]
def baseStart_2291995 : Nat := 118140960795 + 2291995 * 2 ^ 59
def prefixEnd_2291995 : Nat := 4983230072969 + 3 ^ 40 * 2291995 * 2
def baseEnd_2291995 : Nat := 784596728467910195147875

theorem tailTrace_2291995 : CollatzResearch.WordTrace tailWord_2291995 prefixEnd_2291995 784596728467910195147875 := by
  unfold tailWord_2291995
  simp only [CollatzResearch.WordTrace]
  refine ⟨83595925331501031426853439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55730616887667354284568959 83595925331501031426853439)
  ·
    refine ⟨125393887997251547140280159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83595925331501031426853439 125393887997251547140280159)
    ·
      refine ⟨188090831995877320710420239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125393887997251547140280159 188090831995877320710420239)
      ·
        refine ⟨282136247993815981065630359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188090831995877320710420239 282136247993815981065630359)
        ·
          refine ⟨423204371990723971598445539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282136247993815981065630359 423204371990723971598445539)
          ·
            refine ⟨634806557986085957397668309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423204371990723971598445539 634806557986085957397668309)
            ·
              refine ⟨14878278702798889626507851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 634806557986085957397668309 14878278702798889626507851)
              ·
                refine ⟨22317418054198334439761777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14878278702798889626507851 22317418054198334439761777)
                ·
                  refine ⟨16738063540648750829821333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22317418054198334439761777 16738063540648750829821333)
                  ·
                    refine ⟨784596728467910195147875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16738063540648750829821333 784596728467910195147875)
                    ·
                      rfl

theorem cell22_2291995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_2291995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291995 prefixEnd_2291995 := by exact prefixLift 2291995
  have htrace : WordTrace (prefixWord ++ tailWord_2291995) baseStart_2291995 baseEnd_2291995 := by
    simpa [prefixWord, tailWord_2291995, baseEnd_2291995] using wordTrace_append hprefix tailTrace_2291995
  have hstable : (prefixWord ++ tailWord_2291995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291995).length < 2 ^ (prefixWord ++ tailWord_2291995).sum := by decide
  have hdescent : baseEnd_2291995 < baseStart_2291995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292031 : List Nat := [1, 1, 2, 2, 4, 1, 4, 3, 1, 3]
def baseStart_2292031 : Nat := 118140960795 + 2292031 * 2 ^ 59
def prefixEnd_2292031 : Nat := 4983230072969 + 3 ^ 40 * 2292031 * 2
def baseEnd_2292031 : Nat := 784609052003618101247765

theorem tailTrace_2292031 : CollatzResearch.WordTrace tailWord_2292031 prefixEnd_2292031 784609052003618101247765 := by
  unfold tailWord_2292031
  simp only [CollatzResearch.WordTrace]
  refine ⟨83597238359370609575163947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55731492239580406383442631 83597238359370609575163947)
  ·
    refine ⟨125395857539055914362745921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83597238359370609575163947 125395857539055914362745921)
    ·
      refine ⟨94046893154291935772059441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125395857539055914362745921 94046893154291935772059441)
      ·
        refine ⟨70535169865718951829044581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94046893154291935772059441 70535169865718951829044581)
        ·
          refine ⟨13225344349822303467945859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70535169865718951829044581 13225344349822303467945859)
          ·
            refine ⟨19838016524733455201918789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13225344349822303467945859 19838016524733455201918789)
            ·
              refine ⟨3719628098387522850359773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19838016524733455201918789 3719628098387522850359773)
              ·
                refine ⟨1394860536895321068884915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3719628098387522850359773 1394860536895321068884915)
                ·
                  refine ⟨2092290805342981603327373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394860536895321068884915 2092290805342981603327373)
                  ·
                    refine ⟨784609052003618101247765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2092290805342981603327373 784609052003618101247765)
                    ·
                      rfl

theorem cell22_2292031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 1, 3].length) (baseStart_2292031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292031 prefixEnd_2292031 := by exact prefixLift 2292031
  have htrace : WordTrace (prefixWord ++ tailWord_2292031) baseStart_2292031 baseEnd_2292031 := by
    simpa [prefixWord, tailWord_2292031, baseEnd_2292031] using wordTrace_append hprefix tailTrace_2292031
  have hstable : (prefixWord ++ tailWord_2292031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292031).length < 2 ^ (prefixWord ++ tailWord_2292031).sum := by decide
  have hdescent : baseEnd_2292031 < baseStart_2292031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292104 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 4, 3]
def baseStart_2292104 : Nat := 118140960795 + 2292104 * 2 ^ 59
def prefixEnd_2292104 : Nat := 4983230072969 + 3 ^ 40 * 2292104 * 2
def baseEnd_2292104 : Nat := 784634041395470244172541

theorem tailTrace_2292104 : CollatzResearch.WordTrace tailWord_2292104 prefixEnd_2292104 784634041395470244172541 := by
  unfold tailWord_2292104
  simp only [CollatzResearch.WordTrace]
  refine ⟨41799950444053071521285683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55733267258737428695047577 41799950444053071521285683)
  ·
    refine ⟨62699925666079607281928525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41799950444053071521285683 62699925666079607281928525)
    ·
      refine ⟨23512472124779852730723197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62699925666079607281928525 23512472124779852730723197)
      ·
        refine ⟨8817177046792444774021199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23512472124779852730723197 8817177046792444774021199)
        ·
          refine ⟨13225765570188667161031799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8817177046792444774021199 13225765570188667161031799)
          ·
            refine ⟨19838648355283000741547699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13225765570188667161031799 19838648355283000741547699)
            ·
              refine ⟨29757972532924501112321549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19838648355283000741547699 29757972532924501112321549)
              ·
                refine ⟨11159239699846687917120581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29757972532924501112321549 11159239699846687917120581)
                ·
                  refine ⟨2092357443721253984460109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11159239699846687917120581 2092357443721253984460109)
                  ·
                    refine ⟨784634041395470244172541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2092357443721253984460109 784634041395470244172541)
                    ·
                      rfl

theorem cell22_2292104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_2292104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292104 prefixEnd_2292104 := by exact prefixLift 2292104
  have htrace : WordTrace (prefixWord ++ tailWord_2292104) baseStart_2292104 baseEnd_2292104 := by
    simpa [prefixWord, tailWord_2292104, baseEnd_2292104] using wordTrace_append hprefix tailTrace_2292104
  have hstable : (prefixWord ++ tailWord_2292104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292104).length < 2 ^ (prefixWord ++ tailWord_2292104).sum := by decide
  have hdescent : baseEnd_2292104 < baseStart_2292104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292132 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_2292132 : Nat := 118140960795 + 2292132 * 2 ^ 59
def prefixEnd_2292132 : Nat := 4983230072969 + 3 ^ 40 * 2292132 * 2
def baseEnd_2292132 : Nat := 784643626367687504472455

theorem tailTrace_2292132 : CollatzResearch.WordTrace tailWord_2292132 prefixEnd_2292132 784643626367687504472455 := by
  unfold tailWord_2292132
  simp only [CollatzResearch.WordTrace]
  refine ⟨41800461066002351912295325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55733948088003135883060433 41800461066002351912295325)
  ·
    refine ⟨15675172899750881967110747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41800461066002351912295325 15675172899750881967110747)
    ·
      refine ⟨23512759349626322950666121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15675172899750881967110747 23512759349626322950666121)
      ·
        refine ⟨17634569512219742212999591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23512759349626322950666121 17634569512219742212999591)
        ·
          refine ⟨26451854268329613319499387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17634569512219742212999591 26451854268329613319499387)
          ·
            refine ⟨39677781402494419979249081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26451854268329613319499387 39677781402494419979249081)
            ·
              refine ⟨29758336051870814984436811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39677781402494419979249081 29758336051870814984436811)
              ·
                refine ⟨44637504077806222476655217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29758336051870814984436811 44637504077806222476655217)
                ·
                  refine ⟨33478128058354666857491413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44637504077806222476655217 33478128058354666857491413)
                  ·
                    refine ⟨784643626367687504472455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33478128058354666857491413 784643626367687504472455)
                    ·
                      rfl

theorem cell22_2292132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_2292132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292132 prefixEnd_2292132 := by exact prefixLift 2292132
  have htrace : WordTrace (prefixWord ++ tailWord_2292132) baseStart_2292132 baseEnd_2292132 := by
    simpa [prefixWord, tailWord_2292132, baseEnd_2292132] using wordTrace_append hprefix tailTrace_2292132
  have hstable : (prefixWord ++ tailWord_2292132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292132).length < 2 ^ (prefixWord ++ tailWord_2292132).sum := by decide
  have hdescent : baseEnd_2292132 < baseStart_2292132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292136 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2292136 : Nat := 118140960795 + 2292136 * 2 ^ 59
def prefixEnd_2292136 : Nat := 4983230072969 + 3 ^ 40 * 2292136 * 2
def baseEnd_2292136 : Nat := 784644995649432827372443

theorem tailTrace_2292136 : CollatzResearch.WordTrace tailWord_2292136 prefixEnd_2292136 784644995649432827372443 := by
  unfold tailWord_2292136
  simp only [CollatzResearch.WordTrace]
  refine ⟨41800534011995106253868131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55734045349326808338490841 41800534011995106253868131)
  ·
    refine ⟨62700801017992659380802197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41800534011995106253868131 62700801017992659380802197)
    ·
      refine ⟨2939100047718405908475103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62700801017992659380802197 2939100047718405908475103)
      ·
        refine ⟨4408650071577608862712655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2939100047718405908475103 4408650071577608862712655)
        ·
          refine ⟨6612975107366413294068983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4408650071577608862712655 6612975107366413294068983)
          ·
            refine ⟨9919462661049619941103475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6612975107366413294068983 9919462661049619941103475)
            ·
              refine ⟨14879193991574429911655213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9919462661049619941103475 14879193991574429911655213)
              ·
                refine ⟨5579697746840411216870705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14879193991574429911655213 5579697746840411216870705)
                ·
                  refine ⟨4184773310130308412653029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5579697746840411216870705 4184773310130308412653029)
                  ·
                    refine ⟨784644995649432827372443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4184773310130308412653029 784644995649432827372443)
                    ·
                      rfl

theorem cell22_2292136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2292136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292136 prefixEnd_2292136 := by exact prefixLift 2292136
  have htrace : WordTrace (prefixWord ++ tailWord_2292136) baseStart_2292136 baseEnd_2292136 := by
    simpa [prefixWord, tailWord_2292136, baseEnd_2292136] using wordTrace_append hprefix tailTrace_2292136
  have hstable : (prefixWord ++ tailWord_2292136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292136).length < 2 ^ (prefixWord ++ tailWord_2292136).sum := by decide
  have hdescent : baseEnd_2292136 < baseStart_2292136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292207 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 10]
def baseStart_2292207 : Nat := 118140960795 + 2292207 * 2 ^ 59
def prefixEnd_2292207 : Nat := 4983230072969 + 3 ^ 40 * 2292207 * 2
def baseEnd_2292207 : Nat := 261556433466804102949075

theorem tailTrace_2292207 : CollatzResearch.WordTrace tailWord_2292207 prefixEnd_2292207 261556433466804102949075 := by
  unfold tailWord_2292207
  simp only [CollatzResearch.WordTrace]
  refine ⟨83603657606732991633570875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55735771737821994422380583 83603657606732991633570875)
  ·
    refine ⟨125405486410099487450356313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83603657606732991633570875 125405486410099487450356313)
    ·
      refine ⟨94054114807574615587767235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125405486410099487450356313 94054114807574615587767235)
      ·
        refine ⟨141081172211361923381650853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94054114807574615587767235 141081172211361923381650853)
        ·
          refine ⟨26452719789630360634059535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141081172211361923381650853 26452719789630360634059535)
          ·
            refine ⟨39679079684445540951089303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26452719789630360634059535 39679079684445540951089303)
            ·
              refine ⟨59518619526668311426633955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39679079684445540951089303 59518619526668311426633955)
              ·
                refine ⟨89277929290002467139950933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59518619526668311426633955 89277929290002467139950933)
                ·
                  refine ⟨261556433466804102949075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89277929290002467139950933 261556433466804102949075)
                  ·
                    rfl

theorem cell22_2292207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 10].length) (baseStart_2292207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292207 prefixEnd_2292207 := by exact prefixLift 2292207
  have htrace : WordTrace (prefixWord ++ tailWord_2292207) baseStart_2292207 baseEnd_2292207 := by
    simpa [prefixWord, tailWord_2292207, baseEnd_2292207] using wordTrace_append hprefix tailTrace_2292207
  have hstable : (prefixWord ++ tailWord_2292207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292207).length < 2 ^ (prefixWord ++ tailWord_2292207).sum := by decide
  have hdescent : baseEnd_2292207 < baseStart_2292207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292239 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 6, 3]
def baseStart_2292239 : Nat := 118140960795 + 2292239 * 2 ^ 59
def prefixEnd_2292239 : Nat := 4983230072969 + 3 ^ 40 * 2292239 * 2
def baseEnd_2292239 : Nat := 784680254654374892047127

theorem tailTrace_2292239 : CollatzResearch.WordTrace tailWord_2292239 prefixEnd_2292239 784680254654374892047127 := by
  unfold tailWord_2292239
  simp only [CollatzResearch.WordTrace]
  refine ⟨83604824742617061098735771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55736549828411374065823847 83604824742617061098735771)
  ·
    refine ⟨125407237113925591648103657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83604824742617061098735771 125407237113925591648103657)
    ·
      refine ⟨94055427835444193736077743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125407237113925591648103657 94055427835444193736077743)
      ·
        refine ⟨141083141753166290604116615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94055427835444193736077743 141083141753166290604116615)
        ·
          refine ⟨211624712629749435906174923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141083141753166290604116615 211624712629749435906174923)
          ·
            refine ⟨317437068944624153859262385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211624712629749435906174923 317437068944624153859262385)
            ·
              refine ⟨238077801708468115394446789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317437068944624153859262385 238077801708468115394446789)
              ·
                refine ⟨44639587820337771636458773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238077801708468115394446789 44639587820337771636458773)
                ·
                  refine ⟨2092480679078333045459005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44639587820337771636458773 2092480679078333045459005)
                  ·
                    refine ⟨784680254654374892047127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2092480679078333045459005 784680254654374892047127)
                    ·
                      rfl

theorem cell22_2292239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 3].length) (baseStart_2292239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292239 prefixEnd_2292239 := by exact prefixLift 2292239
  have htrace : WordTrace (prefixWord ++ tailWord_2292239) baseStart_2292239 baseEnd_2292239 := by
    simpa [prefixWord, tailWord_2292239, baseEnd_2292239] using wordTrace_append hprefix tailTrace_2292239
  have hstable : (prefixWord ++ tailWord_2292239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292239).length < 2 ^ (prefixWord ++ tailWord_2292239).sum := by decide
  have hdescent : baseEnd_2292239 < baseStart_2292239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292329 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_2292329 : Nat := 118140960795 + 2292329 * 2 ^ 59
def prefixEnd_2292329 : Nat := 4983230072969 + 3 ^ 40 * 2292329 * 2
def baseEnd_2292329 : Nat := 784711063493644657296851

theorem tailTrace_2292329 : CollatzResearch.WordTrace tailWord_2292329 prefixEnd_2292329 784711063493644657296851 := by
  unfold tailWord_2292329
  simp only [CollatzResearch.WordTrace]
  refine ⟨83608107312291006469512041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55738738208194004313008027 83608107312291006469512041)
  ·
    refine ⟨62706080484218254852134031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83608107312291006469512041 62706080484218254852134031)
    ·
      refine ⟨94059120726327382278201047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62706080484218254852134031 94059120726327382278201047)
      ·
        refine ⟨141088681089491073417301571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94059120726327382278201047 141088681089491073417301571)
        ·
          refine ⟨211633021634236610125952357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141088681089491073417301571 211633021634236610125952357)
          ·
            refine ⟨39681191556419364398616067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211633021634236610125952357 39681191556419364398616067)
            ·
              refine ⟨59521787334629046597924101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39681191556419364398616067 59521787334629046597924101)
              ·
                refine ⟨11160335125242946237110769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59521787334629046597924101 11160335125242946237110769)
                ·
                  refine ⟨8370251343932209677833077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11160335125242946237110769 8370251343932209677833077)
                  ·
                    refine ⟨784711063493644657296851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8370251343932209677833077 784711063493644657296851)
                    ·
                      rfl

theorem cell22_2292329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_2292329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292329 prefixEnd_2292329 := by exact prefixLift 2292329
  have htrace : WordTrace (prefixWord ++ tailWord_2292329) baseStart_2292329 baseEnd_2292329 := by
    simpa [prefixWord, tailWord_2292329, baseEnd_2292329] using wordTrace_append hprefix tailTrace_2292329
  have hstable : (prefixWord ++ tailWord_2292329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292329).length < 2 ^ (prefixWord ++ tailWord_2292329).sum := by decide
  have hdescent : baseEnd_2292329 < baseStart_2292329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292335 : List Nat := [1, 1, 2, 1, 3, 2, 6, 2, 1, 3]
def baseStart_2292335 : Nat := 118140960795 + 2292335 * 2 ^ 59
def prefixEnd_2292335 : Nat := 4983230072969 + 3 ^ 40 * 2292335 * 2
def baseEnd_2292335 : Nat := 784713117416262641646833

theorem tailTrace_2292335 : CollatzResearch.WordTrace tailWord_2292335 prefixEnd_2292335 784713117416262641646833 := by
  unfold tailWord_2292335
  simp only [CollatzResearch.WordTrace]
  refine ⟨83608326150269269494230459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55738884100179512996153639 83608326150269269494230459)
  ·
    refine ⟨125412489225403904241345689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83608326150269269494230459 125412489225403904241345689)
    ·
      refine ⟨94059366919052928181009267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125412489225403904241345689 94059366919052928181009267)
      ·
        refine ⟨141089050378579392271513901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94059366919052928181009267 141089050378579392271513901)
        ·
          refine ⟨52908393891967272101817713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141089050378579392271513901 52908393891967272101817713)
          ·
            refine ⟨39681295418975454076363285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52908393891967272101817713 39681295418975454076363285)
            ·
              refine ⟨1860060722764474409829529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39681295418975454076363285 1860060722764474409829529)
              ·
                refine ⟨1395045542073355807372147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860060722764474409829529 1395045542073355807372147)
                ·
                  refine ⟨2092568313110033711058221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395045542073355807372147 2092568313110033711058221)
                  ·
                    refine ⟨784713117416262641646833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2092568313110033711058221 784713117416262641646833)
                    ·
                      rfl

theorem cell22_2292335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 1, 3].length) (baseStart_2292335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292335 prefixEnd_2292335 := by exact prefixLift 2292335
  have htrace : WordTrace (prefixWord ++ tailWord_2292335) baseStart_2292335 baseEnd_2292335 := by
    simpa [prefixWord, tailWord_2292335, baseEnd_2292335] using wordTrace_append hprefix tailTrace_2292335
  have hstable : (prefixWord ++ tailWord_2292335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292335).length < 2 ^ (prefixWord ++ tailWord_2292335).sum := by decide
  have hdescent : baseEnd_2292335 < baseStart_2292335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292361 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 1, 4]
def baseStart_2292361 : Nat := 118140960795 + 2292361 * 2 ^ 59
def prefixEnd_2292361 : Nat := 4983230072969 + 3 ^ 40 * 2292361 * 2
def baseEnd_2292361 : Nat := 784722017747607240496753

theorem tailTrace_2292361 : CollatzResearch.WordTrace tailWord_2292361 prefixEnd_2292361 784722017747607240496753 := by
  unfold tailWord_2292361
  simp only [CollatzResearch.WordTrace]
  refine ⟨83609274448175075934676937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55739516298783383956451291 83609274448175075934676937)
  ·
    refine ⟨62706955836131306951007703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83609274448175075934676937 62706955836131306951007703)
    ·
      refine ⟨94060433754196960426511555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62706955836131306951007703 94060433754196960426511555)
      ·
        refine ⟨141090650631295440639767333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94060433754196960426511555 141090650631295440639767333)
        ·
          refine ⟨26454496993367895119956375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141090650631295440639767333 26454496993367895119956375)
          ·
            refine ⟨39681745490051842679934563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26454496993367895119956375 39681745490051842679934563)
            ·
              refine ⟨59522618235077764019901845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39681745490051842679934563 59522618235077764019901845)
              ·
                refine ⟨2790122729769270188432899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59522618235077764019901845 2790122729769270188432899)
                ·
                  refine ⟨4185184094653905282649349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2790122729769270188432899 4185184094653905282649349)
                  ·
                    refine ⟨784722017747607240496753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4185184094653905282649349 784722017747607240496753)
                    ·
                      rfl

theorem cell22_2292361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_2292361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292361 prefixEnd_2292361 := by exact prefixLift 2292361
  have htrace : WordTrace (prefixWord ++ tailWord_2292361) baseStart_2292361 baseEnd_2292361 := by
    simpa [prefixWord, tailWord_2292361, baseEnd_2292361] using wordTrace_append hprefix tailTrace_2292361
  have hstable : (prefixWord ++ tailWord_2292361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292361).length < 2 ^ (prefixWord ++ tailWord_2292361).sum := by decide
  have hdescent : baseEnd_2292361 < baseStart_2292361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292481 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2292481 : Nat := 118140960795 + 2292481 * 2 ^ 59
def prefixEnd_2292481 : Nat := 4983230072969 + 3 ^ 40 * 2292481 * 2
def baseEnd_2292481 : Nat := 784763096199966927496385

theorem tailTrace_2292481 : CollatzResearch.WordTrace tailWord_2292481 prefixEnd_2292481 784763096199966927496385 := by
  unfold tailWord_2292481
  simp only [CollatzResearch.WordTrace]
  refine ⟨83613651207740336429045297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55742434138493557619363531 83613651207740336429045297)
  ·
    refine ⟨62710238405805252321783973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83613651207740336429045297 62710238405805252321783973)
    ·
      refine ⟨11758169701088484810334495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62710238405805252321783973 11758169701088484810334495)
      ·
        refine ⟨17637254551632727215501743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11758169701088484810334495 17637254551632727215501743)
        ·
          refine ⟨26455881827449090823252615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17637254551632727215501743 26455881827449090823252615)
          ·
            refine ⟨39683822741173636234878923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26455881827449090823252615 39683822741173636234878923)
            ·
              refine ⟨59525734111760454352318385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39683822741173636234878923 59525734111760454352318385)
              ·
                refine ⟨44644300583820340764238789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59525734111760454352318385 44644300583820340764238789)
                ·
                  refine ⟨8370806359466313893294773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44644300583820340764238789 8370806359466313893294773)
                  ·
                    refine ⟨784763096199966927496385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8370806359466313893294773 784763096199966927496385)
                    ·
                      rfl

theorem cell22_2292481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2292481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292481 prefixEnd_2292481 := by exact prefixLift 2292481
  have htrace : WordTrace (prefixWord ++ tailWord_2292481) baseStart_2292481 baseEnd_2292481 := by
    simpa [prefixWord, tailWord_2292481, baseEnd_2292481] using wordTrace_append hprefix tailTrace_2292481
  have hstable : (prefixWord ++ tailWord_2292481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292481).length < 2 ^ (prefixWord ++ tailWord_2292481).sum := by decide
  have hdescent : baseEnd_2292481 < baseStart_2292481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292543 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 1, 5]
def baseStart_2292543 : Nat := 118140960795 + 2292543 * 2 ^ 59
def prefixEnd_2292543 : Nat := 4983230072969 + 3 ^ 40 * 2292543 * 2
def baseEnd_2292543 : Nat := 784784320067019432446195

theorem tailTrace_2292543 : CollatzResearch.WordTrace tailWord_2292543 prefixEnd_2292543 784784320067019432446195 := by
  unfold tailWord_2292543
  simp only [CollatzResearch.WordTrace]
  refine ⟨83615912533515721017802283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55743941689010480678534855 83615912533515721017802283)
  ·
    refine ⟨125423868800273581526703425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83615912533515721017802283 125423868800273581526703425)
    ·
      refine ⟨94067901600205186145027569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125423868800273581526703425 94067901600205186145027569)
      ·
        refine ⟨70550926200153889608770677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94067901600205186145027569 70550926200153889608770677)
        ·
          refine ⟨6614149331264427150822251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70550926200153889608770677 6614149331264427150822251)
          ·
            refine ⟨9921223996896640726233377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6614149331264427150822251 9921223996896640726233377)
            ·
              refine ⟨7440917997672480544675033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9921223996896640726233377 7440917997672480544675033)
              ·
                refine ⟨5580688498254360408506275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7440917997672480544675033 5580688498254360408506275)
                ·
                  refine ⟨8371032747381540612759413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5580688498254360408506275 8371032747381540612759413)
                  ·
                    refine ⟨784784320067019432446195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8371032747381540612759413 784784320067019432446195)
                    ·
                      rfl

theorem cell22_2292543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_2292543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292543 prefixEnd_2292543 := by exact prefixLift 2292543
  have htrace : WordTrace (prefixWord ++ tailWord_2292543) baseStart_2292543 baseEnd_2292543 := by
    simpa [prefixWord, tailWord_2292543, baseEnd_2292543] using wordTrace_append hprefix tailTrace_2292543
  have hstable : (prefixWord ++ tailWord_2292543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292543).length < 2 ^ (prefixWord ++ tailWord_2292543).sum := by decide
  have hdescent : baseEnd_2292543 < baseStart_2292543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292558 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2292558 : Nat := 118140960795 + 2292558 * 2 ^ 59
def prefixEnd_2292558 : Nat := 4983230072969 + 3 ^ 40 * 2292558 * 2
def baseEnd_2292558 : Nat := 784789454873564393321149

theorem tailTrace_2292558 : CollatzResearch.WordTrace tailWord_2292558 prefixEnd_2292558 784789454873564393321149 := by
  unfold tailWord_2292558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10452057453557672322449791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55744306418974252386398885 10452057453557672322449791)
  ·
    refine ⟨15678086180336508483674687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10452057453557672322449791 15678086180336508483674687)
    ·
      refine ⟨23517129270504762725512031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15678086180336508483674687 23517129270504762725512031)
      ·
        refine ⟨35275693905757144088268047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23517129270504762725512031 35275693905757144088268047)
        ·
          refine ⟨52913540858635716132402071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35275693905757144088268047 52913540858635716132402071)
          ·
            refine ⟨79370311287953574198603107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52913540858635716132402071 79370311287953574198603107)
            ·
              refine ⟨119055466931930361297904661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79370311287953574198603107 119055466931930361297904661)
              ·
                refine ⟨5580725012434235685839281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119055466931930361297904661 5580725012434235685839281)
                ·
                  refine ⟨4185543759325676764379461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5580725012434235685839281 4185543759325676764379461)
                  ·
                    refine ⟨784789454873564393321149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4185543759325676764379461 784789454873564393321149)
                    ·
                      rfl

theorem cell22_2292558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2292558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292558 prefixEnd_2292558 := by exact prefixLift 2292558
  have htrace : WordTrace (prefixWord ++ tailWord_2292558) baseStart_2292558 baseEnd_2292558 := by
    simpa [prefixWord, tailWord_2292558, baseEnd_2292558] using wordTrace_append hprefix tailTrace_2292558
  have hstable : (prefixWord ++ tailWord_2292558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292558).length < 2 ^ (prefixWord ++ tailWord_2292558).sum := by decide
  have hdescent : baseEnd_2292558 < baseStart_2292558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292560 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 2, 3]
def baseStart_2292560 : Nat := 118140960795 + 2292560 * 2 ^ 59
def prefixEnd_2292560 : Nat := 4983230072969 + 3 ^ 40 * 2292560 * 2
def baseEnd_2292560 : Nat := 784790139514437054771143

theorem tailTrace_2292560 : CollatzResearch.WordTrace tailWord_2292560 prefixEnd_2292560 784790139514437054771143 := by
  unfold tailWord_2292560
  simp only [CollatzResearch.WordTrace]
  refine ⟨41808266287227066460585567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55744355049636088614114089 41808266287227066460585567)
  ·
    refine ⟨62712399430840599690878351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41808266287227066460585567 62712399430840599690878351)
    ·
      refine ⟨94068599146260899536317527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62712399430840599690878351 94068599146260899536317527)
      ·
        refine ⟨141102898719391349304476291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94068599146260899536317527 141102898719391349304476291)
        ·
          refine ⟨211654348079087023956714437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141102898719391349304476291 211654348079087023956714437)
          ·
            refine ⟨39685190264828816991883957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211654348079087023956714437 39685190264828816991883957)
            ·
              refine ⟨3720486587327701592989121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39685190264828816991883957 3720486587327701592989121)
              ·
                refine ⟨2790364940495776194741841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3720486587327701592989121 2790364940495776194741841)
                ·
                  refine ⟨2092773705371832146056381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2790364940495776194741841 2092773705371832146056381)
                  ·
                    refine ⟨784790139514437054771143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2092773705371832146056381 784790139514437054771143)
                    ·
                      rfl

theorem cell22_2292560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2, 3].length) (baseStart_2292560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292560 prefixEnd_2292560 := by exact prefixLift 2292560
  have htrace : WordTrace (prefixWord ++ tailWord_2292560) baseStart_2292560 baseEnd_2292560 := by
    simpa [prefixWord, tailWord_2292560, baseEnd_2292560] using wordTrace_append hprefix tailTrace_2292560
  have hstable : (prefixWord ++ tailWord_2292560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292560).length < 2 ^ (prefixWord ++ tailWord_2292560).sum := by decide
  have hdescent : baseEnd_2292560 < baseStart_2292560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292590 : List Nat := [4, 1, 2, 3, 2, 1, 1, 8]
def baseStart_2292590 : Nat := 118140960795 + 2292590 * 2 ^ 59
def prefixEnd_2292590 : Nat := 4983230072969 + 3 ^ 40 * 2292590 * 2
def baseEnd_2292590 : Nat := 87200045458614108502339

theorem tailTrace_2292590 : CollatzResearch.WordTrace tailWord_2292590 prefixEnd_2292590 87200045458614108502339 := by
  unfold tailWord_2292590
  simp only [CollatzResearch.WordTrace]
  refine ⟨10452203345543181005595403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55745084509563632029842149 10452203345543181005595403)
  ·
    refine ⟨15678305018314771508393105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10452203345543181005595403 15678305018314771508393105)
    ·
      refine ⟨11758728763736078631294829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15678305018314771508393105 11758728763736078631294829)
      ·
        refine ⟨4409523286401029486735561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11758728763736078631294829 4409523286401029486735561)
        ·
          refine ⟨3307142464800772115051671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4409523286401029486735561 3307142464800772115051671)
          ·
            refine ⟨4960713697201158172577507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307142464800772115051671 4960713697201158172577507)
            ·
              refine ⟨7441070545801737258866261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4960713697201158172577507 7441070545801737258866261)
              ·
                refine ⟨87200045458614108502339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7441070545801737258866261 87200045458614108502339)
                ·
                  rfl

theorem cell22_2292590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_2292590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292590 prefixEnd_2292590 := by exact prefixLift 2292590
  have htrace : WordTrace (prefixWord ++ tailWord_2292590) baseStart_2292590 baseEnd_2292590 := by
    simpa [prefixWord, tailWord_2292590, baseEnd_2292590] using wordTrace_append hprefix tailTrace_2292590
  have hstable : (prefixWord ++ tailWord_2292590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292590).length < 2 ^ (prefixWord ++ tailWord_2292590).sum := by decide
  have hdescent : baseEnd_2292590 < baseStart_2292590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292757 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 3, 3]
def baseStart_2292757 : Nat := 118140960795 + 2292757 * 2 ^ 59
def prefixEnd_2292757 : Nat := 4983230072969 + 3 ^ 40 * 2292757 * 2
def baseEnd_2292757 : Nat := 784857576640394207595539

theorem tailTrace_2292757 : CollatzResearch.WordTrace tailWord_2292757 prefixEnd_2292757 784857576640394207595539 := by
  unfold tailWord_2292757
  simp only [CollatzResearch.WordTrace]
  refine ⟨83623717754740435566092525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55749145169826957044061683 83623717754740435566092525)
  ·
    refine ⟨31358894158027663337284697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83623717754740435566092525 31358894158027663337284697)
    ·
      refine ⟨23519170618520747502963523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31358894158027663337284697 23519170618520747502963523)
      ·
        refine ⟨35278755927781121254445285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23519170618520747502963523 35278755927781121254445285)
        ·
          refine ⟨6614766736458960235208491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35278755927781121254445285 6614766736458960235208491)
          ·
            refine ⟨9922150104688440352812737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6614766736458960235208491 9922150104688440352812737)
            ·
              refine ⟨7441612578516330264609553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9922150104688440352812737 7441612578516330264609553)
              ·
                refine ⟨5581209433887247698457165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7441612578516330264609553 5581209433887247698457165)
                ·
                  refine ⟨2092953537707717886921437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5581209433887247698457165 2092953537707717886921437)
                  ·
                    refine ⟨784857576640394207595539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2092953537707717886921437 784857576640394207595539)
                    ·
                      rfl

theorem cell22_2292757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_2292757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292757 prefixEnd_2292757 := by exact prefixLift 2292757
  have htrace : WordTrace (prefixWord ++ tailWord_2292757) baseStart_2292757 baseEnd_2292757 := by
    simpa [prefixWord, tailWord_2292757, baseEnd_2292757] using wordTrace_append hprefix tailTrace_2292757
  have hstable : (prefixWord ++ tailWord_2292757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292757).length < 2 ^ (prefixWord ++ tailWord_2292757).sum := by decide
  have hdescent : baseEnd_2292757 < baseStart_2292757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292770 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_2292770 : Nat := 118140960795 + 2292770 * 2 ^ 59
def prefixEnd_2292770 : Nat := 4983230072969 + 3 ^ 40 * 2292770 * 2
def baseEnd_2292770 : Nat := 261620675602022169006833

theorem tailTrace_2292770 : CollatzResearch.WordTrace tailWord_2292770 prefixEnd_2292770 261620675602022169006833 := by
  unfold tailWord_2292770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20906047975923334696578941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55749461269128892524210509 20906047975923334696578941)
  ·
    refine ⟨7839767990971250511217103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20906047975923334696578941 7839767990971250511217103)
    ·
      refine ⟨11759651986456875766825655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7839767990971250511217103 11759651986456875766825655)
      ·
        refine ⟨17639477979685313650238483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11759651986456875766825655 17639477979685313650238483)
        ·
          refine ⟨26459216969527970475357725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17639477979685313650238483 26459216969527970475357725)
          ·
            refine ⟨9922206363572988928259147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26459216969527970475357725 9922206363572988928259147)
            ·
              refine ⟨14883309545359483392388721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9922206363572988928259147 14883309545359483392388721)
              ·
                refine ⟨11162482159019612544291541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14883309545359483392388721 11162482159019612544291541)
                ·
                  refine ⟨261620675602022169006833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11162482159019612544291541 261620675602022169006833)
                  ·
                    rfl

theorem cell22_2292770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_2292770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292770 prefixEnd_2292770 := by exact prefixLift 2292770
  have htrace : WordTrace (prefixWord ++ tailWord_2292770) baseStart_2292770 baseEnd_2292770 := by
    simpa [prefixWord, tailWord_2292770, baseEnd_2292770] using wordTrace_append hprefix tailTrace_2292770
  have hstable : (prefixWord ++ tailWord_2292770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292770).length < 2 ^ (prefixWord ++ tailWord_2292770).sum := by decide
  have hdescent : baseEnd_2292770 < baseStart_2292770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292783 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 1, 10]
def baseStart_2292783 : Nat := 118140960795 + 2292783 * 2 ^ 59
def prefixEnd_2292783 : Nat := 4983230072969 + 3 ^ 40 * 2292783 * 2
def baseEnd_2292783 : Nat := 784866476971738806445459

theorem tailTrace_2292783 : CollatzResearch.WordTrace tailWord_2292783 prefixEnd_2292783 784866476971738806445459 := by
  unfold tailWord_2292783
  simp only [CollatzResearch.WordTrace]
  refine ⟨83624666052646242006539003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55749777368430828004359335 83624666052646242006539003)
  ·
    refine ⟨125436999078969363009808505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83624666052646242006539003 125436999078969363009808505)
    ·
      refine ⟨94077749309227022257356379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125436999078969363009808505 94077749309227022257356379)
      ·
        refine ⟨141116623963840533386034569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94077749309227022257356379 141116623963840533386034569)
        ·
          refine ⟨105837467972880400039525927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141116623963840533386034569 105837467972880400039525927)
          ·
            refine ⟨158756201959320600059288891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105837467972880400039525927 158756201959320600059288891)
            ·
              refine ⟨238134302938980900088933337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158756201959320600059288891 238134302938980900088933337)
              ·
                refine ⟨178600727204235675066700003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238134302938980900088933337 178600727204235675066700003)
                ·
                  refine ⟨267901090806353512600050005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178600727204235675066700003 267901090806353512600050005)
                  ·
                    refine ⟨784866476971738806445459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 267901090806353512600050005 784866476971738806445459)
                    ·
                      rfl

theorem cell22_2292783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_2292783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292783 prefixEnd_2292783 := by exact prefixLift 2292783
  have htrace : WordTrace (prefixWord ++ tailWord_2292783) baseStart_2292783 baseEnd_2292783 := by
    simpa [prefixWord, tailWord_2292783, baseEnd_2292783] using wordTrace_append hprefix tailTrace_2292783
  have hstable : (prefixWord ++ tailWord_2292783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292783).length < 2 ^ (prefixWord ++ tailWord_2292783).sum := by decide
  have hdescent : baseEnd_2292783 < baseStart_2292783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292800 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_2292800 : Nat := 118140960795 + 2292800 * 2 ^ 59
def prefixEnd_2292800 : Nat := 4983230072969 + 3 ^ 40 * 2292800 * 2
def baseEnd_2292800 : Nat := 784872296419156428770407

theorem tailTrace_2292800 : CollatzResearch.WordTrace tailWord_2292800 prefixEnd_2292800 784872296419156428770407 := by
  unfold tailWord_2292800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41812643046792326954953927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55750190729056435939938569 41812643046792326954953927)
  ·
    refine ⟨62718964570188490432430891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41812643046792326954953927 62718964570188490432430891)
    ·
      refine ⟨94078446855282735648646337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62718964570188490432430891 94078446855282735648646337)
      ·
        refine ⟨70558835141462051736484753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94078446855282735648646337 70558835141462051736484753)
        ·
          refine ⟨52919126356096538802363565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70558835141462051736484753 52919126356096538802363565)
          ·
            refine ⟨19844672383536202050886337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52919126356096538802363565 19844672383536202050886337)
            ·
              refine ⟨14883504287652151538164753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19844672383536202050886337 14883504287652151538164753)
              ·
                refine ⟨11162628215739113653623565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14883504287652151538164753 11162628215739113653623565)
                ·
                  refine ⟨4185985580902167620108837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11162628215739113653623565 4185985580902167620108837)
                  ·
                    refine ⟨784872296419156428770407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4185985580902167620108837 784872296419156428770407)
                    ·
                      rfl

theorem cell22_2292800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_2292800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292800 prefixEnd_2292800 := by exact prefixLift 2292800
  have htrace : WordTrace (prefixWord ++ tailWord_2292800) baseStart_2292800 baseEnd_2292800 := by
    simpa [prefixWord, tailWord_2292800, baseEnd_2292800] using wordTrace_append hprefix tailTrace_2292800
  have hstable : (prefixWord ++ tailWord_2292800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292800).length < 2 ^ (prefixWord ++ tailWord_2292800).sum := by decide
  have hdescent : baseEnd_2292800 < baseStart_2292800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292817 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 1, 4]
def baseStart_2292817 : Nat := 118140960795 + 2292817 * 2 ^ 59
def prefixEnd_2292817 : Nat := 4983230072969 + 3 ^ 40 * 2292817 * 2
def baseEnd_2292817 : Nat := 784878115866574051095355

theorem tailTrace_2292817 : CollatzResearch.WordTrace tailWord_2292817 prefixEnd_2292817 784878115866574051095355 := by
  unfold tailWord_2292817
  simp only [CollatzResearch.WordTrace]
  refine ⟨83625906134523065813276705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55750604089682043875517803 83625906134523065813276705)
  ·
    refine ⟨62719429600892299359957529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83625906134523065813276705 62719429600892299359957529)
    ·
      refine ⟨47039572200669224519968147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62719429600892299359957529 47039572200669224519968147)
      ·
        refine ⟨70559358301003836779952221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47039572200669224519968147 70559358301003836779952221)
        ·
          refine ⟨26459759362876438792482083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70559358301003836779952221 26459759362876438792482083)
          ·
            refine ⟨39689639044314658188723125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26459759362876438792482083 39689639044314658188723125)
            ·
              refine ⟨3720903660404499205192793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39689639044314658188723125 3720903660404499205192793)
              ·
                refine ⟨2790677745303374403894595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3720903660404499205192793 2790677745303374403894595)
                ·
                  refine ⟨4186016617955061605841893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2790677745303374403894595 4186016617955061605841893)
                  ·
                    refine ⟨784878115866574051095355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4186016617955061605841893 784878115866574051095355)
                    ·
                      rfl

theorem cell22_2292817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_2292817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292817 prefixEnd_2292817 := by exact prefixLift 2292817
  have htrace : WordTrace (prefixWord ++ tailWord_2292817) baseStart_2292817 baseEnd_2292817 := by
    simpa [prefixWord, tailWord_2292817, baseEnd_2292817] using wordTrace_append hprefix tailTrace_2292817
  have hstable : (prefixWord ++ tailWord_2292817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292817).length < 2 ^ (prefixWord ++ tailWord_2292817).sum := by decide
  have hdescent : baseEnd_2292817 < baseStart_2292817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292832 : List Nat := [2, 1, 1, 3, 2, 2, 2, 5, 4]
def baseStart_2292832 : Nat := 118140960795 + 2292832 * 2 ^ 59
def prefixEnd_2292832 : Nat := 4983230072969 + 3 ^ 40 * 2292832 * 2
def baseEnd_2292832 : Nat := 261627750224373003990103

theorem tailTrace_2292832 : CollatzResearch.WordTrace tailWord_2292832 prefixEnd_2292832 261627750224373003990103 := by
  unfold tailWord_2292832
  simp only [CollatzResearch.WordTrace]
  refine ⟨41813226614734361687536375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55750968819645815583381833 41813226614734361687536375)
  ·
    refine ⟨62719839922101542531304563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41813226614734361687536375 62719839922101542531304563)
    ·
      refine ⟨94079759883152313796956845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62719839922101542531304563 94079759883152313796956845)
      ·
        refine ⟨35279909956182117673858817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94079759883152313796956845 35279909956182117673858817)
        ·
          refine ⟨26459932467136588255394113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35279909956182117673858817 26459932467136588255394113)
          ·
            refine ⟨19844949350352441191545585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26459932467136588255394113 19844949350352441191545585)
            ·
              refine ⟨14883712012764330893659189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19844949350352441191545585 14883712012764330893659189)
              ·
                refine ⟨1395348001196656021280549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14883712012764330893659189 1395348001196656021280549)
                ·
                  refine ⟨261627750224373003990103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1395348001196656021280549 261627750224373003990103)
                  ·
                    rfl

theorem cell22_2292832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 4].length) (baseStart_2292832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292832 prefixEnd_2292832 := by exact prefixLift 2292832
  have htrace : WordTrace (prefixWord ++ tailWord_2292832) baseStart_2292832 baseEnd_2292832 := by
    simpa [prefixWord, tailWord_2292832, baseEnd_2292832] using wordTrace_append hprefix tailTrace_2292832
  have hstable : (prefixWord ++ tailWord_2292832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292832).length < 2 ^ (prefixWord ++ tailWord_2292832).sum := by decide
  have hdescent : baseEnd_2292832 < baseStart_2292832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292898 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_2292898 : Nat := 118140960795 + 2292898 * 2 ^ 59
def prefixEnd_2292898 : Nat := 4983230072969 + 3 ^ 40 * 2292898 * 2
def baseEnd_2292898 : Nat := 784905843821916839820107

theorem tailTrace_2292898 : CollatzResearch.WordTrace tailWord_2292898 prefixEnd_2292898 784905843821916839820107 := by
  unfold tailWord_2292898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20907215111807404161743837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55752573631486411097983565 20907215111807404161743837)
  ·
    refine ⟨7840205666927776560653939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20907215111807404161743837 7840205666927776560653939)
    ·
      refine ⟨11760308500391664840980909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7840205666927776560653939 11760308500391664840980909)
      ·
        refine ⟨4410115687646874315367841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11760308500391664840980909 4410115687646874315367841)
        ·
          refine ⟨3307586765735155736525881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4410115687646874315367841 3307586765735155736525881)
          ·
            refine ⟨2480690074301366802394411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3307586765735155736525881 2480690074301366802394411)
            ·
              refine ⟨3721035111452050203591617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2480690074301366802394411 3721035111452050203591617)
              ·
                refine ⟨2790776333589037652693713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3721035111452050203591617 2790776333589037652693713)
                ·
                  refine ⟨2093082250191778239520285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2790776333589037652693713 2093082250191778239520285)
                  ·
                    refine ⟨784905843821916839820107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2093082250191778239520285 784905843821916839820107)
                    ·
                      rfl

theorem cell22_2292898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_2292898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292898 prefixEnd_2292898 := by exact prefixLift 2292898
  have htrace : WordTrace (prefixWord ++ tailWord_2292898) baseStart_2292898 baseEnd_2292898 := by
    simpa [prefixWord, tailWord_2292898, baseEnd_2292898] using wordTrace_append hprefix tailTrace_2292898
  have hstable : (prefixWord ++ tailWord_2292898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292898).length < 2 ^ (prefixWord ++ tailWord_2292898).sum := by decide
  have hdescent : baseEnd_2292898 < baseStart_2292898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292920 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_2292920 : Nat := 118140960795 + 2292920 * 2 ^ 59
def prefixEnd_2292920 : Nat := 4983230072969 + 3 ^ 40 * 2292920 * 2
def baseEnd_2292920 : Nat := 784913374871516115770039

theorem tailTrace_2292920 : CollatzResearch.WordTrace tailWord_2292920 prefixEnd_2292920 784913374871516115770039 := by
  unfold tailWord_2292920
  simp only [CollatzResearch.WordTrace]
  refine ⟨41814831426574957202138107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55753108568766609602850809 41814831426574957202138107)
  ·
    refine ⟨62722247139862435803207161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41814831426574957202138107 62722247139862435803207161)
    ·
      refine ⟨47041685354896826852405371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62722247139862435803207161 47041685354896826852405371)
      ·
        refine ⟨70562528032345240278608057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47041685354896826852405371 70562528032345240278608057)
        ·
          refine ⟨52921896024258930208956043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70562528032345240278608057 52921896024258930208956043)
          ·
            refine ⟨79382844036388395313434065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52921896024258930208956043 79382844036388395313434065)
            ·
              refine ⟨59537133027291296485075549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79382844036388395313434065 59537133027291296485075549)
              ·
                refine ⟨22326424885234236181903331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59537133027291296485075549 22326424885234236181903331)
                ·
                  refine ⟨33489637327851354272854997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22326424885234236181903331 33489637327851354272854997)
                  ·
                    refine ⟨784913374871516115770039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33489637327851354272854997 784913374871516115770039)
                    ·
                      rfl

theorem cell22_2292920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_2292920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292920 prefixEnd_2292920 := by exact prefixLift 2292920
  have htrace : WordTrace (prefixWord ++ tailWord_2292920) baseStart_2292920 baseEnd_2292920 := by
    simpa [prefixWord, tailWord_2292920, baseEnd_2292920] using wordTrace_append hprefix tailTrace_2292920
  have hstable : (prefixWord ++ tailWord_2292920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292920).length < 2 ^ (prefixWord ++ tailWord_2292920).sum := by decide
  have hdescent : baseEnd_2292920 < baseStart_2292920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292935 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2292935 : Nat := 118140960795 + 2292935 * 2 ^ 59
def prefixEnd_2292935 : Nat := 4983230072969 + 3 ^ 40 * 2292935 * 2
def baseEnd_2292935 : Nat := 784918509678061076644993

theorem tailTrace_2292935 : CollatzResearch.WordTrace tailWord_2292935 prefixEnd_2292935 784918509678061076644993 := by
  unfold tailWord_2292935
  simp only [CollatzResearch.WordTrace]
  refine ⟨83630209948095571966072259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55753473298730381310714839 83630209948095571966072259)
  ·
    refine ⟨125445314922143357949108389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83630209948095571966072259 125445314922143357949108389)
    ·
      refine ⟨23520996547901879615457823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125445314922143357949108389 23520996547901879615457823)
      ·
        refine ⟨35281494821852819423186735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23520996547901879615457823 35281494821852819423186735)
        ·
          refine ⟨52922242232779229134780103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35281494821852819423186735 52922242232779229134780103)
          ·
            refine ⟨79383363349168843702170155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52922242232779229134780103 79383363349168843702170155)
            ·
              refine ⟨119075045023753265553255233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79383363349168843702170155 119075045023753265553255233)
              ·
                refine ⟨89306283767814949164941425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119075045023753265553255233 89306283767814949164941425)
                ·
                  refine ⟨66979712825861211873706069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89306283767814949164941425 66979712825861211873706069)
                  ·
                    refine ⟨784918509678061076644993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66979712825861211873706069 784918509678061076644993)
                    ·
                      rfl

theorem cell22_2292935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2292935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2292935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2292935 prefixEnd_2292935 := by exact prefixLift 2292935
  have htrace : WordTrace (prefixWord ++ tailWord_2292935) baseStart_2292935 baseEnd_2292935 := by
    simpa [prefixWord, tailWord_2292935, baseEnd_2292935] using wordTrace_append hprefix tailTrace_2292935
  have hstable : (prefixWord ++ tailWord_2292935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292935).length < 2 ^ (prefixWord ++ tailWord_2292935).sum := by decide
  have hdescent : baseEnd_2292935 < baseStart_2292935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293016 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 2, 3]
def baseStart_2293016 : Nat := 118140960795 + 2293016 * 2 ^ 59
def prefixEnd_2293016 : Nat := 4983230072969 + 3 ^ 40 * 2293016 * 2
def baseEnd_2293016 : Nat := 784946237633403865369745

theorem tailTrace_2293016 : CollatzResearch.WordTrace tailWord_2293016 prefixEnd_2293016 784946237633403865369745 := by
  unfold tailWord_2293016
  simp only [CollatzResearch.WordTrace]
  refine ⟨41816582130401061399885451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55755442840534748533180601 41816582130401061399885451)
  ·
    refine ⟨62724873195601592099828177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41816582130401061399885451 62724873195601592099828177)
    ·
      refine ⟨47043654896701194074871133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62724873195601592099828177 47043654896701194074871133)
      ·
        refine ⟨17641370586262947778076675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47043654896701194074871133 17641370586262947778076675)
        ·
          refine ⟨26462055879394421667115013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17641370586262947778076675 26462055879394421667115013)
          ·
            refine ⟨4961635477386454062584065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26462055879394421667115013 4961635477386454062584065)
            ·
              refine ⟨3721226608039840546938049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4961635477386454062584065 3721226608039840546938049)
              ·
                refine ⟨2790919956029880410203537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3721226608039840546938049 2790919956029880410203537)
                ·
                  refine ⟨2093189967022410307652653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2790919956029880410203537 2093189967022410307652653)
                  ·
                    refine ⟨784946237633403865369745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2093189967022410307652653 784946237633403865369745)
                    ·
                      rfl

theorem cell22_2293016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_2293016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293016 prefixEnd_2293016 := by exact prefixLift 2293016
  have htrace : WordTrace (prefixWord ++ tailWord_2293016) baseStart_2293016 baseEnd_2293016 := by
    simpa [prefixWord, tailWord_2293016, baseEnd_2293016] using wordTrace_append hprefix tailTrace_2293016
  have hstable : (prefixWord ++ tailWord_2293016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293016).length < 2 ^ (prefixWord ++ tailWord_2293016).sum := by decide
  have hdescent : baseEnd_2293016 < baseStart_2293016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293018 : List Nat := [3, 1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_2293018 : Nat := 118140960795 + 2293018 * 2 ^ 59
def prefixEnd_2293018 : Nat := 4983230072969 + 3 ^ 40 * 2293018 * 2
def baseEnd_2293018 : Nat := 261648974091425508939913

theorem tailTrace_2293018 : CollatzResearch.WordTrace tailWord_2293018 prefixEnd_2293018 261648974091425508939913 := by
  unfold tailWord_2293018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20908309301698719285335927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55755491471196584760895805 20908309301698719285335927)
  ·
    refine ⟨31362463952548078928003891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20908309301698719285335927 31362463952548078928003891)
    ·
      refine ⟨47043695928822118392005837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31362463952548078928003891 47043695928822118392005837)
      ·
        refine ⟨17641385973308294397002189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47043695928822118392005837 17641385973308294397002189)
        ·
          refine ⟨6615519739990610398875821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17641385973308294397002189 6615519739990610398875821)
          ·
            refine ⟨2480819902496478899578433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6615519739990610398875821 2480819902496478899578433)
            ·
              refine ⟨1860614926872359174683825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2480819902496478899578433 1860614926872359174683825)
              ·
                refine ⟨1395461195154269381012869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860614926872359174683825 1395461195154269381012869)
                ·
                  refine ⟨261648974091425508939913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1395461195154269381012869 261648974091425508939913)
                  ·
                    rfl

theorem cell22_2293018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_2293018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293018 prefixEnd_2293018 := by exact prefixLift 2293018
  have htrace : WordTrace (prefixWord ++ tailWord_2293018) baseStart_2293018 baseEnd_2293018 := by
    simpa [prefixWord, tailWord_2293018, baseEnd_2293018] using wordTrace_append hprefix tailTrace_2293018
  have hstable : (prefixWord ++ tailWord_2293018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293018).length < 2 ^ (prefixWord ++ tailWord_2293018).sum := by decide
  have hdescent : baseEnd_2293018 < baseStart_2293018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293029 : List Nat := [1, 3, 1, 2, 4, 3, 1, 7]
def baseStart_2293029 : Nat := 118140960795 + 2293029 * 2 ^ 59
def prefixEnd_2293029 : Nat := 4983230072969 + 3 ^ 40 * 2293029 * 2
def baseEnd_2293029 : Nat := 87216743088786240532745

theorem tailTrace_2293029 : CollatzResearch.WordTrace tailWord_2293029 prefixEnd_2293029 87216743088786240532745 := by
  unfold tailWord_2293029
  simp only [CollatzResearch.WordTrace]
  refine ⟨83633638409755026019994141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55755758939836684013329427 83633638409755026019994141)
  ·
    refine ⟨31362614403658134757497803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83633638409755026019994141 31362614403658134757497803)
    ·
      refine ⟨47043921605487202136246705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31362614403658134757497803 47043921605487202136246705)
      ·
        refine ⟨35282941204115401602185029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47043921605487202136246705 35282941204115401602185029)
        ·
          refine ⟨6615551475771637800409693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35282941204115401602185029 6615551475771637800409693)
          ·
            refine ⟨2480831803414364175153635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6615551475771637800409693 2480831803414364175153635)
            ·
              refine ⟨3721247705121546262730453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2480831803414364175153635 3721247705121546262730453)
              ·
                refine ⟨87216743088786240532745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3721247705121546262730453 87216743088786240532745)
                ·
                  rfl

theorem cell22_2293029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 7].length) (baseStart_2293029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293029 prefixEnd_2293029 := by exact prefixLift 2293029
  have htrace : WordTrace (prefixWord ++ tailWord_2293029) baseStart_2293029 baseEnd_2293029 := by
    simpa [prefixWord, tailWord_2293029, baseEnd_2293029] using wordTrace_append hprefix tailTrace_2293029
  have hstable : (prefixWord ++ tailWord_2293029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293029).length < 2 ^ (prefixWord ++ tailWord_2293029).sum := by decide
  have hdescent : baseEnd_2293029 < baseStart_2293029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293072 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_2293072 : Nat := 118140960795 + 2293072 * 2 ^ 59
def prefixEnd_2293072 : Nat := 4983230072969 + 3 ^ 40 * 2293072 * 2
def baseEnd_2293072 : Nat := 784965407577838385969573

theorem tailTrace_2293072 : CollatzResearch.WordTrace tailWord_2293072 prefixEnd_2293072 784965407577838385969573 := by
  unfold tailWord_2293072
  simp only [CollatzResearch.WordTrace]
  refine ⟨41817603374299622181904735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55756804499066162909206313 41817603374299622181904735)
  ·
    refine ⟨62726405061449433272857103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41817603374299622181904735 62726405061449433272857103)
    ·
      refine ⟨94089607592174149909285655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62726405061449433272857103 94089607592174149909285655)
      ·
        refine ⟨141134411388261224863928483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94089607592174149909285655 141134411388261224863928483)
        ·
          refine ⟨211701617082391837295892725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141134411388261224863928483 211701617082391837295892725)
          ·
            refine ⟨19847026601474234746489943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211701617082391837295892725 19847026601474234746489943)
            ·
              refine ⟨29770539902211352119734915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19847026601474234746489943 29770539902211352119734915)
              ·
                refine ⟨44655809853317028179602373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29770539902211352119734915 44655809853317028179602373)
                ·
                  refine ⟨8372964347496942783675445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44655809853317028179602373 8372964347496942783675445)
                  ·
                    refine ⟨784965407577838385969573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8372964347496942783675445 784965407577838385969573)
                    ·
                      rfl

theorem cell22_2293072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_2293072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293072 prefixEnd_2293072 := by exact prefixLift 2293072
  have htrace : WordTrace (prefixWord ++ tailWord_2293072) baseStart_2293072 baseEnd_2293072 := by
    simpa [prefixWord, tailWord_2293072, baseEnd_2293072] using wordTrace_append hprefix tailTrace_2293072
  have hstable : (prefixWord ++ tailWord_2293072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293072).length < 2 ^ (prefixWord ++ tailWord_2293072).sum := by decide
  have hdescent : baseEnd_2293072 < baseStart_2293072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293091 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 5]
def baseStart_2293091 : Nat := 118140960795 + 2293091 * 2 ^ 59
def prefixEnd_2293091 : Nat := 4983230072969 + 3 ^ 40 * 2293091 * 2
def baseEnd_2293091 : Nat := 261657303888709556581505

theorem tailTrace_2293091 : CollatzResearch.WordTrace tailWord_2293091 prefixEnd_2293091 261657303888709556581505 := by
  unfold tailWord_2293091
  simp only [CollatzResearch.WordTrace]
  refine ⟨83635899735530410608751127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55757266490353607072500751 83635899735530410608751127)
  ·
    refine ⟨125453849603295615913126691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83635899735530410608751127 125453849603295615913126691)
    ·
      refine ⟨188180774404943423869690037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125453849603295615913126691 188180774404943423869690037)
      ·
        refine ⟨17641947600463445987783441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188180774404943423869690037 17641947600463445987783441)
        ·
          refine ⟨13231460700347584490837581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17641947600463445987783441 13231460700347584490837581)
          ·
            refine ⟨4961797762630344184064093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13231460700347584490837581 4961797762630344184064093)
            ·
              refine ⟨1860674160986379069024035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4961797762630344184064093 1860674160986379069024035)
              ·
                refine ⟨2791011241479568603536053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860674160986379069024035 2791011241479568603536053)
                ·
                  refine ⟨261657303888709556581505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2791011241479568603536053 261657303888709556581505)
                  ·
                    rfl

theorem cell22_2293091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 5].length) (baseStart_2293091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293091 prefixEnd_2293091 := by exact prefixLift 2293091
  have htrace : WordTrace (prefixWord ++ tailWord_2293091) baseStart_2293091 baseEnd_2293091 := by
    simpa [prefixWord, tailWord_2293091, baseEnd_2293091] using wordTrace_append hprefix tailTrace_2293091
  have hstable : (prefixWord ++ tailWord_2293091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293091).length < 2 ^ (prefixWord ++ tailWord_2293091).sum := by decide
  have hdescent : baseEnd_2293091 < baseStart_2293091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293194 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_2293194 : Nat := 118140960795 + 2293194 * 2 ^ 59
def prefixEnd_2293194 : Nat := 4983230072969 + 3 ^ 40 * 2293194 * 2
def baseEnd_2293194 : Nat := 785007170671070734419199

theorem tailTrace_2293194 : CollatzResearch.WordTrace tailWord_2293194 prefixEnd_2293194 785007170671070734419199 := by
  unfold tailWord_2293194
  simp only [CollatzResearch.WordTrace]
  refine ⟨20909914113539314799937659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55759770969438172799833757 20909914113539314799937659)
  ·
    refine ⟨31364871170308972199906489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20909914113539314799937659 31364871170308972199906489)
    ·
      refine ⟨23523653377731729149929867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31364871170308972199906489 23523653377731729149929867)
      ·
        refine ⟨35285480066597593724894801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23523653377731729149929867 35285480066597593724894801)
        ·
          refine ⟨26464110049948195293671101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35285480066597593724894801 26464110049948195293671101)
          ·
            refine ⟨9924041268730573235126663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26464110049948195293671101 9924041268730573235126663)
            ·
              refine ⟨14886061903095859852689995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9924041268730573235126663 14886061903095859852689995)
              ·
                refine ⟨22329092854643789779034993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14886061903095859852689995 22329092854643789779034993)
                ·
                  refine ⟨16746819640982842334276245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22329092854643789779034993 16746819640982842334276245)
                  ·
                    refine ⟨785007170671070734419199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16746819640982842334276245 785007170671070734419199)
                    ·
                      rfl

theorem cell22_2293194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_2293194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293194 prefixEnd_2293194 := by exact prefixLift 2293194
  have htrace : WordTrace (prefixWord ++ tailWord_2293194) baseStart_2293194 baseEnd_2293194 := by
    simpa [prefixWord, tailWord_2293194, baseEnd_2293194] using wordTrace_append hprefix tailTrace_2293194
  have hstable : (prefixWord ++ tailWord_2293194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293194).length < 2 ^ (prefixWord ++ tailWord_2293194).sum := by decide
  have hdescent : baseEnd_2293194 < baseStart_2293194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293213 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_2293213 : Nat := 118140960795 + 2293213 * 2 ^ 59
def prefixEnd_2293213 : Nat := 4983230072969 + 3 ^ 40 * 2293213 * 2
def baseEnd_2293213 : Nat := 785013674759361018194141

theorem tailTrace_2293213 : CollatzResearch.WordTrace tailWord_2293213 prefixEnd_2293213 785013674759361018194141 := by
  unfold tailWord_2293213
  simp only [CollatzResearch.WordTrace]
  refine ⟨83640349441088425444692293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55760232960725616963128195 83640349441088425444692293)
  ·
    refine ⟨15682565520204079770879805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83640349441088425444692293 15682565520204079770879805)
    ·
      refine ⟨5880962070076529914079927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15682565520204079770879805 5880962070076529914079927)
      ·
        refine ⟨8821443105114794871119891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5880962070076529914079927 8821443105114794871119891)
        ·
          refine ⟨13232164657672192306679837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8821443105114794871119891 13232164657672192306679837)
          ·
            refine ⟨4962061746627072115004939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13232164657672192306679837 4962061746627072115004939)
            ·
              refine ⟨7443092619940608172507409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4962061746627072115004939 7443092619940608172507409)
              ·
                refine ⟨5582319464955456129380557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7443092619940608172507409 5582319464955456129380557)
                ·
                  refine ⟨2093369799358296048517709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5582319464955456129380557 2093369799358296048517709)
                  ·
                    refine ⟨785013674759361018194141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2093369799358296048517709 785013674759361018194141)
                    ·
                      rfl

theorem cell22_2293213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_2293213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293213 prefixEnd_2293213 := by exact prefixLift 2293213
  have htrace : WordTrace (prefixWord ++ tailWord_2293213) baseStart_2293213 baseEnd_2293213 := by
    simpa [prefixWord, tailWord_2293213, baseEnd_2293213] using wordTrace_append hprefix tailTrace_2293213
  have hstable : (prefixWord ++ tailWord_2293213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293213).length < 2 ^ (prefixWord ++ tailWord_2293213).sum := by decide
  have hdescent : baseEnd_2293213 < baseStart_2293213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293224 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2293224 : Nat := 118140960795 + 2293224 * 2 ^ 59
def prefixEnd_2293224 : Nat := 4983230072969 + 3 ^ 40 * 2293224 * 2
def baseEnd_2293224 : Nat := 785017440284160656169107

theorem tailTrace_2293224 : CollatzResearch.WordTrace tailWord_2293224 prefixEnd_2293224 785017440284160656169107 := by
  unfold tailWord_2293224
  simp only [CollatzResearch.WordTrace]
  refine ⟨41820375322024287161671363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55760500429365716215561817 41820375322024287161671363)
  ·
    refine ⟨62730562983036430742507045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41820375322024287161671363 62730562983036430742507045)
    ·
      refine ⟨11761980559319330764220071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62730562983036430742507045 11761980559319330764220071)
      ·
        refine ⟨17642970838978996146330107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11761980559319330764220071 17642970838978996146330107)
        ·
          refine ⟨26464456258468494219495161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17642970838978996146330107 26464456258468494219495161)
          ·
            refine ⟨19848342193851370664621371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26464456258468494219495161 19848342193851370664621371)
            ·
              refine ⟨29772513290777055996932057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19848342193851370664621371 29772513290777055996932057)
              ·
                refine ⟨22329384968082791997699043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29772513290777055996932057 22329384968082791997699043)
                ·
                  refine ⟨33494077452124187996548565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22329384968082791997699043 33494077452124187996548565)
                  ·
                    refine ⟨785017440284160656169107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33494077452124187996548565 785017440284160656169107)
                    ·
                      rfl

theorem cell22_2293224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2293224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293224 prefixEnd_2293224 := by exact prefixLift 2293224
  have htrace : WordTrace (prefixWord ++ tailWord_2293224) baseStart_2293224 baseEnd_2293224 := by
    simpa [prefixWord, tailWord_2293224, baseEnd_2293224] using wordTrace_append hprefix tailTrace_2293224
  have hstable : (prefixWord ++ tailWord_2293224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293224).length < 2 ^ (prefixWord ++ tailWord_2293224).sum := by decide
  have hdescent : baseEnd_2293224 < baseStart_2293224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293230 : List Nat := [4, 1, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_2293230 : Nat := 118140960795 + 2293230 * 2 ^ 59
def prefixEnd_2293230 : Nat := 4983230072969 + 3 ^ 40 * 2293230 * 2
def baseEnd_2293230 : Nat := 785019494206778640519089

theorem tailTrace_2293230 : CollatzResearch.WordTrace tailWord_2293230 prefixEnd_2293230 785019494206778640519089 := by
  unfold tailWord_2293230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10455121185253354668507643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55760646321351224898707429 10455121185253354668507643)
  ·
    refine ⟨15682681777880032002761465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10455121185253354668507643 15682681777880032002761465)
    ·
      refine ⟨11762011333410024002071099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15682681777880032002761465 11762011333410024002071099)
      ·
        refine ⟨17643017000115036003106649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11762011333410024002071099 17643017000115036003106649)
        ·
          refine ⟨13232262750086277002329987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17643017000115036003106649 13232262750086277002329987)
          ·
            refine ⟨19848394125129415503494981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13232262750086277002329987 19848394125129415503494981)
            ·
              refine ⟨3721573898461765406905309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19848394125129415503494981 3721573898461765406905309)
              ·
                refine ⟨1395590211923162027589491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3721573898461765406905309 1395590211923162027589491)
                ·
                  refine ⟨2093385317884743041384237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395590211923162027589491 2093385317884743041384237)
                  ·
                    refine ⟨785019494206778640519089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2093385317884743041384237 785019494206778640519089)
                    ·
                      rfl

theorem cell22_2293230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_2293230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293230 prefixEnd_2293230 := by exact prefixLift 2293230
  have htrace : WordTrace (prefixWord ++ tailWord_2293230) baseStart_2293230 baseEnd_2293230 := by
    simpa [prefixWord, tailWord_2293230, baseEnd_2293230] using wordTrace_append hprefix tailTrace_2293230
  have hstable : (prefixWord ++ tailWord_2293230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293230).length < 2 ^ (prefixWord ++ tailWord_2293230).sum := by decide
  have hdescent : baseEnd_2293230 < baseStart_2293230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293239 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 5, 4]
def baseStart_2293239 : Nat := 118140960795 + 2293239 * 2 ^ 59
def prefixEnd_2293239 : Nat := 4983230072969 + 3 ^ 40 * 2293239 * 2
def baseEnd_2293239 : Nat := 785022575090705617044061

theorem tailTrace_2293239 : CollatzResearch.WordTrace tailWord_2293239 prefixEnd_2293239 785022575090705617044061 := by
  unfold tailWord_2293239
  simp only [CollatzResearch.WordTrace]
  refine ⟨83641297738994231885138771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55760865159329487923425847 83641297738994231885138771)
  ·
    refine ⟨125461946608491347827708157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83641297738994231885138771 125461946608491347827708157)
    ·
      refine ⟨47048229978184255435390559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125461946608491347827708157 47048229978184255435390559)
      ·
        refine ⟨70572344967276383153085839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47048229978184255435390559 70572344967276383153085839)
        ·
          refine ⟨105858517450914574729628759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70572344967276383153085839 105858517450914574729628759)
          ·
            refine ⟨158787776176371862094443139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105858517450914574729628759 158787776176371862094443139)
            ·
              refine ⟨238181664264557793141664709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158787776176371862094443139 238181664264557793141664709)
              ·
                refine ⟨44659062049604586214062133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238181664264557793141664709 44659062049604586214062133)
                ·
                  refine ⟨4186787067150429957568325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44659062049604586214062133 4186787067150429957568325)
                  ·
                    refine ⟨785022575090705617044061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4186787067150429957568325 785022575090705617044061)
                    ·
                      rfl

theorem cell22_2293239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_2293239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293239 prefixEnd_2293239 := by exact prefixLift 2293239
  have htrace : WordTrace (prefixWord ++ tailWord_2293239) baseStart_2293239 baseEnd_2293239 := by
    simpa [prefixWord, tailWord_2293239, baseEnd_2293239] using wordTrace_append hprefix tailTrace_2293239
  have hstable : (prefixWord ++ tailWord_2293239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293239).length < 2 ^ (prefixWord ++ tailWord_2293239).sum := by decide
  have hdescent : baseEnd_2293239 < baseStart_2293239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293299 : List Nat := [1, 1, 1, 2, 4, 3, 10]
def baseStart_2293299 : Nat := 118140960795 + 2293299 * 2 ^ 59
def prefixEnd_2293299 : Nat := 4983230072969 + 3 ^ 40 * 2293299 * 2
def baseEnd_2293299 : Nat := 29075670900625387427551

theorem tailTrace_2293299 : CollatzResearch.WordTrace tailWord_2293299 prefixEnd_2293299 29075670900625387427551 := by
  unfold tailWord_2293299
  simp only [CollatzResearch.WordTrace]
  refine ⟨83643486118776862132322951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55762324079184574754881967 83643486118776862132322951)
  ·
    refine ⟨125465229178165293198484427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83643486118776862132322951 125465229178165293198484427)
    ·
      refine ⟨188197843767247939797726641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125465229178165293198484427 188197843767247939797726641)
      ·
        refine ⟨141148382825435954848294981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188197843767247939797726641 141148382825435954848294981)
        ·
          refine ⟨26465321779769241534055309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141148382825435954848294981 26465321779769241534055309)
          ·
            refine ⟨9924495667413465575270741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26465321779769241534055309 9924495667413465575270741)
            ·
              refine ⟨29075670900625387427551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9924495667413465575270741 29075670900625387427551)
              ·
                rfl

theorem cell22_2293299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 10].length) (baseStart_2293299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293299 prefixEnd_2293299 := by exact prefixLift 2293299
  have htrace : WordTrace (prefixWord ++ tailWord_2293299) baseStart_2293299 baseEnd_2293299 := by
    simpa [prefixWord, tailWord_2293299, baseEnd_2293299] using wordTrace_append hprefix tailTrace_2293299
  have hstable : (prefixWord ++ tailWord_2293299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293299).length < 2 ^ (prefixWord ++ tailWord_2293299).sum := by decide
  have hdescent : baseEnd_2293299 < baseStart_2293299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293301 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_2293301 : Nat := 118140960795 + 2293301 * 2 ^ 59
def prefixEnd_2293301 : Nat := 4983230072969 + 3 ^ 40 * 2293301 * 2
def baseEnd_2293301 : Nat := 785043798957758121993871

theorem tailTrace_2293301 : CollatzResearch.WordTrace tailWord_2293301 prefixEnd_2293301 785043798957758121993871 := by
  unfold tailWord_2293301
  simp only [CollatzResearch.WordTrace]
  refine ⟨83643559064769616473895757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55762372709846410982597171 83643559064769616473895757)
  ·
    refine ⟨31366334649288606177710909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83643559064769616473895757 31366334649288606177710909)
    ·
      refine ⟨11762375493483227316641591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31366334649288606177710909 11762375493483227316641591)
      ·
        refine ⟨17643563240224840974962387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11762375493483227316641591 17643563240224840974962387)
        ·
          refine ⟨26465344860337261462443581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17643563240224840974962387 26465344860337261462443581)
          ·
            refine ⟨9924504322626473048416343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26465344860337261462443581 9924504322626473048416343)
            ·
              refine ⟨14886756483939709572624515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9924504322626473048416343 14886756483939709572624515)
              ·
                refine ⟨22330134725909564358936773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14886756483939709572624515 22330134725909564358936773)
                ·
                  refine ⟨4186900261108043317300645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22330134725909564358936773 4186900261108043317300645)
                  ·
                    refine ⟨785043798957758121993871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4186900261108043317300645 785043798957758121993871)
                    ·
                      rfl

theorem cell22_2293301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_2293301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293301 prefixEnd_2293301 := by exact prefixLift 2293301
  have htrace : WordTrace (prefixWord ++ tailWord_2293301) baseStart_2293301 baseEnd_2293301 := by
    simpa [prefixWord, tailWord_2293301, baseEnd_2293301] using wordTrace_append hprefix tailTrace_2293301
  have hstable : (prefixWord ++ tailWord_2293301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293301).length < 2 ^ (prefixWord ++ tailWord_2293301).sum := by decide
  have hdescent : baseEnd_2293301 < baseStart_2293301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293305 : List Nat := [1, 2, 1, 5, 1, 3, 3, 2, 4]
def baseStart_2293305 : Nat := 118140960795 + 2293305 * 2 ^ 59
def prefixEnd_2293305 : Nat := 4983230072969 + 3 ^ 40 * 2293305 * 2
def baseEnd_2293305 : Nat := 261681722746501148297953

theorem tailTrace_2293305 : CollatzResearch.WordTrace tailWord_2293305 prefixEnd_2293305 261681722746501148297953 := by
  unfold tailWord_2293305
  simp only [CollatzResearch.WordTrace]
  refine ⟨83643704956755125157041369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55762469971170083438027579 83643704956755125157041369)
  ·
    refine ⟨62732778717566343867781027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83643704956755125157041369 62732778717566343867781027)
    ·
      refine ⟨94099168076349515801671541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62732778717566343867781027 94099168076349515801671541)
      ·
        refine ⟨8821797007157767106406707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94099168076349515801671541 8821797007157767106406707)
        ·
          refine ⟨13232695510736650659610061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8821797007157767106406707 13232695510736650659610061)
          ·
            refine ⟨4962260816526243997353773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13232695510736650659610061 4962260816526243997353773)
            ·
              refine ⟨1860847806197341499007665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4962260816526243997353773 1860847806197341499007665)
              ·
                refine ⟨1395635854648006124255749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860847806197341499007665 1395635854648006124255749)
                ·
                  refine ⟨261681722746501148297953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1395635854648006124255749 261681722746501148297953)
                  ·
                    rfl

theorem cell22_2293305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 4].length) (baseStart_2293305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293305 prefixEnd_2293305 := by exact prefixLift 2293305
  have htrace : WordTrace (prefixWord ++ tailWord_2293305) baseStart_2293305 baseEnd_2293305 := by
    simpa [prefixWord, tailWord_2293305, baseEnd_2293305] using wordTrace_append hprefix tailTrace_2293305
  have hstable : (prefixWord ++ tailWord_2293305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293305).length < 2 ^ (prefixWord ++ tailWord_2293305).sum := by decide
  have hdescent : baseEnd_2293305 < baseStart_2293305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293376 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_2293376 : Nat := 118140960795 + 2293376 * 2 ^ 59
def prefixEnd_2293376 : Nat := 4983230072969 + 3 ^ 40 * 2293376 * 2
def baseEnd_2293376 : Nat := 785069472990482926368641

theorem tailTrace_2293376 : CollatzResearch.WordTrace tailWord_2293376 prefixEnd_2293376 785069472990482926368641 := by
  unfold tailWord_2293376
  simp only [CollatzResearch.WordTrace]
  refine ⟨41823147269748952141437991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55764196359665269521917321 41823147269748952141437991)
  ·
    refine ⟨62734720904623428212156987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41823147269748952141437991 62734720904623428212156987)
    ·
      refine ⟨94102081356935142318235481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62734720904623428212156987 94102081356935142318235481)
      ·
        refine ⟨70576561017701356738676611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94102081356935142318235481 70576561017701356738676611)
        ·
          refine ⟨105864841526552035108014917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70576561017701356738676611 105864841526552035108014917)
          ·
            refine ⟨19849657786228506582752797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105864841526552035108014917 19849657786228506582752797)
            ·
              refine ⟨7443621669835689968532299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19849657786228506582752797 7443621669835689968532299)
              ·
                refine ⟨11165432504753534952798449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7443621669835689968532299 11165432504753534952798449)
                ·
                  refine ⟨8374074378565151214598837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11165432504753534952798449 8374074378565151214598837)
                  ·
                    refine ⟨785069472990482926368641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8374074378565151214598837 785069472990482926368641)
                    ·
                      rfl

theorem cell22_2293376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_2293376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293376 prefixEnd_2293376 := by exact prefixLift 2293376
  have htrace : WordTrace (prefixWord ++ tailWord_2293376) baseStart_2293376 baseEnd_2293376 := by
    simpa [prefixWord, tailWord_2293376, baseEnd_2293376] using wordTrace_append hprefix tailTrace_2293376
  have hstable : (prefixWord ++ tailWord_2293376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293376).length < 2 ^ (prefixWord ++ tailWord_2293376).sum := by decide
  have hdescent : baseEnd_2293376 < baseStart_2293376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293423 : List Nat := [1, 1, 2, 1, 2, 4, 1, 6, 4]
def baseStart_2293423 : Nat := 118140960795 + 2293423 * 2 ^ 59
def prefixEnd_2293423 : Nat := 4983230072969 + 3 ^ 40 * 2293423 * 2
def baseEnd_2293423 : Nat := 261695187350330156814499

theorem tailTrace_2293423 : CollatzResearch.WordTrace tailWord_2293423 prefixEnd_2293423 261695187350330156814499 := by
  unfold tailWord_2293423
  simp only [CollatzResearch.WordTrace]
  refine ⟨83648008770327631309836923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55765339180218420873224615 83648008770327631309836923)
  ·
    refine ⟨125472013155491446964755385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83648008770327631309836923 125472013155491446964755385)
    ·
      refine ⟨94104009866618585223566539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125472013155491446964755385 94104009866618585223566539)
      ·
        refine ⟨141156014799927877835349809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94104009866618585223566539 141156014799927877835349809)
        ·
          refine ⟨105867011099945908376512357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141156014799927877835349809 105867011099945908376512357)
          ·
            refine ⟨19850064581239857820596067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105867011099945908376512357 19850064581239857820596067)
            ·
              refine ⟨29775096871859786730894101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19850064581239857820596067 29775096871859786730894101)
              ·
                refine ⟨1395707665868427503010661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29775096871859786730894101 1395707665868427503010661)
                ·
                  refine ⟨261695187350330156814499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1395707665868427503010661 261695187350330156814499)
                  ·
                    rfl

theorem cell22_2293423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 4].length) (baseStart_2293423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293423 prefixEnd_2293423 := by exact prefixLift 2293423
  have htrace : WordTrace (prefixWord ++ tailWord_2293423) baseStart_2293423 baseEnd_2293423 := by
    simpa [prefixWord, tailWord_2293423, baseEnd_2293423] using wordTrace_append hprefix tailTrace_2293423
  have hstable : (prefixWord ++ tailWord_2293423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293423).length < 2 ^ (prefixWord ++ tailWord_2293423).sum := by decide
  have hdescent : baseEnd_2293423 < baseStart_2293423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293481 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_2293481 : Nat := 118140960795 + 2293481 * 2 ^ 59
def prefixEnd_2293481 : Nat := 4983230072969 + 3 ^ 40 * 2293481 * 2
def baseEnd_2293481 : Nat := 785105416636297652493319

theorem tailTrace_2293481 : CollatzResearch.WordTrace tailWord_2293481 prefixEnd_2293481 785105416636297652493319 := by
  unfold tailWord_2293481
  simp only [CollatzResearch.WordTrace]
  refine ⟨83650124204117507215448297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55766749469411671476965531 83650124204117507215448297)
  ·
    refine ⟨62737593153088130411586223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83650124204117507215448297 62737593153088130411586223)
    ·
      refine ⟨94106389729632195617379335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62737593153088130411586223 94106389729632195617379335)
      ·
        refine ⟨141159584594448293426069003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94106389729632195617379335 141159584594448293426069003)
        ·
          refine ⟨211739376891672440139103505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141159584594448293426069003 211739376891672440139103505)
          ·
            refine ⟨158804532668754330104327629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211739376891672440139103505 158804532668754330104327629)
            ·
              refine ⟨59551699750782873789122861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158804532668754330104327629 59551699750782873789122861)
              ·
                refine ⟨22331887406543577670921073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59551699750782873789122861 22331887406543577670921073)
                ·
                  refine ⟨16748915554907683253190805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22331887406543577670921073 16748915554907683253190805)
                  ·
                    refine ⟨785105416636297652493319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16748915554907683253190805 785105416636297652493319)
                    ·
                      rfl

theorem cell22_2293481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_2293481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293481 prefixEnd_2293481 := by exact prefixLift 2293481
  have htrace : WordTrace (prefixWord ++ tailWord_2293481) baseStart_2293481 baseEnd_2293481 := by
    simpa [prefixWord, tailWord_2293481, baseEnd_2293481] using wordTrace_append hprefix tailTrace_2293481
  have hstable : (prefixWord ++ tailWord_2293481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293481).length < 2 ^ (prefixWord ++ tailWord_2293481).sum := by decide
  have hdescent : baseEnd_2293481 < baseStart_2293481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293496 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 9]
def baseStart_2293496 : Nat := 118140960795 + 2293496 * 2 ^ 59
def prefixEnd_2293496 : Nat := 4983230072969 + 3 ^ 40 * 2293496 * 2
def baseEnd_2293496 : Nat := 261703517147614204456091

theorem tailTrace_2293496 : CollatzResearch.WordTrace tailWord_2293496 prefixEnd_2293496 261703517147614204456091 := by
  unfold tailWord_2293496
  simp only [CollatzResearch.WordTrace]
  refine ⟨41825335649531582388622171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55767114199375443184829561 41825335649531582388622171)
  ·
    refine ⟨62738003474297373582933257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41825335649531582388622171 62738003474297373582933257)
    ·
      refine ⟨47053502605723030187199943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62738003474297373582933257 47053502605723030187199943)
      ·
        refine ⟨70580253908584545280799915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47053502605723030187199943 70580253908584545280799915)
        ·
          refine ⟨105870380862876817921199873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70580253908584545280799915 105870380862876817921199873)
          ·
            refine ⟨79402785647157613440899905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105870380862876817921199873 79402785647157613440899905)
            ·
              refine ⟨59552089235368210080674929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79402785647157613440899905 59552089235368210080674929)
              ·
                refine ⟨44664066926526157560506197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59552089235368210080674929 44664066926526157560506197)
                ·
                  refine ⟨261703517147614204456091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44664066926526157560506197 261703517147614204456091)
                  ·
                    rfl

theorem cell22_2293496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_2293496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293496 prefixEnd_2293496 := by exact prefixLift 2293496
  have htrace : WordTrace (prefixWord ++ tailWord_2293496) baseStart_2293496 baseEnd_2293496 := by
    simpa [prefixWord, tailWord_2293496, baseEnd_2293496] using wordTrace_append hprefix tailTrace_2293496
  have hstable : (prefixWord ++ tailWord_2293496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293496).length < 2 ^ (prefixWord ++ tailWord_2293496).sum := by decide
  have hdescent : baseEnd_2293496 < baseStart_2293496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293510 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2293510 : Nat := 118140960795 + 2293510 * 2 ^ 59
def prefixEnd_2293510 : Nat := 4983230072969 + 3 ^ 40 * 2293510 * 2
def baseEnd_2293510 : Nat := 785115343928951243518231

theorem tailTrace_2293510 : CollatzResearch.WordTrace tailWord_2293510 prefixEnd_2293510 785115343928951243518231 := by
  unfold tailWord_2293510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614099435031638911507937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55767454614008296778835989 2614099435031638911507937)
  ·
    refine ⟨1960574576273729183630953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2614099435031638911507937 1960574576273729183630953)
    ·
      refine ⟨1470430932205296887723215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1960574576273729183630953 1470430932205296887723215)
      ·
        refine ⟨2205646398307945331584823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1470430932205296887723215 2205646398307945331584823)
        ·
          refine ⟨3308469597461917997377235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2205646398307945331584823 3308469597461917997377235)
          ·
            refine ⟨4962704396192876996065853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308469597461917997377235 4962704396192876996065853)
            ·
              refine ⟨1861014148572328873524695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4962704396192876996065853 1861014148572328873524695)
              ·
                refine ⟨2791521222858493310287043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861014148572328873524695 2791521222858493310287043)
                ·
                  refine ⟨4187281834287739965430565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791521222858493310287043 4187281834287739965430565)
                  ·
                    refine ⟨785115343928951243518231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4187281834287739965430565 785115343928951243518231)
                    ·
                      rfl

theorem cell22_2293510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2293510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293510 prefixEnd_2293510 := by exact prefixLift 2293510
  have htrace : WordTrace (prefixWord ++ tailWord_2293510) baseStart_2293510 baseEnd_2293510 := by
    simpa [prefixWord, tailWord_2293510, baseEnd_2293510] using wordTrace_append hprefix tailTrace_2293510
  have hstable : (prefixWord ++ tailWord_2293510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293510).length < 2 ^ (prefixWord ++ tailWord_2293510).sum := by decide
  have hdescent : baseEnd_2293510 < baseStart_2293510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293530 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_2293530 : Nat := 118140960795 + 2293530 * 2 ^ 59
def prefixEnd_2293530 : Nat := 4983230072969 + 3 ^ 40 * 2293530 * 2
def baseEnd_2293530 : Nat := 261707396779225952672723

theorem tailTrace_2293530 : CollatzResearch.WordTrace tailWord_2293530 prefixEnd_2293530 261707396779225952672723 := by
  unfold tailWord_2293530
  simp only [CollatzResearch.WordTrace]
  refine ⟨20912977845234997145995511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55767940920626659055988029 20912977845234997145995511)
  ·
    refine ⟨31369466767852495718993267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20912977845234997145995511 31369466767852495718993267)
    ·
      refine ⟨47054200151778743578489901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31369466767852495718993267 47054200151778743578489901)
      ·
        refine ⟨17645325056917028841933713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47054200151778743578489901 17645325056917028841933713)
        ·
          refine ⟨13233993792687771631450285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17645325056917028841933713 13233993792687771631450285)
          ·
            refine ⟨4962747672257914361793857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13233993792687771631450285 4962747672257914361793857)
            ·
              refine ⟨3722060754193435771345393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4962747672257914361793857 3722060754193435771345393)
              ·
                refine ⟨2791545565645076828509045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722060754193435771345393 2791545565645076828509045)
                ·
                  refine ⟨261707396779225952672723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2791545565645076828509045 261707396779225952672723)
                  ·
                    rfl

theorem cell22_2293530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_2293530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293530 prefixEnd_2293530 := by exact prefixLift 2293530
  have htrace : WordTrace (prefixWord ++ tailWord_2293530) baseStart_2293530 baseEnd_2293530 := by
    simpa [prefixWord, tailWord_2293530, baseEnd_2293530] using wordTrace_append hprefix tailTrace_2293530
  have hstable : (prefixWord ++ tailWord_2293530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293530).length < 2 ^ (prefixWord ++ tailWord_2293530).sum := by decide
  have hdescent : baseEnd_2293530 < baseStart_2293530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293573 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_2293573 : Nat := 118140960795 + 2293573 * 2 ^ 59
def prefixEnd_2293573 : Nat := 4983230072969 + 3 ^ 40 * 2293573 * 2
def baseEnd_2293573 : Nat := 785136910116440079193037

theorem tailTrace_2293573 : CollatzResearch.WordTrace tailWord_2293573 prefixEnd_2293573 785136910116440079193037 := by
  unfold tailWord_2293573
  simp only [CollatzResearch.WordTrace]
  refine ⟨83653479719784206927797373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55768986479856137951864915 83653479719784206927797373)
  ·
    refine ⟨31370054894919077597924015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83653479719784206927797373 31370054894919077597924015)
    ·
      refine ⟨47055082342378616396886023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31370054894919077597924015 47055082342378616396886023)
      ·
        refine ⟨70582623513567924595329035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47055082342378616396886023 70582623513567924595329035)
        ·
          refine ⟨105873935270351886892993553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70582623513567924595329035 105873935270351886892993553)
          ·
            refine ⟨79405451452763915169745165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105873935270351886892993553 79405451452763915169745165)
            ·
              refine ⟨29777044294786468188654437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79405451452763915169745165 29777044294786468188654437)
              ·
                refine ⟨5583195805272462785372707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29777044294786468188654437 5583195805272462785372707)
                ·
                  refine ⟨8374793707908694178059061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5583195805272462785372707 8374793707908694178059061)
                  ·
                    refine ⟨785136910116440079193037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8374793707908694178059061 785136910116440079193037)
                    ·
                      rfl

theorem cell22_2293573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_2293573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293573 prefixEnd_2293573 := by exact prefixLift 2293573
  have htrace : WordTrace (prefixWord ++ tailWord_2293573) baseStart_2293573 baseEnd_2293573 := by
    simpa [prefixWord, tailWord_2293573, baseEnd_2293573] using wordTrace_append hprefix tailTrace_2293573
  have hstable : (prefixWord ++ tailWord_2293573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293573).length < 2 ^ (prefixWord ++ tailWord_2293573).sum := by decide
  have hdescent : baseEnd_2293573 < baseStart_2293573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293575 : List Nat := [1, 1, 4, 1, 2, 1, 3, 5, 4]
def baseStart_2293575 : Nat := 118140960795 + 2293575 * 2 ^ 59
def prefixEnd_2293575 : Nat := 4983230072969 + 3 ^ 40 * 2293575 * 2
def baseEnd_2293575 : Nat := 261712531585770913547677

theorem tailTrace_2293575 : CollatzResearch.WordTrace tailWord_2293575 prefixEnd_2293575 261712531585770913547677 := by
  unfold tailWord_2293575
  simp only [CollatzResearch.WordTrace]
  refine ⟨83653552665776961269370179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55769035110517974179580119 83653552665776961269370179)
  ·
    refine ⟨125480328998665441904055269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83653552665776961269370179 125480328998665441904055269)
    ·
      refine ⟨23527561687249770357010363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125480328998665441904055269 23527561687249770357010363)
      ·
        refine ⟨35291342530874655535515545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23527561687249770357010363 35291342530874655535515545)
        ·
          refine ⟨26468506898155991651636659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35291342530874655535515545 26468506898155991651636659)
          ·
            refine ⟨39702760347233987477454989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26468506898155991651636659 39702760347233987477454989)
            ·
              refine ⟨14888535130212745304045621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39702760347233987477454989 14888535130212745304045621)
              ·
                refine ⟨1395800168457444872254277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14888535130212745304045621 1395800168457444872254277)
                ·
                  refine ⟨261712531585770913547677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1395800168457444872254277 261712531585770913547677)
                  ·
                    rfl

theorem cell22_2293575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 4].length) (baseStart_2293575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293575 prefixEnd_2293575 := by exact prefixLift 2293575
  have htrace : WordTrace (prefixWord ++ tailWord_2293575) baseStart_2293575 baseEnd_2293575 := by
    simpa [prefixWord, tailWord_2293575, baseEnd_2293575] using wordTrace_append hprefix tailTrace_2293575
  have hstable : (prefixWord ++ tailWord_2293575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293575).length < 2 ^ (prefixWord ++ tailWord_2293575).sum := by decide
  have hdescent : baseEnd_2293575 < baseStart_2293575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293618 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_2293618 : Nat := 118140960795 + 2293618 * 2 ^ 59
def prefixEnd_2293618 : Nat := 4983230072969 + 3 ^ 40 * 2293618 * 2
def baseEnd_2293618 : Nat := 785152314536074961817899

theorem tailTrace_2293618 : CollatzResearch.WordTrace tailWord_2293618 prefixEnd_2293618 785152314536074961817899 := by
  unfold tailWord_2293618
  simp only [CollatzResearch.WordTrace]
  refine ⟨20913780251155294903296377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55770080669747453075457005 20913780251155294903296377)
  ·
    refine ⟨15685335188366471177472283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20913780251155294903296377 15685335188366471177472283)
    ·
      refine ⟨23528002782549706766208425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15685335188366471177472283 23528002782549706766208425)
      ·
        refine ⟨17646002086912280074656319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23528002782549706766208425 17646002086912280074656319)
        ·
          refine ⟨26469003130368420111984479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17646002086912280074656319 26469003130368420111984479)
          ·
            refine ⟨39703504695552630167976719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26469003130368420111984479 39703504695552630167976719)
            ·
              refine ⟨59555257043328945251965079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39703504695552630167976719 59555257043328945251965079)
              ·
                refine ⟨89332885564993417877947619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59555257043328945251965079 89332885564993417877947619)
                ·
                  refine ⟨133999328347490126816921429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89332885564993417877947619 133999328347490126816921429)
                  ·
                    refine ⟨785152314536074961817899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 133999328347490126816921429 785152314536074961817899)
                    ·
                      rfl

theorem cell22_2293618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_2293618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293618 prefixEnd_2293618 := by exact prefixLift 2293618
  have htrace : WordTrace (prefixWord ++ tailWord_2293618) baseStart_2293618 baseEnd_2293618 := by
    simpa [prefixWord, tailWord_2293618, baseEnd_2293618] using wordTrace_append hprefix tailTrace_2293618
  have hstable : (prefixWord ++ tailWord_2293618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293618).length < 2 ^ (prefixWord ++ tailWord_2293618).sum := by decide
  have hdescent : baseEnd_2293618 < baseStart_2293618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293710 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_2293710 : Nat := 118140960795 + 2293710 * 2 ^ 59
def prefixEnd_2293710 : Nat := 4983230072969 + 3 ^ 40 * 2293710 * 2
def baseEnd_2293710 : Nat := 261727936005405796172539

theorem tailTrace_2293710 : CollatzResearch.WordTrace tailWord_2293710 prefixEnd_2293710 261727936005405796172539 := by
  unfold tailWord_2293710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10457309565035984915691823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55772317680191919550356389 10457309565035984915691823)
  ·
    refine ⟨15685964347553977373537735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10457309565035984915691823 15685964347553977373537735)
    ·
      refine ⟨23528946521330966060306603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15685964347553977373537735 23528946521330966060306603)
      ·
        refine ⟨35293419781996449090459905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23528946521330966060306603 35293419781996449090459905)
        ·
          refine ⟨26470064836497336817844929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35293419781996449090459905 26470064836497336817844929)
          ·
            refine ⟨19852548627373002613383697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26470064836497336817844929 19852548627373002613383697)
            ·
              refine ⟨14889411470529751960037773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19852548627373002613383697 14889411470529751960037773)
              ·
                refine ⟨5583529301448656985014165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14889411470529751960037773 5583529301448656985014165)
                ·
                  refine ⟨261727936005405796172539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5583529301448656985014165 261727936005405796172539)
                  ·
                    rfl

theorem cell22_2293710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_2293710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293710 prefixEnd_2293710 := by exact prefixLift 2293710
  have htrace : WordTrace (prefixWord ++ tailWord_2293710) baseStart_2293710 baseEnd_2293710 := by
    simpa [prefixWord, tailWord_2293710, baseEnd_2293710] using wordTrace_append hprefix tailTrace_2293710
  have hstable : (prefixWord ++ tailWord_2293710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293710).length < 2 ^ (prefixWord ++ tailWord_2293710).sum := by decide
  have hdescent : baseEnd_2293710 < baseStart_2293710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293742 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2293742 : Nat := 118140960795 + 2293742 * 2 ^ 59
def prefixEnd_2293742 : Nat := 4983230072969 + 3 ^ 40 * 2293742 * 2
def baseEnd_2293742 : Nat := 785194762270179971717519

theorem tailTrace_2293742 : CollatzResearch.WordTrace tailWord_2293742 prefixEnd_2293742 785194762270179971717519 := by
  unfold tailWord_2293742
  simp only [CollatzResearch.WordTrace]
  refine ⟨10457455457021493598837435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55773095770781299193799653 10457455457021493598837435)
  ·
    refine ⟨15686183185532240398256153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10457455457021493598837435 15686183185532240398256153)
    ·
      refine ⟨11764637389149180298692115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15686183185532240398256153 11764637389149180298692115)
      ·
        refine ⟨17646956083723770448038173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11764637389149180298692115 17646956083723770448038173)
        ·
          refine ⟨6617608531396413918014315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17646956083723770448038173 6617608531396413918014315)
          ·
            refine ⟨9926412797094620877021473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6617608531396413918014315 9926412797094620877021473)
            ·
              refine ⟨7444809597820965657766105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9926412797094620877021473 7444809597820965657766105)
              ·
                refine ⟨5583607198365724243324579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7444809597820965657766105 5583607198365724243324579)
                ·
                  refine ⟨8375410797548586364986869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5583607198365724243324579 8375410797548586364986869)
                  ·
                    refine ⟨785194762270179971717519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8375410797548586364986869 785194762270179971717519)
                    ·
                      rfl

theorem cell22_2293742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2293742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293742 prefixEnd_2293742 := by exact prefixLift 2293742
  have htrace : WordTrace (prefixWord ++ tailWord_2293742) baseStart_2293742 baseEnd_2293742 := by
    simpa [prefixWord, tailWord_2293742, baseEnd_2293742] using wordTrace_append hprefix tailTrace_2293742
  have hstable : (prefixWord ++ tailWord_2293742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293742).length < 2 ^ (prefixWord ++ tailWord_2293742).sum := by decide
  have hdescent : baseEnd_2293742 < baseStart_2293742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293789 : List Nat := [1, 4, 2, 2, 2, 3, 2, 6]
def baseStart_2293789 : Nat := 118140960795 + 2293789 * 2 ^ 59
def prefixEnd_2293789 : Nat := 4983230072969 + 3 ^ 40 * 2293789 * 2
def baseEnd_2293789 : Nat := 87245650147854168421375

theorem tailTrace_2293789 : CollatzResearch.WordTrace tailWord_2293789 prefixEnd_2293789 87245650147854168421375 := by
  unfold tailWord_2293789
  simp only [CollatzResearch.WordTrace]
  refine ⟨83661357887001675817660421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55774238591334450545106947 83661357887001675817660421)
  ·
    refine ⟨15686504603812814215811329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83661357887001675817660421 15686504603812814215811329)
    ·
      refine ⟨11764878452859610661858497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15686504603812814215811329 11764878452859610661858497)
      ·
        refine ⟨8823658839644707996393873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11764878452859610661858497 8823658839644707996393873)
        ·
          refine ⟨6617744129733530997295405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8823658839644707996393873 6617744129733530997295405)
          ·
            refine ⟨2481654048650074123985777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6617744129733530997295405 2481654048650074123985777)
            ·
              refine ⟨1861240536487555592989333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2481654048650074123985777 1861240536487555592989333)
              ·
                refine ⟨87245650147854168421375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1861240536487555592989333 87245650147854168421375)
                ·
                  rfl

theorem cell22_2293789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 6].length) (baseStart_2293789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293789 prefixEnd_2293789 := by exact prefixLift 2293789
  have htrace : WordTrace (prefixWord ++ tailWord_2293789) baseStart_2293789 baseEnd_2293789 := by
    simpa [prefixWord, tailWord_2293789, baseEnd_2293789] using wordTrace_append hprefix tailTrace_2293789
  have hstable : (prefixWord ++ tailWord_2293789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293789).length < 2 ^ (prefixWord ++ tailWord_2293789).sum := by decide
  have hdescent : baseEnd_2293789 < baseStart_2293789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293804 : List Nat := [2, 2, 1, 1, 1, 2, 2, 7, 1, 3]
def baseStart_2293804 : Nat := 118140960795 + 2293804 * 2 ^ 59
def prefixEnd_2293804 : Nat := 4983230072969 + 3 ^ 40 * 2293804 * 2
def baseEnd_2293804 : Nat := 785215986137232476667329

theorem tailTrace_2293804 : CollatzResearch.WordTrace tailWord_2293804 prefixEnd_2293804 785215986137232476667329 := by
  unfold tailWord_2293804
  simp only [CollatzResearch.WordTrace]
  refine ⟨41830952490973666689728233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55774603321298222252970977 41830952490973666689728233)
  ·
    refine ⟨31373214368230250017296175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41830952490973666689728233 31373214368230250017296175)
    ·
      refine ⟨47059821552345375025944263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31373214368230250017296175 47059821552345375025944263)
      ·
        refine ⟨70589732328518062538916395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47059821552345375025944263 70589732328518062538916395)
        ·
          refine ⟨105884598492777093808374593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70589732328518062538916395 105884598492777093808374593)
          ·
            refine ⟨79413448869582820356280945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105884598492777093808374593 79413448869582820356280945)
            ·
              refine ⟨59560086652187115267210709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79413448869582820356280945 59560086652187115267210709)
              ·
                refine ⟨1395939530910635514075251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59560086652187115267210709 1395939530910635514075251)
                ·
                  refine ⟨2093909296365953271112877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395939530910635514075251 2093909296365953271112877)
                  ·
                    refine ⟨785215986137232476667329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2093909296365953271112877 785215986137232476667329)
                    ·
                      rfl

theorem cell22_2293804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_2293804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293804 prefixEnd_2293804 := by exact prefixLift 2293804
  have htrace : WordTrace (prefixWord ++ tailWord_2293804) baseStart_2293804 baseEnd_2293804 := by
    simpa [prefixWord, tailWord_2293804, baseEnd_2293804] using wordTrace_append hprefix tailTrace_2293804
  have hstable : (prefixWord ++ tailWord_2293804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293804).length < 2 ^ (prefixWord ++ tailWord_2293804).sum := by decide
  have hdescent : baseEnd_2293804 < baseStart_2293804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293815 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 4, 5]
def baseStart_2293815 : Nat := 118140960795 + 2293815 * 2 ^ 59
def prefixEnd_2293815 : Nat := 4983230072969 + 3 ^ 40 * 2293815 * 2
def baseEnd_2293815 : Nat := 785219751662032114642295

theorem tailTrace_2293815 : CollatzResearch.WordTrace tailWord_2293815 prefixEnd_2293815 785219751662032114642295 := by
  unfold tailWord_2293815
  simp only [CollatzResearch.WordTrace]
  refine ⟨83662306184907482258106899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55774870789938321505404599 83662306184907482258106899)
  ·
    refine ⟨125493459277361223387160349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83662306184907482258106899 125493459277361223387160349)
    ·
      refine ⟨47060047229010458770185131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125493459277361223387160349 47060047229010458770185131)
      ·
        refine ⟨70590070843515688155277697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47060047229010458770185131 70590070843515688155277697)
        ·
          refine ⟨52942553132636766116458273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70590070843515688155277697 52942553132636766116458273)
          ·
            refine ⟨39706914849477574587343705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52942553132636766116458273 39706914849477574587343705)
            ·
              refine ⟨29780186137108180940507779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39706914849477574587343705 29780186137108180940507779)
              ·
                refine ⟨44670279205662271410761669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29780186137108180940507779 44670279205662271410761669)
                ·
                  refine ⟨8375677351061675889517813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44670279205662271410761669 8375677351061675889517813)
                  ·
                    refine ⟨785219751662032114642295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8375677351061675889517813 785219751662032114642295)
                    ·
                      rfl

theorem cell22_2293815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_2293815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293815 prefixEnd_2293815 := by exact prefixLift 2293815
  have htrace : WordTrace (prefixWord ++ tailWord_2293815) baseStart_2293815 baseEnd_2293815 := by
    simpa [prefixWord, tailWord_2293815, baseEnd_2293815] using wordTrace_append hprefix tailTrace_2293815
  have hstable : (prefixWord ++ tailWord_2293815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293815).length < 2 ^ (prefixWord ++ tailWord_2293815).sum := by decide
  have hdescent : baseEnd_2293815 < baseStart_2293815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293879 : List Nat := [1, 1, 3, 1, 1, 6, 1, 4, 4]
def baseStart_2293879 : Nat := 118140960795 + 2293879 * 2 ^ 59
def prefixEnd_2293879 : Nat := 4983230072969 + 3 ^ 40 * 2293879 * 2
def baseEnd_2293879 : Nat := 261747220056652427014033

theorem tailTrace_2293879 : CollatzResearch.WordTrace tailWord_2293879 prefixEnd_2293879 261747220056652427014033 := by
  unfold tailWord_2293879
  simp only [CollatzResearch.WordTrace]
  refine ⟨83664640456675621188436691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55776426971117080792291127 83664640456675621188436691)
  ·
    refine ⟨125496960685013431782655037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83664640456675621188436691 125496960685013431782655037)
    ·
      refine ⟨47061360256880036918495639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125496960685013431782655037 47061360256880036918495639)
      ·
        refine ⟨70592040385320055377743459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47061360256880036918495639 70592040385320055377743459)
        ·
          refine ⟨105888060577980083066615189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70592040385320055377743459 105888060577980083066615189)
          ·
            refine ⟨4963502839592816393747587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105888060577980083066615189 4963502839592816393747587)
            ·
              refine ⟨7445254259389224590621381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4963502839592816393747587 7445254259389224590621381)
              ·
                refine ⟨1395985173635479610741509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7445254259389224590621381 1395985173635479610741509)
                ·
                  refine ⟨261747220056652427014033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1395985173635479610741509 261747220056652427014033)
                  ·
                    rfl

theorem cell22_2293879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 4].length) (baseStart_2293879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293879 prefixEnd_2293879 := by exact prefixLift 2293879
  have htrace : WordTrace (prefixWord ++ tailWord_2293879) baseStart_2293879 baseEnd_2293879 := by
    simpa [prefixWord, tailWord_2293879, baseEnd_2293879] using wordTrace_append hprefix tailTrace_2293879
  have hstable : (prefixWord ++ tailWord_2293879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293879).length < 2 ^ (prefixWord ++ tailWord_2293879).sum := by decide
  have hdescent : baseEnd_2293879 < baseStart_2293879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293892 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_2293892 : Nat := 118140960795 + 2293892 * 2 ^ 59
def prefixEnd_2293892 : Nat := 4983230072969 + 3 ^ 40 * 2293892 * 2
def baseEnd_2293892 : Nat := 785246110335629580467059

theorem tailTrace_2293892 : CollatzResearch.WordTrace tailWord_2293892 prefixEnd_2293892 785246110335629580467059 := by
  unfold tailWord_2293892
  simp only [CollatzResearch.WordTrace]
  refine ⟨41832557302814262204329965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55776743070419016272439953 41832557302814262204329965)
  ·
    refine ⟨15687208988555348326623737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41832557302814262204329965 15687208988555348326623737)
    ·
      refine ⟨11765406741416511244967803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15687208988555348326623737 11765406741416511244967803)
      ·
        refine ⟨17648110112124766867451705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11765406741416511244967803 17648110112124766867451705)
        ·
          refine ⟨13236082584093575150588779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17648110112124766867451705 13236082584093575150588779)
          ·
            refine ⟨19854123876140362725883169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13236082584093575150588779 19854123876140362725883169)
            ·
              refine ⟨14890592907105272044412377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19854123876140362725883169 14890592907105272044412377)
              ·
                refine ⟨11167944680328954033309283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14890592907105272044412377 11167944680328954033309283)
                ·
                  refine ⟨16751917020493431049963925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11167944680328954033309283 16751917020493431049963925)
                  ·
                    refine ⟨785246110335629580467059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16751917020493431049963925 785246110335629580467059)
                    ·
                      rfl

theorem cell22_2293892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_2293892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293892 prefixEnd_2293892 := by exact prefixLift 2293892
  have htrace : WordTrace (prefixWord ++ tailWord_2293892) baseStart_2293892 baseEnd_2293892 := by
    simpa [prefixWord, tailWord_2293892, baseEnd_2293892] using wordTrace_append hprefix tailTrace_2293892
  have hstable : (prefixWord ++ tailWord_2293892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293892).length < 2 ^ (prefixWord ++ tailWord_2293892).sum := by decide
  have hdescent : baseEnd_2293892 < baseStart_2293892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293956 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_2293956 : Nat := 118140960795 + 2293956 * 2 ^ 59
def prefixEnd_2293956 : Nat := 4983230072969 + 3 ^ 40 * 2293956 * 2
def baseEnd_2293956 : Nat := 785268018843554746866863

theorem tailTrace_2293956 : CollatzResearch.WordTrace tailWord_2293956 prefixEnd_2293956 785268018843554746866863 := by
  unfold tailWord_2293956
  simp only [CollatzResearch.WordTrace]
  refine ⟨41833724438698331669494861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55778299251597775559326481 41833724438698331669494861)
  ·
    refine ⟨15687646664511874376060573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41833724438698331669494861 15687646664511874376060573)
    ·
      refine ⟨5882867499191952891022715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15687646664511874376060573 5882867499191952891022715)
      ·
        refine ⟨8824301248787929336534073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5882867499191952891022715 8824301248787929336534073)
        ·
          refine ⟨6618225936590947002400555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8824301248787929336534073 6618225936590947002400555)
          ·
            refine ⟨9927338904886420503600833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618225936590947002400555 9927338904886420503600833)
            ·
              refine ⟨7445504178664815377700625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9927338904886420503600833 7445504178664815377700625)
              ·
                refine ⟨5584128133998611533275469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7445504178664815377700625 5584128133998611533275469)
                ·
                  refine ⟨2094048050249479324978301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5584128133998611533275469 2094048050249479324978301)
                  ·
                    refine ⟨785268018843554746866863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2094048050249479324978301 785268018843554746866863)
                    ·
                      rfl

theorem cell22_2293956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_2293956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2293956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2293956 prefixEnd_2293956 := by exact prefixLift 2293956
  have htrace : WordTrace (prefixWord ++ tailWord_2293956) baseStart_2293956 baseEnd_2293956 := by
    simpa [prefixWord, tailWord_2293956, baseEnd_2293956] using wordTrace_append hprefix tailTrace_2293956
  have hstable : (prefixWord ++ tailWord_2293956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293956).length < 2 ^ (prefixWord ++ tailWord_2293956).sum := by decide
  have hdescent : baseEnd_2293956 < baseStart_2293956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294014 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2294014 : Nat := 118140960795 + 2294014 * 2 ^ 59
def prefixEnd_2294014 : Nat := 4983230072969 + 3 ^ 40 * 2294014 * 2
def baseEnd_2294014 : Nat := 261762624476287309638895

theorem tailTrace_2294014 : CollatzResearch.WordTrace tailWord_2294014 prefixEnd_2294014 261762624476287309638895 := by
  unfold tailWord_2294014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10458695538898317405575137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55779709540791026163067397 10458695538898317405575137)
  ·
    refine ⟨7844021654173738054181353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10458695538898317405575137 7844021654173738054181353)
    ·
      refine ⟨5883016240630303540636015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7844021654173738054181353 5883016240630303540636015)
      ·
        refine ⟨8824524360945455310954023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5883016240630303540636015 8824524360945455310954023)
        ·
          refine ⟨13236786541418182966431035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8824524360945455310954023 13236786541418182966431035)
          ·
            refine ⟨19855179812127274449646553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13236786541418182966431035 19855179812127274449646553)
            ·
              refine ⟨14891384859095455837234915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19855179812127274449646553 14891384859095455837234915)
              ·
                refine ⟨22337077288643183755852373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14891384859095455837234915 22337077288643183755852373)
                ·
                  refine ⟨261762624476287309638895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22337077288643183755852373 261762624476287309638895)
                  ·
                    rfl

theorem cell22_2294014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2294014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294014 prefixEnd_2294014 := by exact prefixLift 2294014
  have htrace : WordTrace (prefixWord ++ tailWord_2294014) baseStart_2294014 baseEnd_2294014 := by
    simpa [prefixWord, tailWord_2294014, baseEnd_2294014] using wordTrace_append hprefix tailTrace_2294014
  have hstable : (prefixWord ++ tailWord_2294014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294014).length < 2 ^ (prefixWord ++ tailWord_2294014).sum := by decide
  have hdescent : baseEnd_2294014 < baseStart_2294014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294042 : List Nat := [3, 1, 1, 3, 14]
def baseStart_2294042 : Nat := 118140960795 + 2294042 * 2 ^ 59
def prefixEnd_2294042 : Nat := 4983230072969 + 3 ^ 40 * 2294042 * 2
def baseEnd_2294042 : Nat := 3231676783543535758093

theorem tailTrace_2294042 : CollatzResearch.WordTrace tailWord_2294042 prefixEnd_2294042 3231676783543535758093 := by
  unfold tailWord_2294042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20917646388771275006655095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55780390370056733351080253 20917646388771275006655095)
  ·
    refine ⟨31376469583156912509982643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20917646388771275006655095 31376469583156912509982643)
    ·
      refine ⟨47064704374735368764973965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31376469583156912509982643 47064704374735368764973965)
      ·
        refine ⟨17649264140525763286865237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47064704374735368764973965 17649264140525763286865237)
        ·
          refine ⟨3231676783543535758093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 17649264140525763286865237 3231676783543535758093)
          ·
            rfl

theorem cell22_2294042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 14].length) (baseStart_2294042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294042 prefixEnd_2294042 := by exact prefixLift 2294042
  have htrace : WordTrace (prefixWord ++ tailWord_2294042) baseStart_2294042 baseEnd_2294042 := by
    simpa [prefixWord, tailWord_2294042, baseEnd_2294042] using wordTrace_append hprefix tailTrace_2294042
  have hstable : (prefixWord ++ tailWord_2294042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294042).length < 2 ^ (prefixWord ++ tailWord_2294042).sum := by decide
  have hdescent : baseEnd_2294042 < baseStart_2294042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294048 : List Nat := [2, 1, 1, 5, 2, 1, 4, 2, 4]
def baseStart_2294048 : Nat := 118140960795 + 2294048 * 2 ^ 59
def prefixEnd_2294048 : Nat := 4983230072969 + 3 ^ 40 * 2294048 * 2
def baseEnd_2294048 : Nat := 261766504107899057855527

theorem tailTrace_2294048 : CollatzResearch.WordTrace tailWord_2294048 prefixEnd_2294048 261766504107899057855527 := by
  unfold tailWord_2294048
  simp only [CollatzResearch.WordTrace]
  refine ⟨41835402196531681525669399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55780536262042242034225865 41835402196531681525669399)
  ·
    refine ⟨62753103294797522288504099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41835402196531681525669399 62753103294797522288504099)
    ·
      refine ⟨94129654942196283432756149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62753103294797522288504099 94129654942196283432756149)
      ·
        refine ⟨8824655150830901571820889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94129654942196283432756149 8824655150830901571820889)
        ·
          refine ⟨6618491363123176178865667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8824655150830901571820889 6618491363123176178865667)
          ·
            refine ⟨9927737044684764268298501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618491363123176178865667 9927737044684764268298501)
            ·
              refine ⟨1861450695878393300305969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9927737044684764268298501 1861450695878393300305969)
              ·
                refine ⟨1396088021908794975229477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1861450695878393300305969 1396088021908794975229477)
                ·
                  refine ⟨261766504107899057855527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1396088021908794975229477 261766504107899057855527)
                  ·
                    rfl

theorem cell22_2294048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 4].length) (baseStart_2294048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294048 prefixEnd_2294048 := by exact prefixLift 2294048
  have htrace : WordTrace (prefixWord ++ tailWord_2294048) baseStart_2294048 baseEnd_2294048 := by
    simpa [prefixWord, tailWord_2294048, baseEnd_2294048] using wordTrace_append hprefix tailTrace_2294048
  have hstable : (prefixWord ++ tailWord_2294048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294048).length < 2 ^ (prefixWord ++ tailWord_2294048).sum := by decide
  have hdescent : baseEnd_2294048 < baseStart_2294048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294078 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_2294078 : Nat := 118140960795 + 2294078 * 2 ^ 59
def prefixEnd_2294078 : Nat := 4983230072969 + 3 ^ 40 * 2294078 * 2
def baseEnd_2294078 : Nat := 785309781936787095316489

theorem tailTrace_2294078 : CollatzResearch.WordTrace tailWord_2294078 prefixEnd_2294078 785309781936787095316489 := by
  unfold tailWord_2294078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10458987322869334771866361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55781265721969785449953925 10458987322869334771866361)
  ·
    refine ⟨7844240492152001078899771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10458987322869334771866361 7844240492152001078899771)
    ·
      refine ⟨11766360738228001618349657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7844240492152001078899771 11766360738228001618349657)
      ·
        refine ⟨8824770553671001213762243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11766360738228001618349657 8824770553671001213762243)
        ·
          refine ⟨13237155830506501820643365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8824770553671001213762243 13237155830506501820643365)
          ·
            refine ⟨2481966718219969091370631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13237155830506501820643365 2481966718219969091370631)
            ·
              refine ⟨3722950077329953637055947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481966718219969091370631 3722950077329953637055947)
              ·
                refine ⟨5584425115994930455583921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3722950077329953637055947 5584425115994930455583921)
                ·
                  refine ⟨4188318836996197841687941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5584425115994930455583921 4188318836996197841687941)
                  ·
                    refine ⟨785309781936787095316489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4188318836996197841687941 785309781936787095316489)
                    ·
                      rfl

theorem cell22_2294078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_2294078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294078 prefixEnd_2294078 := by exact prefixLift 2294078
  have htrace : WordTrace (prefixWord ++ tailWord_2294078) baseStart_2294078 baseEnd_2294078 := by
    simpa [prefixWord, tailWord_2294078, baseEnd_2294078] using wordTrace_append hprefix tailTrace_2294078
  have hstable : (prefixWord ++ tailWord_2294078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294078).length < 2 ^ (prefixWord ++ tailWord_2294078).sum := by decide
  have hdescent : baseEnd_2294078 < baseStart_2294078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294104 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 5]
def baseStart_2294104 : Nat := 118140960795 + 2294104 * 2 ^ 59
def prefixEnd_2294104 : Nat := 4983230072969 + 3 ^ 40 * 2294104 * 2
def baseEnd_2294104 : Nat := 261772894089377231388803

theorem tailTrace_2294104 : CollatzResearch.WordTrace tailWord_2294104 prefixEnd_2294104 261772894089377231388803 := by
  unfold tailWord_2294104
  simp only [CollatzResearch.WordTrace]
  refine ⟨41836423440430242307688683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55781897920573656410251577 41836423440430242307688683)
  ·
    refine ⟨62754635160645363461533025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41836423440430242307688683 62754635160645363461533025)
    ·
      refine ⟨47065976370484022596149769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62754635160645363461533025 47065976370484022596149769)
      ·
        refine ⟨35299482277863016947112327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47065976370484022596149769 35299482277863016947112327)
        ·
          refine ⟨52949223416794525420668491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35299482277863016947112327 52949223416794525420668491)
          ·
            refine ⟨79423835125191788131002737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52949223416794525420668491 79423835125191788131002737)
            ·
              refine ⟨59567876343893841098252053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79423835125191788131002737 59567876343893841098252053)
              ·
                refine ⟨2792244203620023801480565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59567876343893841098252053 2792244203620023801480565)
                ·
                  refine ⟨261772894089377231388803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2792244203620023801480565 261772894089377231388803)
                  ·
                    rfl

theorem cell22_2294104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_2294104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294104 prefixEnd_2294104 := by exact prefixLift 2294104
  have htrace : WordTrace (prefixWord ++ tailWord_2294104) baseStart_2294104 baseEnd_2294104 := by
    simpa [prefixWord, tailWord_2294104, baseEnd_2294104] using wordTrace_append hprefix tailTrace_2294104
  have hstable : (prefixWord ++ tailWord_2294104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294104).length < 2 ^ (prefixWord ++ tailWord_2294104).sum := by decide
  have hdescent : baseEnd_2294104 < baseStart_2294104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294121 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 5]
def baseStart_2294121 : Nat := 118140960795 + 2294121 * 2 ^ 59
def prefixEnd_2294121 : Nat := 4983230072969 + 3 ^ 40 * 2294121 * 2
def baseEnd_2294121 : Nat := 261774833905183105497119

theorem tailTrace_2294121 : CollatzResearch.WordTrace tailWord_2294121 prefixEnd_2294121 261774833905183105497119 := by
  unfold tailWord_2294121
  simp only [CollatzResearch.WordTrace]
  refine ⟨83673466921798896518746217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55782311281199264345830811 83673466921798896518746217)
  ·
    refine ⟨62755100191349172389059663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83673466921798896518746217 62755100191349172389059663)
    ·
      refine ⟨94132650287023758583589495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62755100191349172389059663 94132650287023758583589495)
      ·
        refine ⟨141198975430535637875384243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94132650287023758583589495 141198975430535637875384243)
        ·
          refine ⟨211798463145803456813076365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141198975430535637875384243 211798463145803456813076365)
          ·
            refine ⟨79424423679676296304903637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211798463145803456813076365 79424423679676296304903637)
            ·
              refine ⟨1861509929992413194646179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 79424423679676296304903637 1861509929992413194646179)
              ·
                refine ⟨2792264894988619791969269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861509929992413194646179 2792264894988619791969269)
                ·
                  refine ⟨261774833905183105497119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2792264894988619791969269 261774833905183105497119)
                  ·
                    rfl

theorem cell22_2294121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 5].length) (baseStart_2294121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294121 prefixEnd_2294121 := by exact prefixLift 2294121
  have htrace : WordTrace (prefixWord ++ tailWord_2294121) baseStart_2294121 baseEnd_2294121 := by
    simpa [prefixWord, tailWord_2294121, baseEnd_2294121] using wordTrace_append hprefix tailTrace_2294121
  have hstable : (prefixWord ++ tailWord_2294121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294121).length < 2 ^ (prefixWord ++ tailWord_2294121).sum := by decide
  have hdescent : baseEnd_2294121 < baseStart_2294121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294151 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 1, 4]
def baseStart_2294151 : Nat := 118140960795 + 2294151 * 2 ^ 59
def prefixEnd_2294151 : Nat := 4983230072969 + 3 ^ 40 * 2294151 * 2
def baseEnd_2294151 : Nat := 785334771328639238241265

theorem tailTrace_2294151 : CollatzResearch.WordTrace tailWord_2294151 prefixEnd_2294151 785334771328639238241265 := by
  unfold tailWord_2294151
  simp only [CollatzResearch.WordTrace]
  refine ⟨83674561111690211642338307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55783040741126807761558871 83674561111690211642338307)
  ·
    refine ⟨125511841667535317463507461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83674561111690211642338307 125511841667535317463507461)
    ·
      refine ⟨23533470312662872024407649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125511841667535317463507461 23533470312662872024407649)
      ·
        refine ⟨17650102734497154018305737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23533470312662872024407649 17650102734497154018305737)
        ·
          refine ⟨13237577050872865513729303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17650102734497154018305737 13237577050872865513729303)
          ·
            refine ⟨19856365576309298270593955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13237577050872865513729303 19856365576309298270593955)
            ·
              refine ⟨29784548364463947405890933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19856365576309298270593955 29784548364463947405890933)
              ·
                refine ⟨2792301409168495069302275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29784548364463947405890933 2792301409168495069302275)
                ·
                  refine ⟨4188452113752742603953413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792301409168495069302275 4188452113752742603953413)
                  ·
                    refine ⟨785334771328639238241265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4188452113752742603953413 785334771328639238241265)
                    ·
                      rfl

theorem cell22_2294151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_2294151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294151 prefixEnd_2294151 := by exact prefixLift 2294151
  have htrace : WordTrace (prefixWord ++ tailWord_2294151) baseStart_2294151 baseEnd_2294151 := by
    simpa [prefixWord, tailWord_2294151, baseEnd_2294151] using wordTrace_append hprefix tailTrace_2294151
  have hstable : (prefixWord ++ tailWord_2294151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294151).length < 2 ^ (prefixWord ++ tailWord_2294151).sum := by decide
  have hdescent : baseEnd_2294151 < baseStart_2294151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294194 : List Nat := [3, 2, 1, 1, 1, 1, 3, 10]
def baseStart_2294194 : Nat := 118140960795 + 2294194 * 2 ^ 59
def prefixEnd_2294194 : Nat := 4983230072969 + 3 ^ 40 * 2294194 * 2
def baseEnd_2294194 : Nat := 87261054567489051046237

theorem tailTrace_2294194 : CollatzResearch.WordTrace tailWord_2294194 prefixEnd_2294194 87261054567489051046237 := by
  unfold tailWord_2294194
  simp only [CollatzResearch.WordTrace]
  refine ⟨20919032362633607496538409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55784086300356286657435757 20919032362633607496538409)
  ·
    refine ⟨15689274271975205622403807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20919032362633607496538409 15689274271975205622403807)
    ·
      refine ⟨23533911407962808433605711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15689274271975205622403807 23533911407962808433605711)
      ·
        refine ⟨35300867111944212650408567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23533911407962808433605711 35300867111944212650408567)
        ·
          refine ⟨52951300667916318975612851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35300867111944212650408567 52951300667916318975612851)
          ·
            refine ⟨79426951001874478463419277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52951300667916318975612851 79426951001874478463419277)
            ·
              refine ⟨29785106625702929423782229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79426951001874478463419277 29785106625702929423782229)
              ·
                refine ⟨87261054567489051046237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29785106625702929423782229 87261054567489051046237)
                ·
                  rfl

theorem cell22_2294194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_2294194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294194 prefixEnd_2294194 := by exact prefixLift 2294194
  have htrace : WordTrace (prefixWord ++ tailWord_2294194) baseStart_2294194 baseEnd_2294194 := by
    simpa [prefixWord, tailWord_2294194, baseEnd_2294194] using wordTrace_append hprefix tailTrace_2294194
  have hstable : (prefixWord ++ tailWord_2294194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294194).length < 2 ^ (prefixWord ++ tailWord_2294194).sum := by decide
  have hdescent : baseEnd_2294194 < baseStart_2294194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294228 : List Nat := [2, 4, 1, 2, 2, 3, 1, 7]
def baseStart_2294228 : Nat := 118140960795 + 2294228 * 2 ^ 59
def prefixEnd_2294228 : Nat := 4983230072969 + 3 ^ 40 * 2294228 * 2
def baseEnd_2294228 : Nat := 87262347778026300451781

theorem tailTrace_2294228 : CollatzResearch.WordTrace tailWord_2294228 prefixEnd_2294228 87262347778026300451781 := by
  unfold tailWord_2294228
  simp only [CollatzResearch.WordTrace]
  refine ⟨41838684766205626896445669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55784913021607502528594225 41838684766205626896445669)
  ·
    refine ⟨7844753393663555043083563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41838684766205626896445669 7844753393663555043083563)
    ·
      refine ⟨11767130090495332564625345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7844753393663555043083563 11767130090495332564625345)
      ·
        refine ⟨8825347567871499423469009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11767130090495332564625345 8825347567871499423469009)
        ·
          refine ⟨6619010675903624567601757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8825347567871499423469009 6619010675903624567601757)
          ·
            refine ⟨2482129003463859212850659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6619010675903624567601757 2482129003463859212850659)
            ·
              refine ⟨3723193505195788819275989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2482129003463859212850659 3723193505195788819275989)
              ·
                refine ⟨87262347778026300451781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3723193505195788819275989 87262347778026300451781)
                ·
                  rfl

theorem cell22_2294228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 7].length) (baseStart_2294228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294228 prefixEnd_2294228 := by exact prefixLift 2294228
  have htrace : WordTrace (prefixWord ++ tailWord_2294228) baseStart_2294228 baseEnd_2294228 := by
    simpa [prefixWord, tailWord_2294228, baseEnd_2294228] using wordTrace_append hprefix tailTrace_2294228
  have hstable : (prefixWord ++ tailWord_2294228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294228).length < 2 ^ (prefixWord ++ tailWord_2294228).sum := by decide
  have hdescent : baseEnd_2294228 < baseStart_2294228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294273 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 5]
def baseStart_2294273 : Nat := 118140960795 + 2294273 * 2 ^ 59
def prefixEnd_2294273 : Nat := 4983230072969 + 3 ^ 40 * 2294273 * 2
def baseEnd_2294273 : Nat := 261792178140623862230297

theorem tailTrace_2294273 : CollatzResearch.WordTrace tailWord_2294273 prefixEnd_2294273 261792178140623862230297 := by
  unfold tailWord_2294273
  simp only [CollatzResearch.WordTrace]
  refine ⟨83679010817248226478279473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55786007211498817652186315 83679010817248226478279473)
  ·
    refine ⟨62759258112936169858709605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83679010817248226478279473 62759258112936169858709605)
    ·
      refine ⟨11767360896175531848508051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62759258112936169858709605 11767360896175531848508051)
      ·
        refine ⟨17651041344263297772762077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11767360896175531848508051 17651041344263297772762077)
        ·
          refine ⟨6619140504098736664785779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17651041344263297772762077 6619140504098736664785779)
          ·
            refine ⟨9928710756148104997178669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6619140504098736664785779 9928710756148104997178669)
            ·
              refine ⟨3723266533555539373942001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9928710756148104997178669 3723266533555539373942001)
              ·
                refine ⟨2792449900166654530456501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3723266533555539373942001 2792449900166654530456501)
                ·
                  refine ⟨261792178140623862230297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2792449900166654530456501 261792178140623862230297)
                  ·
                    rfl

theorem cell22_2294273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_2294273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294273 prefixEnd_2294273 := by exact prefixLift 2294273
  have htrace : WordTrace (prefixWord ++ tailWord_2294273) baseStart_2294273 baseEnd_2294273 := by
    simpa [prefixWord, tailWord_2294273, baseEnd_2294273] using wordTrace_append hprefix tailTrace_2294273
  have hstable : (prefixWord ++ tailWord_2294273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294273).length < 2 ^ (prefixWord ++ tailWord_2294273).sum := by decide
  have hdescent : baseEnd_2294273 < baseStart_2294273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294311 : List Nat := [1, 1, 7, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2294311 : Nat := 118140960795 + 2294311 * 2 ^ 59
def prefixEnd_2294311 : Nat := 4983230072969 + 3 ^ 40 * 2294311 * 2
def baseEnd_2294311 : Nat := 785389542598452154240775

theorem tailTrace_2294311 : CollatzResearch.WordTrace tailWord_2294311 prefixEnd_2294311 785389542598452154240775 := by
  unfold tailWord_2294311
  simp only [CollatzResearch.WordTrace]
  refine ⟨83680396791110558968162787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55786931194073705978775191 83680396791110558968162787)
  ·
    refine ⟨125520595186665838452244181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83680396791110558968162787 125520595186665838452244181)
    ·
      refine ⟨2941888949687480588724473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 125520595186665838452244181 2941888949687480588724473)
      ·
        refine ⟨2206416712265610441543355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2941888949687480588724473 2206416712265610441543355)
        ·
          refine ⟨3309625068398415662315033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206416712265610441543355 3309625068398415662315033)
          ·
            refine ⟨2482218801298811746736275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3309625068398415662315033 2482218801298811746736275)
            ·
              refine ⟨3723328201948217620104413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2482218801298811746736275 3723328201948217620104413)
              ·
                refine ⟨1396248075730581607539155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3723328201948217620104413 1396248075730581607539155)
                ·
                  refine ⟨2094372113595872411308733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396248075730581607539155 2094372113595872411308733)
                  ·
                    refine ⟨785389542598452154240775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2094372113595872411308733 785389542598452154240775)
                    ·
                      rfl

theorem cell22_2294311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2294311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294311 prefixEnd_2294311 := by exact prefixLift 2294311
  have htrace : WordTrace (prefixWord ++ tailWord_2294311) baseStart_2294311 baseEnd_2294311 := by
    simpa [prefixWord, tailWord_2294311, baseEnd_2294311] using wordTrace_append hprefix tailTrace_2294311
  have hstable : (prefixWord ++ tailWord_2294311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294311).length < 2 ^ (prefixWord ++ tailWord_2294311).sum := by decide
  have hdescent : baseEnd_2294311 < baseStart_2294311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294316 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_2294316 : Nat := 118140960795 + 2294316 * 2 ^ 59
def prefixEnd_2294316 : Nat := 4983230072969 + 3 ^ 40 * 2294316 * 2
def baseEnd_2294316 : Nat := 785391254200633807865759

theorem tailTrace_2294316 : CollatzResearch.WordTrace tailWord_2294316 prefixEnd_2294316 785391254200633807865759 := by
  unfold tailWord_2294316
  simp only [CollatzResearch.WordTrace]
  refine ⟨41840289578046222411047401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55787052770728296548063201 41840289578046222411047401)
  ·
    refine ⟨31380217183534666808285551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41840289578046222411047401 31380217183534666808285551)
    ·
      refine ⟨47070325775302000212428327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31380217183534666808285551 47070325775302000212428327)
      ·
        refine ⟨70605488662953000318642491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47070325775302000212428327 70605488662953000318642491)
        ·
          refine ⟨105908232994429500477963737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70605488662953000318642491 105908232994429500477963737)
          ·
            refine ⟨79431174745822125358472803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105908232994429500477963737 79431174745822125358472803)
            ·
              refine ⟨119146762118733188037709205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79431174745822125358472803 119146762118733188037709205)
              ·
                refine ⟨5585004474315618189267619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119146762118733188037709205 5585004474315618189267619)
                ·
                  refine ⟨8377506711473427283901429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5585004474315618189267619 8377506711473427283901429)
                  ·
                    refine ⟨785391254200633807865759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8377506711473427283901429 785391254200633807865759)
                    ·
                      rfl

theorem cell22_2294316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_2294316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294316 prefixEnd_2294316 := by exact prefixLift 2294316
  have htrace : WordTrace (prefixWord ++ tailWord_2294316) baseStart_2294316 baseEnd_2294316 := by
    simpa [prefixWord, tailWord_2294316, baseEnd_2294316] using wordTrace_append hprefix tailTrace_2294316
  have hstable : (prefixWord ++ tailWord_2294316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294316).length < 2 ^ (prefixWord ++ tailWord_2294316).sum := by decide
  have hdescent : baseEnd_2294316 < baseStart_2294316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294335 : List Nat := [1, 1, 2, 2, 3, 2, 5, 2, 4]
def baseStart_2294335 : Nat := 118140960795 + 2294335 * 2 ^ 59
def prefixEnd_2294335 : Nat := 4983230072969 + 3 ^ 40 * 2294335 * 2
def baseEnd_2294335 : Nat := 261799252762974697213567

theorem tailTrace_2294335 : CollatzResearch.WordTrace tailWord_2294335 prefixEnd_2294335 261799252762974697213567 := by
  unfold tailWord_2294335
  simp only [CollatzResearch.WordTrace]
  refine ⟨83681272143023611067036459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55787514762015740711357639 83681272143023611067036459)
  ·
    refine ⟨125521908214535416600554689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83681272143023611067036459 125521908214535416600554689)
    ·
      refine ⟨94141431160901562450416017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125521908214535416600554689 94141431160901562450416017)
      ·
        refine ⟨70606073370676171837812013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94141431160901562450416017 70606073370676171837812013)
        ·
          refine ⟨26477277514003564439179505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70606073370676171837812013 26477277514003564439179505)
          ·
            refine ⟨19857958135502673329384629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26477277514003564439179505 19857958135502673329384629)
            ·
              refine ⟨1861683575203375624629809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19857958135502673329384629 1861683575203375624629809)
              ·
                refine ⟨1396262681402531718472357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1861683575203375624629809 1396262681402531718472357)
                ·
                  refine ⟨261799252762974697213567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1396262681402531718472357 261799252762974697213567)
                  ·
                    rfl

theorem cell22_2294335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 4].length) (baseStart_2294335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294335 prefixEnd_2294335 := by exact prefixLift 2294335
  have htrace : WordTrace (prefixWord ++ tailWord_2294335) baseStart_2294335 baseEnd_2294335 := by
    simpa [prefixWord, tailWord_2294335, baseEnd_2294335] using wordTrace_append hprefix tailTrace_2294335
  have hstable : (prefixWord ++ tailWord_2294335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294335).length < 2 ^ (prefixWord ++ tailWord_2294335).sum := by decide
  have hdescent : baseEnd_2294335 < baseStart_2294335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294346 : List Nat := [3, 1, 2, 1, 1, 4, 1, 9]
def baseStart_2294346 : Nat := 118140960795 + 2294346 * 2 ^ 59
def prefixEnd_2294346 : Nat := 4983230072969 + 3 ^ 40 * 2294346 * 2
def baseEnd_2294346 : Nat := 87266835979302636623963

theorem tailTrace_2294346 : CollatzResearch.WordTrace tailWord_2294346 prefixEnd_2294346 87266835979302636623963 := by
  unfold tailWord_2294346
  simp only [CollatzResearch.WordTrace]
  refine ⟨20920418336495939986421723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55787782230655839963791261 20920418336495939986421723)
  ·
    refine ⟨31380627504743909979632585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20920418336495939986421723 31380627504743909979632585)
    ·
      refine ⟨23535470628557932484724439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31380627504743909979632585 23535470628557932484724439)
      ·
        refine ⟨35303205942836898727086659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23535470628557932484724439 35303205942836898727086659)
        ·
          refine ⟨52954808914255348090629989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35303205942836898727086659 52954808914255348090629989)
          ·
            refine ⟨9929026671422877766993123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52954808914255348090629989 9929026671422877766993123)
            ·
              refine ⟨14893540007134316650489685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9929026671422877766993123 14893540007134316650489685)
              ·
                refine ⟨87266835979302636623963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14893540007134316650489685 87266835979302636623963)
                ·
                  rfl

theorem cell22_2294346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_2294346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294346 prefixEnd_2294346 := by exact prefixLift 2294346
  have htrace : WordTrace (prefixWord ++ tailWord_2294346) baseStart_2294346 baseEnd_2294346 := by
    simpa [prefixWord, tailWord_2294346, baseEnd_2294346] using wordTrace_append hprefix tailTrace_2294346
  have hstable : (prefixWord ++ tailWord_2294346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294346).length < 2 ^ (prefixWord ++ tailWord_2294346).sum := by decide
  have hdescent : baseEnd_2294346 < baseStart_2294346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294391 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 7]
def baseStart_2294391 : Nat := 118140960795 + 2294391 * 2 ^ 59
def prefixEnd_2294391 : Nat := 4983230072969 + 3 ^ 40 * 2294391 * 2
def baseEnd_2294391 : Nat := 261805642744452870746843

theorem tailTrace_2294391 : CollatzResearch.WordTrace tailWord_2294391 prefixEnd_2294391 261805642744452870746843 := by
  unfold tailWord_2294391
  simp only [CollatzResearch.WordTrace]
  refine ⟨83683314630820732631075027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55788876420547155087383351 83683314630820732631075027)
  ·
    refine ⟨125524971946231098946612541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83683314630820732631075027 125524971946231098946612541)
    ·
      refine ⟨47071864479836662104979703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125524971946231098946612541 47071864479836662104979703)
      ·
        refine ⟨70607796719754993157469555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47071864479836662104979703 70607796719754993157469555)
        ·
          refine ⟨105911695079632489736204333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70607796719754993157469555 105911695079632489736204333)
          ·
            refine ⟨39716885654862183651076625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105911695079632489736204333 39716885654862183651076625)
            ·
              refine ⟨29787664241146637738307469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39716885654862183651076625 29787664241146637738307469)
              ·
                refine ⟨11170374090429989151865301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29787664241146637738307469 11170374090429989151865301)
                ·
                  refine ⟨261805642744452870746843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11170374090429989151865301 261805642744452870746843)
                  ·
                    rfl

theorem cell22_2294391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 7].length) (baseStart_2294391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294391 prefixEnd_2294391 := by exact prefixLift 2294391
  have htrace : WordTrace (prefixWord ++ tailWord_2294391) baseStart_2294391 baseEnd_2294391 := by
    simpa [prefixWord, tailWord_2294391, baseEnd_2294391] using wordTrace_append hprefix tailTrace_2294391
  have hstable : (prefixWord ++ tailWord_2294391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294391).length < 2 ^ (prefixWord ++ tailWord_2294391).sum := by decide
  have hdescent : baseEnd_2294391 < baseStart_2294391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294442 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_2294442 : Nat := 118140960795 + 2294442 * 2 ^ 59
def prefixEnd_2294442 : Nat := 4983230072969 + 3 ^ 40 * 2294442 * 2
def baseEnd_2294442 : Nat := 261811462191870493071791

theorem tailTrace_2294442 : CollatzResearch.WordTrace tailWord_2294442 prefixEnd_2294442 261811462191870493071791 := by
  unfold tailWord_2294442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20921293688408992085295395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55790116502423978894121053 20921293688408992085295395)
  ·
    refine ⟨31381940532613488127943093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20921293688408992085295395 31381940532613488127943093)
    ·
      refine ⟨2942056924932514511994665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31381940532613488127943093 2942056924932514511994665)
      ·
        refine ⟨2206542693699385883995999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2942056924932514511994665 2206542693699385883995999)
        ·
          refine ⟨3309814040549078825993999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206542693699385883995999 3309814040549078825993999)
          ·
            refine ⟨4964721060823618238990999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3309814040549078825993999 4964721060823618238990999)
            ·
              refine ⟨7447081591235427358486499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964721060823618238990999 7447081591235427358486499)
              ·
                refine ⟨11170622386853141037729749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7447081591235427358486499 11170622386853141037729749)
                ·
                  refine ⟨261811462191870493071791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11170622386853141037729749 261811462191870493071791)
                  ·
                    rfl

theorem cell22_2294442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_2294442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294442 prefixEnd_2294442 := by exact prefixLift 2294442
  have htrace : WordTrace (prefixWord ++ tailWord_2294442) baseStart_2294442 baseEnd_2294442 := by
    simpa [prefixWord, tailWord_2294442, baseEnd_2294442] using wordTrace_append hprefix tailTrace_2294442
  have hstable : (prefixWord ++ tailWord_2294442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294442).length < 2 ^ (prefixWord ++ tailWord_2294442).sum := by decide
  have hdescent : baseEnd_2294442 < baseStart_2294442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294487 : List Nat := [1, 1, 3, 2, 1, 6, 1, 3, 4]
def baseStart_2294487 : Nat := 118140960795 + 2294487 * 2 ^ 59
def prefixEnd_2294487 : Nat := 4983230072969 + 3 ^ 40 * 2294487 * 2
def baseEnd_2294487 : Nat := 261816596998415453946745

theorem tailTrace_2294487 : CollatzResearch.WordTrace tailWord_2294487 prefixEnd_2294487 261816596998415453946745 := by
  unfold tailWord_2294487
  simp only [CollatzResearch.WordTrace]
  refine ⟨83686816038472941026569715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55791210692315294017713143 83686816038472941026569715)
  ·
    refine ⟨125530224057709411539854573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83686816038472941026569715 125530224057709411539854573)
    ·
      refine ⟨47073834021641029327445465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125530224057709411539854573 47073834021641029327445465)
      ·
        refine ⟨35305375516230771995584099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47073834021641029327445465 35305375516230771995584099)
        ·
          refine ⟨52958063274346157993376149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35305375516230771995584099 52958063274346157993376149)
          ·
            refine ⟨2482409215984976155939507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52958063274346157993376149 2482409215984976155939507)
            ·
              refine ⟨3723613823977464233909261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2482409215984976155939507 3723613823977464233909261)
              ·
                refine ⟨1396355183991549087715973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3723613823977464233909261 1396355183991549087715973)
                ·
                  refine ⟨261816596998415453946745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1396355183991549087715973 261816596998415453946745)
                  ·
                    rfl

theorem cell22_2294487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 4].length) (baseStart_2294487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294487 prefixEnd_2294487 := by exact prefixLift 2294487
  have htrace : WordTrace (prefixWord ++ tailWord_2294487) baseStart_2294487 baseEnd_2294487 := by
    simpa [prefixWord, tailWord_2294487, baseEnd_2294487] using wordTrace_append hprefix tailTrace_2294487
  have hstable : (prefixWord ++ tailWord_2294487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294487).length < 2 ^ (prefixWord ++ tailWord_2294487).sum := by decide
  have hdescent : baseEnd_2294487 < baseStart_2294487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294500 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_2294500 : Nat := 118140960795 + 2294500 * 2 ^ 59
def prefixEnd_2294500 : Nat := 4983230072969 + 3 ^ 40 * 2294500 * 2
def baseEnd_2294500 : Nat := 785454241160918661265195

theorem tailTrace_2294500 : CollatzResearch.WordTrace tailWord_2294500 prefixEnd_2294500 785454241160918661265195 := by
  unfold tailWord_2294500
  simp only [CollatzResearch.WordTrace]
  refine ⟨41843645093712922123396477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55791526791617229497861969 41843645093712922123396477)
  ·
    refine ⟨15691366910142345796273679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41843645093712922123396477 15691366910142345796273679)
    ·
      refine ⟨23537050365213518694410519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15691366910142345796273679 23537050365213518694410519)
      ·
        refine ⟨35305575547820278041615779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23537050365213518694410519 35305575547820278041615779)
        ·
          refine ⟨52958363321730417062423669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35305575547820278041615779 52958363321730417062423669)
          ·
            refine ⟨4964846561412226599602219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52958363321730417062423669 4964846561412226599602219)
            ·
              refine ⟨7447269842118339899403329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964846561412226599602219 7447269842118339899403329)
              ·
                refine ⟨5585452381588754924552497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7447269842118339899403329 5585452381588754924552497)
                ·
                  refine ⟨4189089286191566193414373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5585452381588754924552497 4189089286191566193414373)
                  ·
                    refine ⟨785454241160918661265195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4189089286191566193414373 785454241160918661265195)
                    ·
                      rfl

theorem cell22_2294500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_2294500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294500 prefixEnd_2294500 := by exact prefixLift 2294500
  have htrace : WordTrace (prefixWord ++ tailWord_2294500) baseStart_2294500 baseEnd_2294500 := by
    simpa [prefixWord, tailWord_2294500, baseEnd_2294500] using wordTrace_append hprefix tailTrace_2294500
  have hstable : (prefixWord ++ tailWord_2294500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294500).length < 2 ^ (prefixWord ++ tailWord_2294500).sum := by decide
  have hdescent : baseEnd_2294500 < baseStart_2294500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294504 : List Nat := [2, 1, 4, 1, 4, 1, 3, 2, 4]
def baseStart_2294504 : Nat := 118140960795 + 2294504 * 2 ^ 59
def prefixEnd_2294504 : Nat := 4983230072969 + 3 ^ 40 * 2294504 * 2
def baseEnd_2294504 : Nat := 261818536814221328055061

theorem tailTrace_2294504 : CollatzResearch.WordTrace tailWord_2294504 prefixEnd_2294504 261818536814221328055061 := by
  unfold tailWord_2294504
  simp only [CollatzResearch.WordTrace]
  refine ⟨41843718039705676464969283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55791624052940901953292377 41843718039705676464969283)
  ·
    refine ⟨62765577059558514697453925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41843718039705676464969283 62765577059558514697453925)
    ·
      refine ⟨11768545698667221505772611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62765577059558514697453925 11768545698667221505772611)
      ·
        refine ⟨17652818548000832258658917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11768545698667221505772611 17652818548000832258658917)
        ·
          refine ⟨3309903477750156048498547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17652818548000832258658917 3309903477750156048498547)
          ·
            refine ⟨4964855216625234072747821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3309903477750156048498547 4964855216625234072747821)
            ·
              refine ⟨1861820706234462777280433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4964855216625234072747821 1861820706234462777280433)
              ·
                refine ⟨1396365529675847082960325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1861820706234462777280433 1396365529675847082960325)
                ·
                  refine ⟨261818536814221328055061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1396365529675847082960325 261818536814221328055061)
                  ·
                    rfl

theorem cell22_2294504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 4].length) (baseStart_2294504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294504 prefixEnd_2294504 := by exact prefixLift 2294504
  have htrace : WordTrace (prefixWord ++ tailWord_2294504) baseStart_2294504 baseEnd_2294504 := by
    simpa [prefixWord, tailWord_2294504, baseEnd_2294504] using wordTrace_append hprefix tailTrace_2294504
  have hstable : (prefixWord ++ tailWord_2294504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294504).length < 2 ^ (prefixWord ++ tailWord_2294504).sum := by decide
  have hdescent : baseEnd_2294504 < baseStart_2294504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294547 : List Nat := [1, 1, 1, 2, 1, 3, 4, 5, 1, 3]
def baseStart_2294547 : Nat := 118140960795 + 2294547 * 2 ^ 59
def prefixEnd_2294547 : Nat := 4983230072969 + 3 ^ 40 * 2294547 * 2
def baseEnd_2294547 : Nat := 785470330221426205340051

theorem tailTrace_2294547 : CollatzResearch.WordTrace tailWord_2294547 prefixEnd_2294547 785470330221426205340051 := by
  unfold tailWord_2294547
  simp only [CollatzResearch.WordTrace]
  refine ⟨83689004418255571273753895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55792669612170380849169263 83689004418255571273753895)
  ·
    refine ⟨125533506627383356910630843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83689004418255571273753895 125533506627383356910630843)
    ·
      refine ⟨188300259941075035365946265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125533506627383356910630843 188300259941075035365946265)
      ·
        refine ⟨141225194955806276524459699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188300259941075035365946265 141225194955806276524459699)
        ·
          refine ⟨211837792433709414786689549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141225194955806276524459699 211837792433709414786689549)
          ·
            refine ⟨79439172162641030545008581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211837792433709414786689549 79439172162641030545008581)
            ·
              refine ⟨14894844780495193227189109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79439172162641030545008581 14894844780495193227189109)
              ·
                refine ⟨1396391698171424365048979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14894844780495193227189109 1396391698171424365048979)
                ·
                  refine ⟨2094587547257136547573469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396391698171424365048979 2094587547257136547573469)
                  ·
                    refine ⟨785470330221426205340051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2094587547257136547573469 785470330221426205340051)
                    ·
                      rfl

theorem cell22_2294547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 1, 3].length) (baseStart_2294547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294547 prefixEnd_2294547 := by exact prefixLift 2294547
  have htrace : WordTrace (prefixWord ++ tailWord_2294547) baseStart_2294547 baseEnd_2294547 := by
    simpa [prefixWord, tailWord_2294547, baseEnd_2294547] using wordTrace_append hprefix tailTrace_2294547
  have hstable : (prefixWord ++ tailWord_2294547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294547).length < 2 ^ (prefixWord ++ tailWord_2294547).sum := by decide
  have hdescent : baseEnd_2294547 < baseStart_2294547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294560 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 5]
def baseStart_2294560 : Nat := 118140960795 + 2294560 * 2 ^ 59
def prefixEnd_2294560 : Nat := 4983230072969 + 3 ^ 40 * 2294560 * 2
def baseEnd_2294560 : Nat := 261824926795699501588337

theorem tailTrace_2294560 : CollatzResearch.WordTrace tailWord_2294560 prefixEnd_2294560 261824926795699501588337 := by
  unfold tailWord_2294560
  simp only [CollatzResearch.WordTrace]
  refine ⟨41844739283604237246988567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55792985711472316329318089 41844739283604237246988567)
  ·
    refine ⟨62767108925406355870482851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41844739283604237246988567 62767108925406355870482851)
    ·
      refine ⟨94150663388109533805724277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62767108925406355870482851 94150663388109533805724277)
      ·
        refine ⟨8826624692635268794286651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94150663388109533805724277 8826624692635268794286651)
        ·
          refine ⟨13239937038952903191429977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8826624692635268794286651 13239937038952903191429977)
          ·
            refine ⟨9929952779214677393572483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13239937038952903191429977 9929952779214677393572483)
            ·
              refine ⟨14894929168822016090358725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9929952779214677393572483 14894929168822016090358725)
              ·
                refine ⟨2792799219154128016942261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14894929168822016090358725 2792799219154128016942261)
                ·
                  refine ⟨261824926795699501588337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2792799219154128016942261 261824926795699501588337)
                  ·
                    rfl

theorem cell22_2294560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_2294560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294560 prefixEnd_2294560 := by exact prefixLift 2294560
  have htrace : WordTrace (prefixWord ++ tailWord_2294560) baseStart_2294560 baseEnd_2294560 := by
    simpa [prefixWord, tailWord_2294560, baseEnd_2294560] using wordTrace_append hprefix tailTrace_2294560
  have hstable : (prefixWord ++ tailWord_2294560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294560).length < 2 ^ (prefixWord ++ tailWord_2294560).sum := by decide
  have hdescent : baseEnd_2294560 < baseStart_2294560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294800 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_2294800 : Nat := 118140960795 + 2294800 * 2 ^ 59
def prefixEnd_2294800 : Nat := 4983230072969 + 3 ^ 40 * 2294800 * 2
def baseEnd_2294800 : Nat := 785556937291817878764275

theorem tailTrace_2294800 : CollatzResearch.WordTrace tailWord_2294800 prefixEnd_2294800 785556937291817878764275 := by
  unfold tailWord_2294800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41849116043169497741356927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55798821390892663655142569 41849116043169497741356927)
  ·
    refine ⟨62773674064754246612035391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41849116043169497741356927 62773674064754246612035391)
    ·
      refine ⟨94160511097131369918053087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62773674064754246612035391 94160511097131369918053087)
      ·
        refine ⟨141240766645697054877079631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94160511097131369918053087 141240766645697054877079631)
        ·
          refine ⟨211861149968545582315619447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141240766645697054877079631 211861149968545582315619447)
          ·
            refine ⟨317791724952818373473429171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211861149968545582315619447 317791724952818373473429171)
            ·
              refine ⟨476687587429227560210143757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317791724952818373473429171 476687587429227560210143757)
              ·
                refine ⟨178757845285960335078803909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 476687587429227560210143757 178757845285960335078803909)
                ·
                  refine ⟨33517095991117562827275733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178757845285960335078803909 33517095991117562827275733)
                  ·
                    refine ⟨785556937291817878764275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33517095991117562827275733 785556937291817878764275)
                    ·
                      rfl

theorem cell22_2294800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_2294800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294800 prefixEnd_2294800 := by exact prefixLift 2294800
  have htrace : WordTrace (prefixWord ++ tailWord_2294800) baseStart_2294800 baseEnd_2294800 := by
    simpa [prefixWord, tailWord_2294800, baseEnd_2294800] using wordTrace_append hprefix tailTrace_2294800
  have hstable : (prefixWord ++ tailWord_2294800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294800).length < 2 ^ (prefixWord ++ tailWord_2294800).sum := by decide
  have hdescent : baseEnd_2294800 < baseStart_2294800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294819 : List Nat := [1, 1, 1, 4, 3, 4, 2, 6]
def baseStart_2294819 : Nat := 118140960795 + 2294819 * 2 ^ 59
def prefixEnd_2294819 : Nat := 4983230072969 + 3 ^ 40 * 2294819 * 2
def baseEnd_2294819 : Nat := 87284826820012018059913

theorem tailTrace_2294819 : CollatzResearch.WordTrace tailWord_2294819 prefixEnd_2294819 87284826820012018059913 := by
  unfold tailWord_2294819
  simp only [CollatzResearch.WordTrace]
  refine ⟨83698925073270161727655511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55799283382180107818437007 83698925073270161727655511)
  ·
    refine ⟨125548387609905242591483267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83698925073270161727655511 125548387609905242591483267)
    ·
      refine ⟨188322581414857863887224901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125548387609905242591483267 188322581414857863887224901)
      ·
        refine ⟨35310484015285849478854669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188322581414857863887224901 35310484015285849478854669)
        ·
          refine ⟨13241431505732193554570501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35310484015285849478854669 13241431505732193554570501)
          ·
            refine ⟨2482768407324786291481969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13241431505732193554570501 2482768407324786291481969)
            ·
              refine ⟨1862076305493589718611477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2482768407324786291481969 1862076305493589718611477)
              ·
                refine ⟨87284826820012018059913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1862076305493589718611477 87284826820012018059913)
                ·
                  rfl

theorem cell22_2294819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 6].length) (baseStart_2294819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294819 prefixEnd_2294819 := by exact prefixLift 2294819
  have htrace : WordTrace (prefixWord ++ tailWord_2294819) baseStart_2294819 baseEnd_2294819 := by
    simpa [prefixWord, tailWord_2294819, baseEnd_2294819] using wordTrace_append hprefix tailTrace_2294819
  have hstable : (prefixWord ++ tailWord_2294819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294819).length < 2 ^ (prefixWord ++ tailWord_2294819).sum := by decide
  have hdescent : baseEnd_2294819 < baseStart_2294819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294847 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 5]
def baseStart_2294847 : Nat := 118140960795 + 2294847 * 2 ^ 59
def prefixEnd_2294847 : Nat := 4983230072969 + 3 ^ 40 * 2294847 * 2
def baseEnd_2294847 : Nat := 261857675450775140946377

theorem tailTrace_2294847 : CollatzResearch.WordTrace tailWord_2294847 prefixEnd_2294847 261857675450775140946377 := by
  unfold tailWord_2294847
  simp only [CollatzResearch.WordTrace]
  refine ⟨83699946317168722509674795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55799964211445815006449863 83699946317168722509674795)
  ·
    refine ⟨125549919475753083764512193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83699946317168722509674795 125549919475753083764512193)
    ·
      refine ⟨94162439606814812823384145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125549919475753083764512193 94162439606814812823384145)
      ·
        refine ⟨70621829705111109617538109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94162439606814812823384145 70621829705111109617538109)
        ·
          refine ⟨26483186139416666106576791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70621829705111109617538109 26483186139416666106576791)
          ·
            refine ⟨39724779209124999159865187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26483186139416666106576791 39724779209124999159865187)
            ·
              refine ⟨59587168813687498739797781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39724779209124999159865187 59587168813687498739797781)
              ·
                refine ⟨2793148538141601503428021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59587168813687498739797781 2793148538141601503428021)
                ·
                  refine ⟨261857675450775140946377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2793148538141601503428021 261857675450775140946377)
                  ·
                    rfl

theorem cell22_2294847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 5].length) (baseStart_2294847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294847 prefixEnd_2294847 := by exact prefixLift 2294847
  have htrace : WordTrace (prefixWord ++ tailWord_2294847) baseStart_2294847 baseEnd_2294847 := by
    simpa [prefixWord, tailWord_2294847, baseEnd_2294847] using wordTrace_append hprefix tailTrace_2294847
  have hstable : (prefixWord ++ tailWord_2294847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294847).length < 2 ^ (prefixWord ++ tailWord_2294847).sum := by decide
  have hdescent : baseEnd_2294847 < baseStart_2294847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294862 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2294862 : Nat := 118140960795 + 2294862 * 2 ^ 59
def prefixEnd_2294862 : Nat := 4983230072969 + 3 ^ 40 * 2294862 * 2
def baseEnd_2294862 : Nat := 785578161158870383714085

theorem tailTrace_2294862 : CollatzResearch.WordTrace tailWord_2294862 prefixEnd_2294862 785578161158870383714085 := by
  unfold tailWord_2294862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10462561676514297508933855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55800328941409586714313893 10462561676514297508933855)
  ·
    refine ⟨15693842514771446263400783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10462561676514297508933855 15693842514771446263400783)
    ·
      refine ⟨23540763772157169395101175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15693842514771446263400783 23540763772157169395101175)
      ·
        refine ⟨35311145658235754092651763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23540763772157169395101175 35311145658235754092651763)
        ·
          refine ⟨52966718487353631138977645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35311145658235754092651763 52966718487353631138977645)
          ·
            refine ⟨19862519432757611677116617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52966718487353631138977645 19862519432757611677116617)
            ·
              refine ⟨14896889574568208757837463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19862519432757611677116617 14896889574568208757837463)
              ·
                refine ⟨22345334361852313136756195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14896889574568208757837463 22345334361852313136756195)
                ·
                  refine ⟨33518001542778469705134293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22345334361852313136756195 33518001542778469705134293)
                  ·
                    refine ⟨785578161158870383714085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33518001542778469705134293 785578161158870383714085)
                    ·
                      rfl

theorem cell22_2294862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2294862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294862 prefixEnd_2294862 := by exact prefixLift 2294862
  have htrace : WordTrace (prefixWord ++ tailWord_2294862) baseStart_2294862 baseEnd_2294862 := by
    simpa [prefixWord, tailWord_2294862, baseEnd_2294862] using wordTrace_append hprefix tailTrace_2294862
  have hstable : (prefixWord ++ tailWord_2294862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294862).length < 2 ^ (prefixWord ++ tailWord_2294862).sum := by decide
  have hdescent : baseEnd_2294862 < baseStart_2294862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294943 : List Nat := [1, 1, 2, 6, 2, 1, 2, 3, 4]
def baseStart_2294943 : Nat := 118140960795 + 2294943 * 2 ^ 59
def prefixEnd_2294943 : Nat := 4983230072969 + 3 ^ 40 * 2294943 * 2
def baseEnd_2294943 : Nat := 261868629704737724146279

theorem tailTrace_2294943 : CollatzResearch.WordTrace tailWord_2294943 prefixEnd_2294943 261868629704737724146279 := by
  unfold tailWord_2294943
  simp only [CollatzResearch.WordTrace]
  refine ⟨83703447724820930905169483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55802298483213953936779655 83703447724820930905169483)
  ·
    refine ⟨125555171587231396357754225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83703447724820930905169483 125555171587231396357754225)
    ·
      refine ⟨94166378690423547268315669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125555171587231396357754225 94166378690423547268315669)
      ·
        refine ⟨4414049001113603778202297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94166378690423547268315669 4414049001113603778202297)
        ·
          refine ⟨3310536750835202833651723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4414049001113603778202297 3310536750835202833651723)
          ·
            refine ⟨4965805126252804250477585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3310536750835202833651723 4965805126252804250477585)
            ·
              refine ⟨3724353844689603187858189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4965805126252804250477585 3724353844689603187858189)
              ·
                refine ⟨1396632691758601195446821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3724353844689603187858189 1396632691758601195446821)
                ·
                  refine ⟨261868629704737724146279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1396632691758601195446821 261868629704737724146279)
                  ·
                    rfl

theorem cell22_2294943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 4].length) (baseStart_2294943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294943 prefixEnd_2294943 := by exact prefixLift 2294943
  have htrace : WordTrace (prefixWord ++ tailWord_2294943) baseStart_2294943 baseEnd_2294943 := by
    simpa [prefixWord, tailWord_2294943, baseEnd_2294943] using wordTrace_append hprefix tailTrace_2294943
  have hstable : (prefixWord ++ tailWord_2294943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294943).length < 2 ^ (prefixWord ++ tailWord_2294943).sum := by decide
  have hdescent : baseEnd_2294943 < baseStart_2294943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294986 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 3, 3]
def baseStart_2294986 : Nat := 118140960795 + 2294986 * 2 ^ 59
def prefixEnd_2294986 : Nat := 4983230072969 + 3 ^ 40 * 2294986 * 2
def baseEnd_2294986 : Nat := 785620608892975393613705

theorem tailTrace_2294986 : CollatzResearch.WordTrace tailWord_2294986 prefixEnd_2294986 785620608892975393613705 := by
  unfold tailWord_2294986
  simp only [CollatzResearch.WordTrace]
  refine ⟨20926254015916287312246203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55803344042443432832656541 20926254015916287312246203)
  ·
    refine ⟨31389381023874430968369305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20926254015916287312246203 31389381023874430968369305)
    ·
      refine ⟨23542035767905823226276979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31389381023874430968369305 23542035767905823226276979)
      ·
        refine ⟨35313053651858734839415469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23542035767905823226276979 35313053651858734839415469)
        ·
          refine ⟨13242395119447025564780801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35313053651858734839415469 13242395119447025564780801)
          ·
            refine ⟨9931796339585269173585601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13242395119447025564780801 9931796339585269173585601)
            ·
              refine ⟨7448847254688951880189201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9931796339585269173585601 7448847254688951880189201)
              ·
                refine ⟨5586635441016713910141901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7448847254688951880189201 5586635441016713910141901)
                ·
                  refine ⟨2094988290381267716303213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5586635441016713910141901 2094988290381267716303213)
                  ·
                    refine ⟨785620608892975393613705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2094988290381267716303213 785620608892975393613705)
                    ·
                      rfl

theorem cell22_2294986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_2294986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2294986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2294986 prefixEnd_2294986 := by exact prefixLift 2294986
  have htrace : WordTrace (prefixWord ++ tailWord_2294986) baseStart_2294986 baseEnd_2294986 := by
    simpa [prefixWord, tailWord_2294986, baseEnd_2294986] using wordTrace_append hprefix tailTrace_2294986
  have hstable : (prefixWord ++ tailWord_2294986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294986).length < 2 ^ (prefixWord ++ tailWord_2294986).sum := by decide
  have hdescent : baseEnd_2294986 < baseStart_2294986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295020 : List Nat := [2, 2, 1, 1, 2, 5, 3, 2, 1, 3]
def baseStart_2295020 : Nat := 118140960795 + 2295020 * 2 ^ 59
def prefixEnd_2295020 : Nat := 4983230072969 + 3 ^ 40 * 2295020 * 2
def baseEnd_2295020 : Nat := 785632247787810638263601

theorem tailTrace_2295020 : CollatzResearch.WordTrace tailWord_2295020 prefixEnd_2295020 785632247787810638263601 := by
  unfold tailWord_2295020
  simp only [CollatzResearch.WordTrace]
  refine ⟨41853128072770986527861257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55804170763694648703815009 41853128072770986527861257)
  ·
    refine ⟨31389846054578239895895943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41853128072770986527861257 31389846054578239895895943)
    ·
      refine ⟨47084769081867359843843915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31389846054578239895895943 47084769081867359843843915)
      ·
        refine ⟨70627153622801039765765873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47084769081867359843843915 70627153622801039765765873)
        ·
          refine ⟨52970365217100779824324405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70627153622801039765765873 52970365217100779824324405)
          ·
            refine ⟨4965971739103198108530413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52970365217100779824324405 4965971739103198108530413)
            ·
              refine ⟨1862239402163699290698905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4965971739103198108530413 1862239402163699290698905)
              ·
                refine ⟨1396679551622774468024179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1862239402163699290698905 1396679551622774468024179)
                ·
                  refine ⟨2095019327434161702036269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396679551622774468024179 2095019327434161702036269)
                  ·
                    refine ⟨785632247787810638263601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2095019327434161702036269 785632247787810638263601)
                    ·
                      rfl

theorem cell22_2295020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_2295020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295020 prefixEnd_2295020 := by exact prefixLift 2295020
  have htrace : WordTrace (prefixWord ++ tailWord_2295020) baseStart_2295020 baseEnd_2295020 := by
    simpa [prefixWord, tailWord_2295020, baseEnd_2295020] using wordTrace_append hprefix tailTrace_2295020
  have hstable : (prefixWord ++ tailWord_2295020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295020).length < 2 ^ (prefixWord ++ tailWord_2295020).sum := by decide
  have hdescent : baseEnd_2295020 < baseStart_2295020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295061 : List Nat := [1, 3, 2, 1, 2, 1, 1, 7, 4]
def baseStart_2295061 : Nat := 118140960795 + 2295061 * 2 ^ 59
def prefixEnd_2295061 : Nat := 4983230072969 + 3 ^ 40 * 2295061 * 2
def baseEnd_2295061 : Nat := 261882094308566732662825

theorem tailTrace_2295061 : CollatzResearch.WordTrace tailWord_2295061 prefixEnd_2295061 261882094308566732662825 := by
  unfold tailWord_2295061
  simp only [CollatzResearch.WordTrace]
  refine ⟨83707751538393437057965037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55805167692262291371976691 83707751538393437057965037)
  ·
    refine ⟨31390406826897538896736889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83707751538393437057965037 31390406826897538896736889)
    ·
      refine ⟨23542805120173154172552667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31390406826897538896736889 23542805120173154172552667)
      ·
        refine ⟨35314207680259731258829001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23542805120173154172552667 35314207680259731258829001)
        ·
          refine ⟨26485655760194798444121751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35314207680259731258829001 26485655760194798444121751)
          ·
            refine ⟨39728483640292197666182627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26485655760194798444121751 39728483640292197666182627)
            ·
              refine ⟨59592725460438296499273941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39728483640292197666182627 59592725460438296499273941)
              ·
                refine ⟨1396704502979022574201733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59592725460438296499273941 1396704502979022574201733)
                ·
                  refine ⟨261882094308566732662825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1396704502979022574201733 261882094308566732662825)
                  ·
                    rfl

theorem cell22_2295061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_2295061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295061 prefixEnd_2295061 := by exact prefixLift 2295061
  have htrace : WordTrace (prefixWord ++ tailWord_2295061) baseStart_2295061 baseEnd_2295061 := by
    simpa [prefixWord, tailWord_2295061, baseEnd_2295061] using wordTrace_append hprefix tailTrace_2295061
  have hstable : (prefixWord ++ tailWord_2295061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295061).length < 2 ^ (prefixWord ++ tailWord_2295061).sum := by decide
  have hdescent : baseEnd_2295061 < baseStart_2295061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295063 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 1, 4]
def baseStart_2295063 : Nat := 118140960795 + 2295063 * 2 ^ 59
def prefixEnd_2295063 : Nat := 4983230072969 + 3 ^ 40 * 2295063 * 2
def baseEnd_2295063 : Nat := 785646967566572859438469

theorem tailTrace_2295063 : CollatzResearch.WordTrace tailWord_2295063 prefixEnd_2295063 785646967566572859438469 := by
  unfold tailWord_2295063
  simp only [CollatzResearch.WordTrace]
  refine ⟨83707824484386191399537843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55805216322924127599691895 83707824484386191399537843)
  ·
    refine ⟨125561736726579287099306765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83707824484386191399537843 125561736726579287099306765)
    ·
      refine ⟨47085651272467232662240037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125561736726579287099306765 47085651272467232662240037)
      ·
        refine ⟨8828559613587606124170007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47085651272467232662240037 8828559613587606124170007)
        ·
          refine ⟨13242839420381409186255011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8828559613587606124170007 13242839420381409186255011)
          ·
            refine ⟨19864259130572113779382517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13242839420381409186255011 19864259130572113779382517)
            ·
              refine ⟨1862274293491135666817111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19864259130572113779382517 1862274293491135666817111)
              ·
                refine ⟨2793411440236703500225667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862274293491135666817111 2793411440236703500225667)
                ·
                  refine ⟨4190117160355055250338501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793411440236703500225667 4190117160355055250338501)
                  ·
                    refine ⟨785646967566572859438469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190117160355055250338501 785646967566572859438469)
                    ·
                      rfl

theorem cell22_2295063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_2295063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295063 prefixEnd_2295063 := by exact prefixLift 2295063
  have htrace : WordTrace (prefixWord ++ tailWord_2295063) baseStart_2295063 baseEnd_2295063 := by
    simpa [prefixWord, tailWord_2295063, baseEnd_2295063] using wordTrace_append hprefix tailTrace_2295063
  have hstable : (prefixWord ++ tailWord_2295063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295063).length < 2 ^ (prefixWord ++ tailWord_2295063).sum := by decide
  have hdescent : baseEnd_2295063 < baseStart_2295063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295093 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 2, 3]
def baseStart_2295093 : Nat := 118140960795 + 2295093 * 2 ^ 59
def prefixEnd_2295093 : Nat := 4983230072969 + 3 ^ 40 * 2295093 * 2
def baseEnd_2295093 : Nat := 785657237179662781188377

theorem tailTrace_2295093 : CollatzResearch.WordTrace tailWord_2295093 prefixEnd_2295093 785657237179662781188377 := by
  unfold tailWord_2295093
  simp only [CollatzResearch.WordTrace]
  refine ⟨83708918674277506523129933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55805945782851671015419955 83708918674277506523129933)
  ·
    refine ⟨31390844502854064946173725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83708918674277506523129933 31390844502854064946173725)
    ·
      refine ⟨11771566688570274354815147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31390844502854064946173725 11771566688570274354815147)
      ·
        refine ⟨17657350032855411532222721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11771566688570274354815147 17657350032855411532222721)
        ·
          refine ⟨13243012524641558649167041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17657350032855411532222721 13243012524641558649167041)
          ·
            refine ⟨9932259393481168986875281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13243012524641558649167041 9932259393481168986875281)
            ·
              refine ⟨7449194545110876740156461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9932259393481168986875281 7449194545110876740156461)
              ·
                refine ⟨2793447954416578777558673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7449194545110876740156461 2793447954416578777558673)
                ·
                  refine ⟨2095085965812434083169005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2793447954416578777558673 2095085965812434083169005)
                  ·
                    refine ⟨785657237179662781188377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2095085965812434083169005 785657237179662781188377)
                    ·
                      rfl

theorem cell22_2295093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_2295093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295093 prefixEnd_2295093 := by exact prefixLift 2295093
  have htrace : WordTrace (prefixWord ++ tailWord_2295093) baseStart_2295093 baseEnd_2295093 := by
    simpa [prefixWord, tailWord_2295093, baseEnd_2295093] using wordTrace_append hprefix tailTrace_2295093
  have hstable : (prefixWord ++ tailWord_2295093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295093).length < 2 ^ (prefixWord ++ tailWord_2295093).sum := by decide
  have hdescent : baseEnd_2295093 < baseStart_2295093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295108 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2295108 : Nat := 118140960795 + 2295108 * 2 ^ 59
def prefixEnd_2295108 : Nat := 4983230072969 + 3 ^ 40 * 2295108 * 2
def baseEnd_2295108 : Nat := 785662371986207742063331

theorem tailTrace_2295108 : CollatzResearch.WordTrace tailWord_2295108 prefixEnd_2295108 785662371986207742063331 := by
  unfold tailWord_2295108
  simp only [CollatzResearch.WordTrace]
  refine ⟨41854732884611582042462989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55806310512815442723283985 41854732884611582042462989)
  ·
    refine ⟨15695524831729343265923621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41854732884611582042462989 15695524831729343265923621)
    ·
      refine ⟨2942910905949251862360679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15695524831729343265923621 2942910905949251862360679)
      ·
        refine ⟨4414366358923877793541019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2942910905949251862360679 4414366358923877793541019)
        ·
          refine ⟨6621549538385816690311529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4414366358923877793541019 6621549538385816690311529)
          ·
            refine ⟨4966162153789362517733647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6621549538385816690311529 4966162153789362517733647)
            ·
              refine ⟨7449243230684043776600471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4966162153789362517733647 7449243230684043776600471)
              ·
                refine ⟨11173864846026065664900707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7449243230684043776600471 11173864846026065664900707)
                ·
                  refine ⟨16760797269039098497351061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11173864846026065664900707 16760797269039098497351061)
                  ·
                    refine ⟨785662371986207742063331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16760797269039098497351061 785662371986207742063331)
                    ·
                      rfl

theorem cell22_2295108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2295108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295108 prefixEnd_2295108 := by exact prefixLift 2295108
  have htrace : WordTrace (prefixWord ++ tailWord_2295108) baseStart_2295108 baseEnd_2295108 := by
    simpa [prefixWord, tailWord_2295108, baseEnd_2295108] using wordTrace_append hprefix tailTrace_2295108
  have hstable : (prefixWord ++ tailWord_2295108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295108).length < 2 ^ (prefixWord ++ tailWord_2295108).sum := by decide
  have hdescent : baseEnd_2295108 < baseStart_2295108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295121 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 5, 3]
def baseStart_2295121 : Nat := 118140960795 + 2295121 * 2 ^ 59
def prefixEnd_2295121 : Nat := 4983230072969 + 3 ^ 40 * 2295121 * 2
def baseEnd_2295121 : Nat := 785666822151880041488291

theorem tailTrace_2295121 : CollatzResearch.WordTrace tailWord_2295121 prefixEnd_2295121 785666822151880041488291 := by
  unfold tailWord_2295121
  simp only [CollatzResearch.WordTrace]
  refine ⟨83709939918176067305149217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55806626612117378203432811 83709939918176067305149217)
  ·
    refine ⟨62782454938632050478861913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83709939918176067305149217 62782454938632050478861913)
    ·
      refine ⟨47086841203974037859146435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62782454938632050478861913 47086841203974037859146435)
      ·
        refine ⟨70630261805961056788719653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47086841203974037859146435 70630261805961056788719653)
        ·
          refine ⟨13243174088617698147884935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70630261805961056788719653 13243174088617698147884935)
          ·
            refine ⟨19864761132926547221827403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13243174088617698147884935 19864761132926547221827403)
            ·
              refine ⟨29797141699389820832741105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19864761132926547221827403 29797141699389820832741105)
              ·
                refine ⟨22347856274542365624555829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29797141699389820832741105 22347856274542365624555829)
                ·
                  refine ⟨2095111525738346777302109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22347856274542365624555829 2095111525738346777302109)
                  ·
                    refine ⟨785666822151880041488291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2095111525738346777302109 785666822151880041488291)
                    ·
                      rfl

theorem cell22_2295121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_2295121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295121 prefixEnd_2295121 := by exact prefixLift 2295121
  have htrace : WordTrace (prefixWord ++ tailWord_2295121) baseStart_2295121 baseEnd_2295121 := by
    simpa [prefixWord, tailWord_2295121, baseEnd_2295121] using wordTrace_append hprefix tailTrace_2295121
  have hstable : (prefixWord ++ tailWord_2295121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295121).length < 2 ^ (prefixWord ++ tailWord_2295121).sum := by decide
  have hdescent : baseEnd_2295121 < baseStart_2295121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295172 : List Nat := [2, 3, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_2295172 : Nat := 118140960795 + 2295172 * 2 ^ 59
def prefixEnd_2295172 : Nat := 4983230072969 + 3 ^ 40 * 2295172 * 2
def baseEnd_2295172 : Nat := 785684280494132908463135

theorem tailTrace_2295172 : CollatzResearch.WordTrace tailWord_2295172 prefixEnd_2295172 785684280494132908463135 := by
  unfold tailWord_2295172
  simp only [CollatzResearch.WordTrace]
  refine ⟨41855900020495651507627885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55807866693994202010170513 41855900020495651507627885)
  ·
    refine ⟨15695962507685869315360457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41855900020495651507627885 15695962507685869315360457)
    ·
      refine ⟨11771971880764401986520343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15695962507685869315360457 11771971880764401986520343)
      ·
        refine ⟨17657957821146602979780515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11771971880764401986520343 17657957821146602979780515)
        ·
          refine ⟨26486936731719904469670773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17657957821146602979780515 26486936731719904469670773)
          ·
            refine ⟨2483150318598741044031635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26486936731719904469670773 2483150318598741044031635)
            ·
              refine ⟨3724725477898111566047453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483150318598741044031635 3724725477898111566047453)
              ·
                refine ⟨1396772054211791837267795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3724725477898111566047453 1396772054211791837267795)
                ·
                  refine ⟨2095158081317687755901693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396772054211791837267795 2095158081317687755901693)
                  ·
                    refine ⟨785684280494132908463135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2095158081317687755901693 785684280494132908463135)
                    ·
                      rfl

theorem cell22_2295172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_2295172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295172 prefixEnd_2295172 := by exact prefixLift 2295172
  have htrace : WordTrace (prefixWord ++ tailWord_2295172) baseStart_2295172 baseEnd_2295172 := by
    simpa [prefixWord, tailWord_2295172, baseEnd_2295172] using wordTrace_append hprefix tailTrace_2295172
  have hstable : (prefixWord ++ tailWord_2295172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295172).length < 2 ^ (prefixWord ++ tailWord_2295172).sum := by decide
  have hdescent : baseEnd_2295172 < baseStart_2295172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295258 : List Nat := [3, 1, 1, 2, 3, 4, 1, 7]
def baseStart_2295258 : Nat := 118140960795 + 2295258 * 2 ^ 59
def prefixEnd_2295258 : Nat := 4983230072969 + 3 ^ 40 * 2295258 * 2
def baseEnd_2295258 : Nat := 87301524450184150090319

theorem tailTrace_2295258 : CollatzResearch.WordTrace tailWord_2295258 prefixEnd_2295258 87301524450184150090319 := by
  unfold tailWord_2295258
  simp only [CollatzResearch.WordTrace]
  refine ⟨20928734179669934925721607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55809957812453159801924285 20928734179669934925721607)
  ·
    refine ⟨31393101269504902388582411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20928734179669934925721607 31393101269504902388582411)
    ·
      refine ⟨47089651904257353582873617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31393101269504902388582411 47089651904257353582873617)
      ·
        refine ⟨35317238928193015187155213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47089651904257353582873617 35317238928193015187155213)
        ·
          refine ⟨13243964598072380695183205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35317238928193015187155213 13243964598072380695183205)
          ·
            refine ⟨2483243362138571380346851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13243964598072380695183205 2483243362138571380346851)
            ·
              refine ⟨3724865043207857070520277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483243362138571380346851 3724865043207857070520277)
              ·
                refine ⟨87301524450184150090319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3724865043207857070520277 87301524450184150090319)
                ·
                  rfl

theorem cell22_2295258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_2295258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295258 prefixEnd_2295258 := by exact prefixLift 2295258
  have htrace : WordTrace (prefixWord ++ tailWord_2295258) baseStart_2295258 baseEnd_2295258 := by
    simpa [prefixWord, tailWord_2295258, baseEnd_2295258] using wordTrace_append hprefix tailTrace_2295258
  have hstable : (prefixWord ++ tailWord_2295258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295258).length < 2 ^ (prefixWord ++ tailWord_2295258).sum := by decide
  have hdescent : baseEnd_2295258 < baseStart_2295258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295277 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_2295277 : Nat := 118140960795 + 2295277 * 2 ^ 59
def prefixEnd_2295277 : Nat := 4983230072969 + 3 ^ 40 * 2295277 * 2
def baseEnd_2295277 : Nat := 785720224139947634587813

theorem tailTrace_2295277 : CollatzResearch.WordTrace tailWord_2295277 prefixEnd_2295277 785720224139947634587813 := by
  unfold tailWord_2295277
  simp only [CollatzResearch.WordTrace]
  refine ⟨83715629705610905947828085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55810419803740603965218723 83715629705610905947828085)
  ·
    refine ⟨7848340284901022432608883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83715629705610905947828085 7848340284901022432608883)
    ·
      refine ⟨11772510427351533648913325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7848340284901022432608883 11772510427351533648913325)
      ·
        refine ⟨4414691410256825118342497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11772510427351533648913325 4414691410256825118342497)
        ·
          refine ⟨3311018557692618838756873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4414691410256825118342497 3311018557692618838756873)
          ·
            refine ⟨2483263918269464129067655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3311018557692618838756873 2483263918269464129067655)
            ·
              refine ⟨3724895877404196193601483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483263918269464129067655 3724895877404196193601483)
              ·
                refine ⟨5587343816106294290402225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3724895877404196193601483 5587343816106294290402225)
                ·
                  refine ⟨4190507862079720717801669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5587343816106294290402225 4190507862079720717801669)
                  ·
                    refine ⟨785720224139947634587813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190507862079720717801669 785720224139947634587813)
                    ·
                      rfl

theorem cell22_2295277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_2295277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295277 prefixEnd_2295277 := by exact prefixLift 2295277
  have htrace : WordTrace (prefixWord ++ tailWord_2295277) baseStart_2295277 baseEnd_2295277 := by
    simpa [prefixWord, tailWord_2295277, baseEnd_2295277] using wordTrace_append hprefix tailTrace_2295277
  have hstable : (prefixWord ++ tailWord_2295277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295277).length < 2 ^ (prefixWord ++ tailWord_2295277).sum := by decide
  have hdescent : baseEnd_2295277 < baseStart_2295277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295303 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 7]
def baseStart_2295303 : Nat := 118140960795 + 2295303 * 2 ^ 59
def prefixEnd_2295303 : Nat := 4983230072969 + 3 ^ 40 * 2295303 * 2
def baseEnd_2295303 : Nat := 261909708157097411145911

theorem tailTrace_2295303 : CollatzResearch.WordTrace tailWord_2295303 prefixEnd_2295303 261909708157097411145911 := by
  unfold tailWord_2295303
  simp only [CollatzResearch.WordTrace]
  refine ⟨83716578003516712388274563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55811052002344474925516375 83716578003516712388274563)
  ·
    refine ⟨125574867005275068582411845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83716578003516712388274563 125574867005275068582411845)
    ·
      refine ⟨23545287563489075359202221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125574867005275068582411845 23545287563489075359202221)
      ·
        refine ⟨8829482836308403259700833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23545287563489075359202221 8829482836308403259700833)
        ·
          refine ⟨6622112127231302444775625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8829482836308403259700833 6622112127231302444775625)
          ·
            refine ⟨4966584095423476833581719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6622112127231302444775625 4966584095423476833581719)
            ·
              refine ⟨7449876143135215250372579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4966584095423476833581719 7449876143135215250372579)
              ·
                refine ⟨11174814214702822875558869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7449876143135215250372579 11174814214702822875558869)
                ·
                  refine ⟨261909708157097411145911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11174814214702822875558869 261909708157097411145911)
                  ·
                    rfl

theorem cell22_2295303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 7].length) (baseStart_2295303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295303 prefixEnd_2295303 := by exact prefixLift 2295303
  have htrace : WordTrace (prefixWord ++ tailWord_2295303) baseStart_2295303 baseEnd_2295303 := by
    simpa [prefixWord, tailWord_2295303, baseEnd_2295303] using wordTrace_append hprefix tailTrace_2295303
  have hstable : (prefixWord ++ tailWord_2295303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295303).length < 2 ^ (prefixWord ++ tailWord_2295303).sum := by decide
  have hdescent : baseEnd_2295303 < baseStart_2295303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295326 : List Nat := [4, 3, 3, 1, 1, 2, 2, 6]
def baseStart_2295326 : Nat := 118140960795 + 2295326 * 2 ^ 59
def prefixEnd_2295326 : Nat := 4983230072969 + 3 ^ 40 * 2295326 * 2
def baseEnd_2295326 : Nat := 87304110871258648901407

theorem tailTrace_2295326 : CollatzResearch.WordTrace tailWord_2295326 prefixEnd_2295326 87304110871258648901407 := by
  unfold tailWord_2295326
  simp only [CollatzResearch.WordTrace]
  refine ⟨10464677110304173414545229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55811611254955591544241221 10464677110304173414545229)
  ·
    refine ⟨3924253916364065030454461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10464677110304173414545229 3924253916364065030454461)
    ·
      refine ⟨1471595218636524386420423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3924253916364065030454461 1471595218636524386420423)
      ·
        refine ⟨2207392827954786579630635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471595218636524386420423 2207392827954786579630635)
        ·
          refine ⟨3311089241932179869445953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207392827954786579630635 3311089241932179869445953)
          ·
            refine ⟨2483316931449134902084465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3311089241932179869445953 2483316931449134902084465)
            ·
              refine ⟨1862487698586851176563349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2483316931449134902084465 1862487698586851176563349)
              ·
                refine ⟨87304110871258648901407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1862487698586851176563349 87304110871258648901407)
                ·
                  rfl

theorem cell22_2295326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_2295326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295326 prefixEnd_2295326 := by exact prefixLift 2295326
  have htrace : WordTrace (prefixWord ++ tailWord_2295326) baseStart_2295326 baseEnd_2295326 := by
    simpa [prefixWord, tailWord_2295326, baseEnd_2295326] using wordTrace_append hprefix tailTrace_2295326
  have hstable : (prefixWord ++ tailWord_2295326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295326).length < 2 ^ (prefixWord ++ tailWord_2295326).sum := by decide
  have hdescent : baseEnd_2295326 < baseStart_2295326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295395 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 2, 4]
def baseStart_2295395 : Nat := 118140960795 + 2295395 * 2 ^ 59
def prefixEnd_2295395 : Nat := 4983230072969 + 3 ^ 40 * 2295395 * 2
def baseEnd_2295395 : Nat := 785760617951434660137451

theorem tailTrace_2295395 : CollatzResearch.WordTrace tailWord_2295395 prefixEnd_2295395 785760617951434660137451 := by
  unfold tailWord_2295395
  simp only [CollatzResearch.WordTrace]
  refine ⟨83719933519183412100623639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55813289012788941400415759 83719933519183412100623639)
  ·
    refine ⟨125579900278775118150935459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83719933519183412100623639 125579900278775118150935459)
    ·
      refine ⟨188369850418162677226403189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125579900278775118150935459 188369850418162677226403189)
      ·
        refine ⟨17659673476702750989975299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188369850418162677226403189 17659673476702750989975299)
        ·
          refine ⟨26489510215054126484962949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17659673476702750989975299 26489510215054126484962949)
          ·
            refine ⟨4966783165322648715930553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26489510215054126484962949 4966783165322648715930553)
            ·
              refine ⟨3725087373991986536947915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4966783165322648715930553 3725087373991986536947915)
              ·
                refine ⟨5587631060987979805421873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725087373991986536947915 5587631060987979805421873)
                ·
                  refine ⟨4190723295740984854066405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5587631060987979805421873 4190723295740984854066405)
                  ·
                    refine ⟨785760617951434660137451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190723295740984854066405 785760617951434660137451)
                    ·
                      rfl

theorem cell22_2295395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 4].length) (baseStart_2295395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295395 prefixEnd_2295395 := by exact prefixLift 2295395
  have htrace : WordTrace (prefixWord ++ tailWord_2295395) baseStart_2295395 baseEnd_2295395 := by
    simpa [prefixWord, tailWord_2295395, baseEnd_2295395] using wordTrace_append hprefix tailTrace_2295395
  have hstable : (prefixWord ++ tailWord_2295395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295395).length < 2 ^ (prefixWord ++ tailWord_2295395).sum := by decide
  have hdescent : baseEnd_2295395 < baseStart_2295395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295414 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_2295414 : Nat := 118140960795 + 2295414 * 2 ^ 59
def prefixEnd_2295414 : Nat := 4983230072969 + 3 ^ 40 * 2295414 * 2
def baseEnd_2295414 : Nat := 785767122039724943912393

theorem tailTrace_2295414 : CollatzResearch.WordTrace tailWord_2295414 prefixEnd_2295414 785767122039724943912393 := by
  unfold tailWord_2295414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5232539156632161146597831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55813751004076385563710197 5232539156632161146597831)
  ·
    refine ⟨7848808734948241719896747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5232539156632161146597831 7848808734948241719896747)
    ·
      refine ⟨11773213102422362579845121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7848808734948241719896747 11773213102422362579845121)
      ·
        refine ⟨8829909826816771934883841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11773213102422362579845121 8829909826816771934883841)
        ·
          refine ⟨6622432370112578951162881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8829909826816771934883841 6622432370112578951162881)
          ·
            refine ⟨4966824277584434213372161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6622432370112578951162881 4966824277584434213372161)
            ·
              refine ⟨3725118208188325660029121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4966824277584434213372161 3725118208188325660029121)
              ·
                refine ⟨2793838656141244245021841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3725118208188325660029121 2793838656141244245021841)
                ·
                  refine ⟨2095378992105933183766381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2793838656141244245021841 2095378992105933183766381)
                  ·
                    refine ⟨785767122039724943912393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2095378992105933183766381 785767122039724943912393)
                    ·
                      rfl

theorem cell22_2295414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_2295414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295414 prefixEnd_2295414 := by exact prefixLift 2295414
  have htrace : WordTrace (prefixWord ++ tailWord_2295414) baseStart_2295414 baseEnd_2295414 := by
    simpa [prefixWord, tailWord_2295414, baseEnd_2295414] using wordTrace_append hprefix tailTrace_2295414
  have hstable : (prefixWord ++ tailWord_2295414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295414).length < 2 ^ (prefixWord ++ tailWord_2295414).sum := by decide
  have hdescent : baseEnd_2295414 < baseStart_2295414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295453 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2295453 : Nat := 118140960795 + 2295453 * 2 ^ 59
def prefixEnd_2295453 : Nat := 4983230072969 + 3 ^ 40 * 2295453 * 2
def baseEnd_2295453 : Nat := 785780472536741842187273

theorem tailTrace_2295453 : CollatzResearch.WordTrace tailWord_2295453 prefixEnd_2295453 785780472536741842187273 := by
  unfold tailWord_2295453
  simp only [CollatzResearch.WordTrace]
  refine ⟨83722048952973288006235013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55814699301982192004156675 83722048952973288006235013)
  ·
    refine ⟨15697884178682491501169065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83722048952973288006235013 15697884178682491501169065)
    ·
      refine ⟨11773413134011868625876799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15697884178682491501169065 11773413134011868625876799)
      ·
        refine ⟨17660119701017802938815199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11773413134011868625876799 17660119701017802938815199)
        ·
          refine ⟨26490179551526704408222799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17660119701017802938815199 26490179551526704408222799)
          ·
            refine ⟨39735269327290056612334199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26490179551526704408222799 39735269327290056612334199)
            ·
              refine ⟨59602903990935084918501299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39735269327290056612334199 59602903990935084918501299)
              ·
                refine ⟨89404355986402627377751949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59602903990935084918501299 89404355986402627377751949)
                ·
                  refine ⟨33526633494900985266656981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89404355986402627377751949 33526633494900985266656981)
                  ·
                    refine ⟨785780472536741842187273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33526633494900985266656981 785780472536741842187273)
                    ·
                      rfl

theorem cell22_2295453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2295453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295453 prefixEnd_2295453 := by exact prefixLift 2295453
  have htrace : WordTrace (prefixWord ++ tailWord_2295453) baseStart_2295453 baseEnd_2295453 := by
    simpa [prefixWord, tailWord_2295453, baseEnd_2295453] using wordTrace_append hprefix tailTrace_2295453
  have hstable : (prefixWord ++ tailWord_2295453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295453).length < 2 ^ (prefixWord ++ tailWord_2295453).sum := by decide
  have hdescent : baseEnd_2295453 < baseStart_2295453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295502 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2295502 : Nat := 118140960795 + 2295502 * 2 ^ 59
def prefixEnd_2295502 : Nat := 4983230072969 + 3 ^ 40 * 2295502 * 2
def baseEnd_2295502 : Nat := 785797246238122047712123

theorem tailTrace_2295502 : CollatzResearch.WordTrace tailWord_2295502 prefixEnd_2295502 785797246238122047712123 := by
  unfold tailWord_2295502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465479516224471171846095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55815890753197179583179173 10465479516224471171846095)
  ·
    refine ⟨15698219274336706757769143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10465479516224471171846095 15698219274336706757769143)
    ·
      refine ⟨23547328911505060136653715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15698219274336706757769143 23547328911505060136653715)
      ·
        refine ⟨35320993367257590204980573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23547328911505060136653715 35320993367257590204980573)
        ·
          refine ⟨13245372512721596326867715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35320993367257590204980573 13245372512721596326867715)
          ·
            refine ⟨19868058769082394490301573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13245372512721596326867715 19868058769082394490301573)
            ·
              refine ⟨3725261019202948966931545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19868058769082394490301573 3725261019202948966931545)
              ·
                refine ⟨2793945764402211725198659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3725261019202948966931545 2793945764402211725198659)
                ·
                  refine ⟨4190918646603317587797989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793945764402211725198659 4190918646603317587797989)
                  ·
                    refine ⟨785797246238122047712123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190918646603317587797989 785797246238122047712123)
                    ·
                      rfl

theorem cell22_2295502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2295502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295502 prefixEnd_2295502 := by exact prefixLift 2295502
  have htrace : WordTrace (prefixWord ++ tailWord_2295502) baseStart_2295502 baseEnd_2295502 := by
    simpa [prefixWord, tailWord_2295502, baseEnd_2295502] using wordTrace_append hprefix tailTrace_2295502
  have hstable : (prefixWord ++ tailWord_2295502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295502).length < 2 ^ (prefixWord ++ tailWord_2295502).sum := by decide
  have hdescent : baseEnd_2295502 < baseStart_2295502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295510 : List Nat := [5, 2, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2295510 : Nat := 118140960795 + 2295510 * 2 ^ 59
def prefixEnd_2295510 : Nat := 4983230072969 + 3 ^ 40 * 2295510 * 2
def baseEnd_2295510 : Nat := 785799984801612693512099

theorem tailTrace_2295510 : CollatzResearch.WordTrace tailWord_2295510 prefixEnd_2295510 785799984801612693512099 := by
  unfold tailWord_2295510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5232757994610424171316249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55816085275844524494039989 5232757994610424171316249)
  ·
    refine ⟨3924568495957818128487187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5232757994610424171316249 3924568495957818128487187)
    ·
      refine ⟨5886852743936727192730781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3924568495957818128487187 5886852743936727192730781)
      ·
        refine ⟨2207569778976272697274043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5886852743936727192730781 2207569778976272697274043)
        ·
          refine ⟨3311354668464409045911065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207569778976272697274043 3311354668464409045911065)
          ·
            refine ⟨2483516001348306784433299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3311354668464409045911065 2483516001348306784433299)
            ·
              refine ⟨3725274002022460176649949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483516001348306784433299 3725274002022460176649949)
              ·
                refine ⟨1396977750758422566243731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3725274002022460176649949 1396977750758422566243731)
                ·
                  refine ⟨2095466626137633849365597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396977750758422566243731 2095466626137633849365597)
                  ·
                    refine ⟨785799984801612693512099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2095466626137633849365597 785799984801612693512099)
                    ·
                      rfl

theorem cell22_2295510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2295510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295510 prefixEnd_2295510 := by exact prefixLift 2295510
  have htrace : WordTrace (prefixWord ++ tailWord_2295510) baseStart_2295510 baseEnd_2295510 := by
    simpa [prefixWord, tailWord_2295510, baseEnd_2295510] using wordTrace_append hprefix tailTrace_2295510
  have hstable : (prefixWord ++ tailWord_2295510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295510).length < 2 ^ (prefixWord ++ tailWord_2295510).sum := by decide
  have hdescent : baseEnd_2295510 < baseStart_2295510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295530 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_2295530 : Nat := 118140960795 + 2295530 * 2 ^ 59
def prefixEnd_2295530 : Nat := 4983230072969 + 3 ^ 40 * 2295530 * 2
def baseEnd_2295530 : Nat := 785806831210339308012037

theorem tailTrace_2295530 : CollatzResearch.WordTrace tailWord_2295530 prefixEnd_2295530 785806831210339308012037 := by
  unfold tailWord_2295530
  simp only [CollatzResearch.WordTrace]
  refine ⟨20931214343423582539197011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55816571582462886771192029 20931214343423582539197011)
  ·
    refine ⟨31396821515135373808795517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20931214343423582539197011 31396821515135373808795517)
    ·
      refine ⟨11773808068175765178298319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31396821515135373808795517 11773808068175765178298319)
      ·
        refine ⟨17660712102263647767447479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11773808068175765178298319 17660712102263647767447479)
        ·
          refine ⟨26491068153395471651171219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17660712102263647767447479 26491068153395471651171219)
          ·
            refine ⟨39736602230093207476756829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26491068153395471651171219 39736602230093207476756829)
            ·
              refine ⟨14901225836284952803783811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39736602230093207476756829 14901225836284952803783811)
              ·
                refine ⟨22351838754427429205675717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14901225836284952803783811 22351838754427429205675717)
                ·
                  refine ⟨4190969766455142976064197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22351838754427429205675717 4190969766455142976064197)
                  ·
                    refine ⟨785806831210339308012037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190969766455142976064197 785806831210339308012037)
                    ·
                      rfl

theorem cell22_2295530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_2295530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295530 prefixEnd_2295530 := by exact prefixLift 2295530
  have htrace : WordTrace (prefixWord ++ tailWord_2295530) baseStart_2295530 baseEnd_2295530 := by
    simpa [prefixWord, tailWord_2295530, baseEnd_2295530] using wordTrace_append hprefix tailTrace_2295530
  have hstable : (prefixWord ++ tailWord_2295530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295530).length < 2 ^ (prefixWord ++ tailWord_2295530).sum := by decide
  have hdescent : baseEnd_2295530 < baseStart_2295530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295534 : List Nat := [4, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_2295534 : Nat := 118140960795 + 2295534 * 2 ^ 59
def prefixEnd_2295534 : Nat := 4983230072969 + 3 ^ 40 * 2295534 * 2
def baseEnd_2295534 : Nat := 261936066830694876970675

theorem tailTrace_2295534 : CollatzResearch.WordTrace tailWord_2295534 prefixEnd_2295534 261936066830694876970675 := by
  unfold tailWord_2295534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465625408209979854991707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55816668843786559226622437 10465625408209979854991707)
  ·
    refine ⟨15698438112314969782487561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10465625408209979854991707 15698438112314969782487561)
    ·
      refine ⟨11773828584236227336865671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15698438112314969782487561 11773828584236227336865671)
      ·
        refine ⟨17660742876354341005298507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11773828584236227336865671 17660742876354341005298507)
        ·
          refine ⟨26491114314531511507947761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17660742876354341005298507 26491114314531511507947761)
          ·
            refine ⟨19868335735898633630960821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26491114314531511507947761 19868335735898633630960821)
            ·
              refine ⟨1862656475240496902902577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19868335735898633630960821 1862656475240496902902577)
              ·
                refine ⟨1396992356430372677176933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1862656475240496902902577 1396992356430372677176933)
                ·
                  refine ⟨261936066830694876970675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1396992356430372677176933 261936066830694876970675)
                  ·
                    rfl

theorem cell22_2295534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_2295534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295534 prefixEnd_2295534 := by exact prefixLift 2295534
  have htrace : WordTrace (prefixWord ++ tailWord_2295534) baseStart_2295534 baseEnd_2295534 := by
    simpa [prefixWord, tailWord_2295534, baseEnd_2295534] using wordTrace_append hprefix tailTrace_2295534
  have hstable : (prefixWord ++ tailWord_2295534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295534).length < 2 ^ (prefixWord ++ tailWord_2295534).sum := by decide
  have hdescent : baseEnd_2295534 < baseStart_2295534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295665 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_2295665 : Nat := 118140960795 + 2295665 * 2 ^ 59
def prefixEnd_2295665 : Nat := 4983230072969 + 3 ^ 40 * 2295665 * 2
def baseEnd_2295665 : Nat := 785853044469243955886623

theorem tailTrace_2295665 : CollatzResearch.WordTrace tailWord_2295665 prefixEnd_2295665 785853044469243955886623 := by
  unfold tailWord_2295665
  simp only [CollatzResearch.WordTrace]
  refine ⟨83729781228205248212952449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55819854152136832141968299 83729781228205248212952449)
  ·
    refine ⟨62797335921153936159714337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83729781228205248212952449 62797335921153936159714337)
    ·
      refine ⟨47098001940865452119785753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62797335921153936159714337 47098001940865452119785753)
      ·
        refine ⟨35323501455649089089839315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47098001940865452119785753 35323501455649089089839315)
        ·
          refine ⟨52985252183473633634758973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35323501455649089089839315 52985252183473633634758973)
          ·
            refine ⟨19869469568802612613034615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52985252183473633634758973 19869469568802612613034615)
            ·
              refine ⟨29804204353203918919551923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19869469568802612613034615 29804204353203918919551923)
              ·
                refine ⟨44706306529805878379327885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29804204353203918919551923 44706306529805878379327885)
                ·
                  refine ⟨16764864948677204392247957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44706306529805878379327885 16764864948677204392247957)
                  ·
                    refine ⟨785853044469243955886623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16764864948677204392247957 785853044469243955886623)
                    ·
                      rfl

theorem cell22_2295665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_2295665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295665 prefixEnd_2295665 := by exact prefixLift 2295665
  have htrace : WordTrace (prefixWord ++ tailWord_2295665) baseStart_2295665 baseEnd_2295665 := by
    simpa [prefixWord, tailWord_2295665, baseEnd_2295665] using wordTrace_append hprefix tailTrace_2295665
  have hstable : (prefixWord ++ tailWord_2295665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295665).length < 2 ^ (prefixWord ++ tailWord_2295665).sum := by decide
  have hdescent : baseEnd_2295665 < baseStart_2295665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295680 : List Nat := [2, 1, 1, 2, 1, 2, 5, 8]
def baseStart_2295680 : Nat := 118140960795 + 2295680 * 2 ^ 59
def prefixEnd_2295680 : Nat := 4983230072969 + 3 ^ 40 * 2295680 * 2
def baseEnd_2295680 : Nat := 87317575475087657417953

theorem tailTrace_2295680 : CollatzResearch.WordTrace tailWord_2295680 prefixEnd_2295680 87317575475087657417953 := by
  unfold tailWord_2295680
  simp only [CollatzResearch.WordTrace]
  refine ⟨41865164161575452887374247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55820218882100603849832329 41865164161575452887374247)
  ·
    refine ⟨62797746242363179331061371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41865164161575452887374247 62797746242363179331061371)
    ·
      refine ⟨94196619363544768996592057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62797746242363179331061371 94196619363544768996592057)
      ·
        refine ⟨70647464522658576747444043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94196619363544768996592057 70647464522658576747444043)
        ·
          refine ⟨105971196783987865121166065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70647464522658576747444043 105971196783987865121166065)
          ·
            refine ⟨79478397587990898840874549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105971196783987865121166065 79478397587990898840874549)
            ·
              refine ⟨7451099773874146766331989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79478397587990898840874549 7451099773874146766331989)
              ·
                refine ⟨87317575475087657417953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7451099773874146766331989 87317575475087657417953)
                ·
                  rfl

theorem cell22_2295680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 8].length) (baseStart_2295680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295680 prefixEnd_2295680 := by exact prefixLift 2295680
  have htrace : WordTrace (prefixWord ++ tailWord_2295680) baseStart_2295680 baseEnd_2295680 := by
    simpa [prefixWord, tailWord_2295680, baseEnd_2295680] using wordTrace_append hprefix tailTrace_2295680
  have hstable : (prefixWord ++ tailWord_2295680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295680).length < 2 ^ (prefixWord ++ tailWord_2295680).sum := by decide
  have hdescent : baseEnd_2295680 < baseStart_2295680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295714 : List Nat := [3, 3, 1, 2, 3, 1, 2, 7]
def baseStart_2295714 : Nat := 118140960795 + 2295714 * 2 ^ 59
def prefixEnd_2295714 : Nat := 4983230072969 + 3 ^ 40 * 2295714 * 2
def baseEnd_2295714 : Nat := 87318868685624906823497

theorem tailTrace_2295714 : CollatzResearch.WordTrace tailWord_2295714 prefixEnd_2295714 87318868685624906823497 := by
  unfold tailWord_2295714
  simp only [CollatzResearch.WordTrace]
  refine ⟨20932892101256932395371549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55821045603351819720990797 20932892101256932395371549)
  ·
    refine ⟨7849834537971349648264331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20932892101256932395371549 7849834537971349648264331)
    ·
      refine ⟨11774751806957024472396497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7849834537971349648264331 11774751806957024472396497)
      ·
        refine ⟨8831063855217768354297373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11774751806957024472396497 8831063855217768354297373)
        ·
          refine ⟨3311648945706663132861515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8831063855217768354297373 3311648945706663132861515)
          ·
            refine ⟨4967473418559994699292273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311648945706663132861515 4967473418559994699292273)
            ·
              refine ⟨3725605063919996024469205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4967473418559994699292273 3725605063919996024469205)
              ·
                refine ⟨87318868685624906823497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3725605063919996024469205 87318868685624906823497)
                ·
                  rfl

theorem cell22_2295714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_2295714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295714 prefixEnd_2295714 := by exact prefixLift 2295714
  have htrace : WordTrace (prefixWord ++ tailWord_2295714) baseStart_2295714 baseEnd_2295714 := by
    simpa [prefixWord, tailWord_2295714, baseEnd_2295714] using wordTrace_append hprefix tailTrace_2295714
  have hstable : (prefixWord ++ tailWord_2295714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295714).length < 2 ^ (prefixWord ++ tailWord_2295714).sum := by decide
  have hdescent : baseEnd_2295714 < baseStart_2295714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295819 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 4, 3]
def baseStart_2295819 : Nat := 118140960795 + 2295819 * 2 ^ 59
def prefixEnd_2295819 : Nat := 4983230072969 + 3 ^ 40 * 2295819 * 2
def baseEnd_2295819 : Nat := 785905761816438887536151

theorem tailTrace_2295819 : CollatzResearch.WordTrace tailWord_2295819 prefixEnd_2295819 785905761816438887536151 := by
  unfold tailWord_2295819
  simp only [CollatzResearch.WordTrace]
  refine ⟨83735398069647332514058511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55823598713098221676039007 83735398069647332514058511)
  ·
    refine ⟨125603097104470998771087767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83735398069647332514058511 125603097104470998771087767)
    ·
      refine ⟨188404645656706498156631651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125603097104470998771087767 188404645656706498156631651)
      ·
        refine ⟨282606968485059747234947477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188404645656706498156631651 282606968485059747234947477)
        ·
          refine ⟨13247201647737175651638163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 282606968485059747234947477 13247201647737175651638163)
          ·
            refine ⟨19870802471605763477457245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13247201647737175651638163 19870802471605763477457245)
            ·
              refine ⟨7451550926852161304046467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19870802471605763477457245 7451550926852161304046467)
              ·
                refine ⟨11177326390278241956069701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7451550926852161304046467 11177326390278241956069701)
                ·
                  refine ⟨2095748698177170366763069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11177326390278241956069701 2095748698177170366763069)
                  ·
                    refine ⟨785905761816438887536151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2095748698177170366763069 785905761816438887536151)
                    ·
                      rfl

theorem cell22_2295819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 3].length) (baseStart_2295819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295819 prefixEnd_2295819 := by exact prefixLift 2295819
  have htrace : WordTrace (prefixWord ++ tailWord_2295819) baseStart_2295819 baseEnd_2295819 := by
    simpa [prefixWord, tailWord_2295819, baseEnd_2295819] using wordTrace_append hprefix tailTrace_2295819
  have hstable : (prefixWord ++ tailWord_2295819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295819).length < 2 ^ (prefixWord ++ tailWord_2295819).sum := by decide
  have hdescent : baseEnd_2295819 < baseStart_2295819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295832 : List Nat := [2, 1, 2, 3, 2, 1, 2, 9]
def baseStart_2295832 : Nat := 118140960795 + 2295832 * 2 ^ 59
def prefixEnd_2295832 : Nat := 4983230072969 + 3 ^ 40 * 2295832 * 2
def baseEnd_2295832 : Nat := 87323356886901242995679

theorem tailTrace_2295832 : CollatzResearch.WordTrace tailWord_2295832 prefixEnd_2295832 87323356886901242995679 := by
  unfold tailWord_2295832
  simp only [CollatzResearch.WordTrace]
  refine ⟨41867936109300117867140875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55823914812400157156187833 41867936109300117867140875)
  ·
    refine ⟨62801904163950176800711313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41867936109300117867140875 62801904163950176800711313)
    ·
      refine ⟨47101428122962632600533485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62801904163950176800711313 47101428122962632600533485)
      ·
        refine ⟨17663035546110987225200057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47101428122962632600533485 17663035546110987225200057)
        ·
          refine ⟨13247276659583240418900043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17663035546110987225200057 13247276659583240418900043)
          ·
            refine ⟨19870914989374860628350065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13247276659583240418900043 19870914989374860628350065)
            ·
              refine ⟨14903186242031145471262549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19870914989374860628350065 14903186242031145471262549)
              ·
                refine ⟨87323356886901242995679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14903186242031145471262549 87323356886901242995679)
                ·
                  rfl

theorem cell22_2295832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 9].length) (baseStart_2295832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295832 prefixEnd_2295832 := by exact prefixLift 2295832
  have htrace : WordTrace (prefixWord ++ tailWord_2295832) baseStart_2295832 baseEnd_2295832 := by
    simpa [prefixWord, tailWord_2295832, baseEnd_2295832] using wordTrace_append hprefix tailTrace_2295832
  have hstable : (prefixWord ++ tailWord_2295832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295832).length < 2 ^ (prefixWord ++ tailWord_2295832).sum := by decide
  have hdescent : baseEnd_2295832 < baseStart_2295832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295836 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 1, 5]
def baseStart_2295836 : Nat := 118140960795 + 2295836 * 2 ^ 59
def prefixEnd_2295836 : Nat := 4983230072969 + 3 ^ 40 * 2295836 * 2
def baseEnd_2295836 : Nat := 785911581263856509861099

theorem tailTrace_2295836 : CollatzResearch.WordTrace tailWord_2295836 prefixEnd_2295836 785911581263856509861099 := by
  unfold tailWord_2295836
  simp only [CollatzResearch.WordTrace]
  refine ⟨41868009055292872208713681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55824012073723829611618241 41868009055292872208713681)
  ·
    refine ⟨31401006791469654156535261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41868009055292872208713681 31401006791469654156535261)
    ·
      refine ⟨11775377546801120308700723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31401006791469654156535261 11775377546801120308700723)
      ·
        refine ⟨17663066320201680463051085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11775377546801120308700723 17663066320201680463051085)
        ·
          refine ⟨6623649870075630173644157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17663066320201680463051085 6623649870075630173644157)
          ·
            refine ⟨2483868701278361315116559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6623649870075630173644157 2483868701278361315116559)
            ·
              refine ⟨3725803051917541972674839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483868701278361315116559 3725803051917541972674839)
              ·
                refine ⟨5588704577876312959012259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725803051917541972674839 5588704577876312959012259)
                ·
                  refine ⟨8383056866814469438518389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5588704577876312959012259 8383056866814469438518389)
                  ·
                    refine ⟨785911581263856509861099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8383056866814469438518389 785911581263856509861099)
                    ·
                      rfl

theorem cell22_2295836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_2295836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2295836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2295836 prefixEnd_2295836 := by exact prefixLift 2295836
  have htrace : WordTrace (prefixWord ++ tailWord_2295836) baseStart_2295836 baseEnd_2295836 := by
    simpa [prefixWord, tailWord_2295836, baseEnd_2295836] using wordTrace_append hprefix tailTrace_2295836
  have hstable : (prefixWord ++ tailWord_2295836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295836).length < 2 ^ (prefixWord ++ tailWord_2295836).sum := by decide
  have hdescent : baseEnd_2295836 < baseStart_2295836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296018 : List Nat := [3, 2, 2, 2, 1, 4, 2, 6]
def baseStart_2296018 : Nat := 118140960795 + 2296018 * 2 ^ 59
def prefixEnd_2296018 : Nat := 4983230072969 + 3 ^ 40 * 2296018 * 2
def baseEnd_2296018 : Nat := 87330431509252077978949

theorem tailTrace_2296018 : CollatzResearch.WordTrace tailWord_2296018 prefixEnd_2296018 87330431509252077978949 := by
  unfold tailWord_2296018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20935664048981597375138177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55828437463950926333701805 20935664048981597375138177)
  ·
    refine ⟨15701748036736198031353633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20935664048981597375138177 15701748036736198031353633)
    ·
      refine ⟨11776311027552148523515225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15701748036736198031353633 11776311027552148523515225)
      ·
        refine ⟨8832233270664111392636419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11776311027552148523515225 8832233270664111392636419)
        ·
          refine ⟨13248349905996167088954629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8832233270664111392636419 13248349905996167088954629)
          ·
            refine ⟨2484065607374281329178993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13248349905996167088954629 2484065607374281329178993)
            ·
              refine ⟨1863049205530710996884245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2484065607374281329178993 1863049205530710996884245)
              ·
                refine ⟨87330431509252077978949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1863049205530710996884245 87330431509252077978949)
                ·
                  rfl

theorem cell22_2296018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_2296018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296018 prefixEnd_2296018 := by exact prefixLift 2296018
  have htrace : WordTrace (prefixWord ++ tailWord_2296018) baseStart_2296018 baseEnd_2296018 := by
    simpa [prefixWord, tailWord_2296018, baseEnd_2296018] using wordTrace_append hprefix tailTrace_2296018
  have hstable : (prefixWord ++ tailWord_2296018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296018).length < 2 ^ (prefixWord ++ tailWord_2296018).sum := by decide
  have hdescent : baseEnd_2296018 < baseStart_2296018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296046 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_2296046 : Nat := 118140960795 + 2296046 * 2 ^ 59
def prefixEnd_2296046 : Nat := 4983230072969 + 3 ^ 40 * 2296046 * 2
def baseEnd_2296046 : Nat := 261994489518495320703485

theorem tailTrace_2296046 : CollatzResearch.WordTrace tailWord_2296046 prefixEnd_2296046 261994489518495320703485 := by
  unfold tailWord_2296046
  simp only [CollatzResearch.WordTrace]
  refine ⟨10467959679978118785321499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55829118293216633521714661 10467959679978118785321499)
  ·
    refine ⟨15701939519967178177982249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10467959679978118785321499 15701939519967178177982249)
    ·
      refine ⟨11776454639975383633486687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15701939519967178177982249 11776454639975383633486687)
      ·
        refine ⟨17664681959963075450230031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11776454639975383633486687 17664681959963075450230031)
        ·
          refine ⟨26497022939944613175345047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17664681959963075450230031 26497022939944613175345047)
          ·
            refine ⟨39745534409916919763017571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26497022939944613175345047 39745534409916919763017571)
            ·
              refine ⟨59618301614875379644526357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39745534409916919763017571 59618301614875379644526357)
              ·
                refine ⟨2794607888197283420837173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59618301614875379644526357 2794607888197283420837173)
                ·
                  refine ⟨261994489518495320703485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2794607888197283420837173 261994489518495320703485)
                  ·
                    rfl

theorem cell22_2296046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_2296046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296046 prefixEnd_2296046 := by exact prefixLift 2296046
  have htrace : WordTrace (prefixWord ++ tailWord_2296046) baseStart_2296046 baseEnd_2296046 := by
    simpa [prefixWord, tailWord_2296046, baseEnd_2296046] using wordTrace_append hprefix tailTrace_2296046
  have hstable : (prefixWord ++ tailWord_2296046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296046).length < 2 ^ (prefixWord ++ tailWord_2296046).sum := by decide
  have hdescent : baseEnd_2296046 < baseStart_2296046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296050 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_2296050 : Nat := 118140960795 + 2296050 * 2 ^ 59
def prefixEnd_2296050 : Nat := 4983230072969 + 3 ^ 40 * 2296050 * 2
def baseEnd_2296050 : Nat := 785984837837231285010443

theorem tailTrace_2296050 : CollatzResearch.WordTrace tailWord_2296050 prefixEnd_2296050 785984837837231285010443 := by
  unfold tailWord_2296050
  simp only [CollatzResearch.WordTrace]
  refine ⟨20935955832952614741429401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55829215554540305977145069 20935955832952614741429401)
  ·
    refine ⟨15701966874714461056072051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20935955832952614741429401 15701966874714461056072051)
    ·
      refine ⟨23552950312071691584108077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15701966874714461056072051 23552950312071691584108077)
      ·
        refine ⟨8832356367026884344040529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23552950312071691584108077 8832356367026884344040529)
        ·
          refine ⟨6624267275270163258030397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8832356367026884344040529 6624267275270163258030397)
          ·
            refine ⟨2484100228226311221761399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6624267275270163258030397 2484100228226311221761399)
            ·
              refine ⟨3726150342339466832642099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2484100228226311221761399 3726150342339466832642099)
              ·
                refine ⟨5589225513509200248963149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3726150342339466832642099 5589225513509200248963149)
                ·
                  refine ⟨2095959567565950093361181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5589225513509200248963149 2095959567565950093361181)
                  ·
                    refine ⟨785984837837231285010443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2095959567565950093361181 785984837837231285010443)
                    ·
                      rfl

theorem cell22_2296050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_2296050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296050 prefixEnd_2296050 := by exact prefixLift 2296050
  have htrace : WordTrace (prefixWord ++ tailWord_2296050) baseStart_2296050 baseEnd_2296050 := by
    simpa [prefixWord, tailWord_2296050, baseEnd_2296050] using wordTrace_append hprefix tailTrace_2296050
  have hstable : (prefixWord ++ tailWord_2296050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296050).length < 2 ^ (prefixWord ++ tailWord_2296050).sum := by decide
  have hdescent : baseEnd_2296050 < baseStart_2296050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296076 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_2296076 : Nat := 118140960795 + 2296076 * 2 ^ 59
def prefixEnd_2296076 : Nat := 4983230072969 + 3 ^ 40 * 2296076 * 2
def baseEnd_2296076 : Nat := 785993738168575883860363

theorem tailTrace_2296076 : CollatzResearch.WordTrace tailWord_2296076 prefixEnd_2296076 785993738168575883860363 := by
  unfold tailWord_2296076
  simp only [CollatzResearch.WordTrace]
  refine ⟨41872385814858132703082041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55829847753144176937442721 41872385814858132703082041)
  ·
    refine ⟨31404289361143599527311531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41872385814858132703082041 31404289361143599527311531)
    ·
      refine ⟨47106434041715399290967297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31404289361143599527311531 47106434041715399290967297)
      ·
        refine ⟨35329825531286549468225473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47106434041715399290967297 35329825531286549468225473)
        ·
          refine ⟨26497369148464912101169105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35329825531286549468225473 26497369148464912101169105)
          ·
            refine ⟨19873026861348684075876829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26497369148464912101169105 19873026861348684075876829)
            ·
              refine ⟨7452385073005756528453811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19873026861348684075876829 7452385073005756528453811)
              ·
                refine ⟨11178577609508634792680717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7452385073005756528453811 11178577609508634792680717)
                ·
                  refine ⟨4191966603565738047255269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11178577609508634792680717 4191966603565738047255269)
                  ·
                    refine ⟨785993738168575883860363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4191966603565738047255269 785993738168575883860363)
                    ·
                      rfl

theorem cell22_2296076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_2296076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296076 prefixEnd_2296076 := by exact prefixLift 2296076
  have htrace : WordTrace (prefixWord ++ tailWord_2296076) baseStart_2296076 baseEnd_2296076 := by
    simpa [prefixWord, tailWord_2296076, baseEnd_2296076] using wordTrace_append hprefix tailTrace_2296076
  have hstable : (prefixWord ++ tailWord_2296076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296076).length < 2 ^ (prefixWord ++ tailWord_2296076).sum := by decide
  have hdescent : baseEnd_2296076 < baseStart_2296076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296232 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 5]
def baseStart_2296232 : Nat := 118140960795 + 2296232 * 2 ^ 59
def prefixEnd_2296232 : Nat := 4983230072969 + 3 ^ 40 * 2296232 * 2
def baseEnd_2296232 : Nat := 262015713385547825653295

theorem tailTrace_2296232 : CollatzResearch.WordTrace tailWord_2296232 prefixEnd_2296232 262015713385547825653295 := by
  unfold tailWord_2296232
  simp only [CollatzResearch.WordTrace]
  refine ⟨41875230708575552024421475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55833640944767402699228633 41875230708575552024421475)
  ·
    refine ⟨62812846062863328036632213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41875230708575552024421475 62812846062863328036632213)
    ·
      refine ⟨2944352159196718501717135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62812846062863328036632213 2944352159196718501717135)
      ·
        refine ⟨4416528238795077752575703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2944352159196718501717135 4416528238795077752575703)
        ·
          refine ⟨6624792358192616628863555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4416528238795077752575703 6624792358192616628863555)
          ·
            refine ⟨9937188537288924943295333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6624792358192616628863555 9937188537288924943295333)
            ·
              refine ⟨1863222850741673426867875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9937188537288924943295333 1863222850741673426867875)
              ·
                refine ⟨2794834276112510140301813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863222850741673426867875 2794834276112510140301813)
                ·
                  refine ⟨262015713385547825653295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2794834276112510140301813 262015713385547825653295)
                  ·
                    rfl

theorem cell22_2296232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 5].length) (baseStart_2296232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296232 prefixEnd_2296232 := by exact prefixLift 2296232
  have htrace : WordTrace (prefixWord ++ tailWord_2296232) baseStart_2296232 baseEnd_2296232 := by
    simpa [prefixWord, tailWord_2296232, baseEnd_2296232] using wordTrace_append hprefix tailTrace_2296232
  have hstable : (prefixWord ++ tailWord_2296232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296232).length < 2 ^ (prefixWord ++ tailWord_2296232).sum := by decide
  have hdescent : baseEnd_2296232 < baseStart_2296232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296245 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_2296245 : Nat := 118140960795 + 2296245 * 2 ^ 59
def prefixEnd_2296245 : Nat := 4983230072969 + 3 ^ 40 * 2296245 * 2
def baseEnd_2296245 : Nat := 786051590322315776384845

theorem tailTrace_2296245 : CollatzResearch.WordTrace tailWord_2296245 prefixEnd_2296245 786051590322315776384845 := by
  unfold tailWord_2296245
  simp only [CollatzResearch.WordTrace]
  refine ⟨83750935566104007269066189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55833957044069338179377459 83750935566104007269066189)
  ·
    refine ⟨31406600837289002725899821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83750935566104007269066189 31406600837289002725899821)
    ·
      refine ⟨11777475313983376022212433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31406600837289002725899821 11777475313983376022212433)
      ·
        refine ⟨8833106485487532016659325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11777475313983376022212433 8833106485487532016659325)
        ·
          refine ⟨3312414932057824506247247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8833106485487532016659325 3312414932057824506247247)
          ·
            refine ⟨4968622398086736759370871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312414932057824506247247 4968622398086736759370871)
            ·
              refine ⟨7452933597130105139056307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4968622398086736759370871 7452933597130105139056307)
              ·
                refine ⟨11179400395695157708584461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7452933597130105139056307 11179400395695157708584461)
                ·
                  refine ⟨4192275148385684140719173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11179400395695157708584461 4192275148385684140719173)
                  ·
                    refine ⟨786051590322315776384845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4192275148385684140719173 786051590322315776384845)
                    ·
                      rfl

theorem cell22_2296245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_2296245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296245 prefixEnd_2296245 := by exact prefixLift 2296245
  have htrace : WordTrace (prefixWord ++ tailWord_2296245) baseStart_2296245 baseEnd_2296245 := by
    simpa [prefixWord, tailWord_2296245, baseEnd_2296245] using wordTrace_append hprefix tailTrace_2296245
  have hstable : (prefixWord ++ tailWord_2296245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296245).length < 2 ^ (prefixWord ++ tailWord_2296245).sum := by decide
  have hdescent : baseEnd_2296245 < baseStart_2296245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296277 : List Nat := [1, 3, 2, 3, 1, 2, 4, 2, 4]
def baseStart_2296277 : Nat := 118140960795 + 2296277 * 2 ^ 59
def prefixEnd_2296277 : Nat := 4983230072969 + 3 ^ 40 * 2296277 * 2
def baseEnd_2296277 : Nat := 262020848192092786528249

theorem tailTrace_2296277 : CollatzResearch.WordTrace tailWord_2296277 prefixEnd_2296277 262020848192092786528249 := by
  unfold tailWord_2296277
  simp only [CollatzResearch.WordTrace]
  refine ⟨83752102701988076734231085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55834735134658717822820723 83752102701988076734231085)
  ·
    refine ⟨31407038513245528775336657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83752102701988076734231085 31407038513245528775336657)
    ·
      refine ⟨23555278884934146581502493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31407038513245528775336657 23555278884934146581502493)
      ·
        refine ⟨8833229581850304968063435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23555278884934146581502493 8833229581850304968063435)
        ·
          refine ⟨13249844372775457452095153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8833229581850304968063435 13249844372775457452095153)
          ·
            refine ⟨9937383279581593089071365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13249844372775457452095153 9937383279581593089071365)
            ·
              refine ⟨1863259364921548704200881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9937383279581593089071365 1863259364921548704200881)
              ·
                refine ⟨1397444523691161528150661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1863259364921548704200881 1397444523691161528150661)
                ·
                  refine ⟨262020848192092786528249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1397444523691161528150661 262020848192092786528249)
                  ·
                    rfl

theorem cell22_2296277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_2296277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296277 prefixEnd_2296277 := by exact prefixLift 2296277
  have htrace : WordTrace (prefixWord ++ tailWord_2296277) baseStart_2296277 baseEnd_2296277 := by
    simpa [prefixWord, tailWord_2296277, baseEnd_2296277] using wordTrace_append hprefix tailTrace_2296277
  have hstable : (prefixWord ++ tailWord_2296277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296277).length < 2 ^ (prefixWord ++ tailWord_2296277).sum := by decide
  have hdescent : baseEnd_2296277 < baseStart_2296277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296326 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2296326 : Nat := 118140960795 + 2296326 * 2 ^ 59
def prefixEnd_2296326 : Nat := 4983230072969 + 3 ^ 40 * 2296326 * 2
def baseEnd_2296326 : Nat := 786079318277658565109597

theorem tailTrace_2296326 : CollatzResearch.WordTrace tailWord_2296326 prefixEnd_2296326 786079318277658565109597 := by
  unfold tailWord_2296326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2617309058712829940711401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55835926585873705401843221 2617309058712829940711401)
  ·
    refine ⟨1962981794034622455533551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2617309058712829940711401 1962981794034622455533551)
    ·
      refine ⟨2944472691051933683300327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1962981794034622455533551 2944472691051933683300327)
      ·
        refine ⟨4416709036577900524950491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2944472691051933683300327 4416709036577900524950491)
        ·
          refine ⟨6625063554866850787425737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4416709036577900524950491 6625063554866850787425737)
          ·
            refine ⟨4968797666150138090569303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6625063554866850787425737 4968797666150138090569303)
            ·
              refine ⟨7453196499225207135853955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4968797666150138090569303 7453196499225207135853955)
              ·
                refine ⟨11179794748837810703780933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7453196499225207135853955 11179794748837810703780933)
                ·
                  refine ⟨2096211515407089506958925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11179794748837810703780933 2096211515407089506958925)
                  ·
                    refine ⟨786079318277658565109597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2096211515407089506958925 786079318277658565109597)
                    ·
                      rfl

theorem cell22_2296326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2296326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296326 prefixEnd_2296326 := by exact prefixLift 2296326
  have htrace : WordTrace (prefixWord ++ tailWord_2296326) baseStart_2296326 baseEnd_2296326 := by
    simpa [prefixWord, tailWord_2296326, baseEnd_2296326] using wordTrace_append hprefix tailTrace_2296326
  have hstable : (prefixWord ++ tailWord_2296326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296326).length < 2 ^ (prefixWord ++ tailWord_2296326).sum := by decide
  have hdescent : baseEnd_2296326 < baseStart_2296326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296363 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 3, 4]
def baseStart_2296363 : Nat := 118140960795 + 2296363 * 2 ^ 59
def prefixEnd_2296363 : Nat := 4983230072969 + 3 ^ 40 * 2296363 * 2
def baseEnd_2296363 : Nat := 786091984133802801934483

theorem tailTrace_2296363 : CollatzResearch.WordTrace tailWord_2296363 prefixEnd_2296363 786091984133802801934483 := by
  unfold tailWord_2296363
  simp only [CollatzResearch.WordTrace]
  refine ⟨83755239379676513421861743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55836826253117675614574495 83755239379676513421861743)
  ·
    refine ⟨125632859069514770132792615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83755239379676513421861743 125632859069514770132792615)
    ·
      refine ⟨188449288604272155199188923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125632859069514770132792615 188449288604272155199188923)
      ·
        refine ⟨282673932906408232798783385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188449288604272155199188923 282673932906408232798783385)
        ·
          refine ⟨212005449679806174599087539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282673932906408232798783385 212005449679806174599087539)
          ·
            refine ⟨318008174519709261898631309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212005449679806174599087539 318008174519709261898631309)
            ·
              refine ⟨119253065444890973211986741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 318008174519709261898631309 119253065444890973211986741)
              ·
                refine ⟨11179974885458528738623757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119253065444890973211986741 11179974885458528738623757)
                ·
                  refine ⟨4192490582046948276983909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11179974885458528738623757 4192490582046948276983909)
                  ·
                    refine ⟨786091984133802801934483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4192490582046948276983909 786091984133802801934483)
                    ·
                      rfl

theorem cell22_2296363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 4].length) (baseStart_2296363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296363 prefixEnd_2296363 := by exact prefixLift 2296363
  have htrace : WordTrace (prefixWord ++ tailWord_2296363) baseStart_2296363 baseEnd_2296363 := by
    simpa [prefixWord, tailWord_2296363, baseEnd_2296363] using wordTrace_append hprefix tailTrace_2296363
  have hstable : (prefixWord ++ tailWord_2296363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296363).length < 2 ^ (prefixWord ++ tailWord_2296363).sum := by decide
  have hdescent : baseEnd_2296363 < baseStart_2296363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296388 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2296388 : Nat := 118140960795 + 2296388 * 2 ^ 59
def prefixEnd_2296388 : Nat := 4983230072969 + 3 ^ 40 * 2296388 * 2
def baseEnd_2296388 : Nat := 786100542144711070059407

theorem tailTrace_2296388 : CollatzResearch.WordTrace tailWord_2296388 prefixEnd_2296388 786100542144711070059407 := by
  unfold tailWord_2296388
  simp only [CollatzResearch.WordTrace]
  refine ⟨41878075602292971345760909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55837434136390628461014545 41878075602292971345760909)
  ·
    refine ⟨15704278350859864254660341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41878075602292971345760909 15704278350859864254660341)
    ·
      refine ⟨1472276095393112273874407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15704278350859864254660341 1472276095393112273874407)
      ·
        refine ⟨2208414143089668410811611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472276095393112273874407 2208414143089668410811611)
        ·
          refine ⟨3312621214634502616217417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208414143089668410811611 3312621214634502616217417)
          ·
            refine ⟨2484465910975876962163063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3312621214634502616217417 2484465910975876962163063)
            ·
              refine ⟨3726698866463815443244595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2484465910975876962163063 3726698866463815443244595)
              ·
                refine ⟨5590048299695723164866893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3726698866463815443244595 5590048299695723164866893)
                ·
                  refine ⟨2096268112385896186825085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5590048299695723164866893 2096268112385896186825085)
                  ·
                    refine ⟨786100542144711070059407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2096268112385896186825085 786100542144711070059407)
                    ·
                      rfl

theorem cell22_2296388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2296388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296388 prefixEnd_2296388 := by exact prefixLift 2296388
  have htrace : WordTrace (prefixWord ++ tailWord_2296388) baseStart_2296388 baseEnd_2296388 := by
    simpa [prefixWord, tailWord_2296388, baseEnd_2296388] using wordTrace_append hprefix tailTrace_2296388
  have hstable : (prefixWord ++ tailWord_2296388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296388).length < 2 ^ (prefixWord ++ tailWord_2296388).sum := by decide
  have hdescent : baseEnd_2296388 < baseStart_2296388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296395 : List Nat := [1, 1, 1, 1, 3, 1, 4, 6, 4]
def baseStart_2296395 : Nat := 118140960795 + 2296395 * 2 ^ 59
def prefixEnd_2296395 : Nat := 4983230072969 + 3 ^ 40 * 2296395 * 2
def baseEnd_2296395 : Nat := 262034312795921795044795

theorem tailTrace_2296395 : CollatzResearch.WordTrace tailWord_2296395 prefixEnd_2296395 262034312795921795044795 := by
  unfold tailWord_2296395
  simp only [CollatzResearch.WordTrace]
  refine ⟨83756406515560582887026639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55837604343707055258017759 83756406515560582887026639)
  ·
    refine ⟨125634609773340874330539959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83756406515560582887026639 125634609773340874330539959)
    ·
      refine ⟨188451914660011311495809939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125634609773340874330539959 188451914660011311495809939)
      ·
        refine ⟨282677871990016967243714909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188451914660011311495809939 282677871990016967243714909)
        ·
          refine ⟨106004201996256362716393091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282677871990016967243714909 106004201996256362716393091)
          ·
            refine ⟨159006302994384544074589637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106004201996256362716393091 159006302994384544074589637)
            ·
              refine ⟨29813681811447102013985557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159006302994384544074589637 29813681811447102013985557)
              ·
                refine ⟨1397516334911582906905573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29813681811447102013985557 1397516334911582906905573)
                ·
                  refine ⟨262034312795921795044795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1397516334911582906905573 262034312795921795044795)
                  ·
                    rfl

theorem cell22_2296395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 4].length) (baseStart_2296395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296395 prefixEnd_2296395 := by exact prefixLift 2296395
  have htrace : WordTrace (prefixWord ++ tailWord_2296395) baseStart_2296395 baseEnd_2296395 := by
    simpa [prefixWord, tailWord_2296395, baseEnd_2296395] using wordTrace_append hprefix tailTrace_2296395
  have hstable : (prefixWord ++ tailWord_2296395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296395).length < 2 ^ (prefixWord ++ tailWord_2296395).sum := by decide
  have hdescent : baseEnd_2296395 < baseStart_2296395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296408 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_2296408 : Nat := 118140960795 + 2296408 * 2 ^ 59
def prefixEnd_2296408 : Nat := 4983230072969 + 3 ^ 40 * 2296408 * 2
def baseEnd_2296408 : Nat := 786107388553437684559345

theorem tailTrace_2296408 : CollatzResearch.WordTrace tailWord_2296408 prefixEnd_2296408 786107388553437684559345 := by
  unfold tailWord_2296408
  simp only [CollatzResearch.WordTrace]
  refine ⟨41878440332256743053624939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55837920443008990738166585 41878440332256743053624939)
  ·
    refine ⟨62817660498385114580437409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41878440332256743053624939 62817660498385114580437409)
    ·
      refine ⟨47113245373788835935328057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62817660498385114580437409 47113245373788835935328057)
      ·
        refine ⟨35334934030341626951496043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47113245373788835935328057 35334934030341626951496043)
        ·
          refine ⟨53002401045512440427244065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35334934030341626951496043 53002401045512440427244065)
          ·
            refine ⟨39751800784134330320433049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53002401045512440427244065 39751800784134330320433049)
            ·
              refine ⟨29813850588100747740324787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39751800784134330320433049 29813850588100747740324787)
              ·
                refine ⟨44720775882151121610487181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29813850588100747740324787 44720775882151121610487181)
                ·
                  refine ⟨16770290955806670603932693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44720775882151121610487181 16770290955806670603932693)
                  ·
                    refine ⟨786107388553437684559345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16770290955806670603932693 786107388553437684559345)
                    ·
                      rfl

theorem cell22_2296408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_2296408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296408 prefixEnd_2296408 := by exact prefixLift 2296408
  have htrace : WordTrace (prefixWord ++ tailWord_2296408) baseStart_2296408 baseEnd_2296408 := by
    simpa [prefixWord, tailWord_2296408, baseEnd_2296408] using wordTrace_append hprefix tailTrace_2296408
  have hstable : (prefixWord ++ tailWord_2296408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296408).length < 2 ^ (prefixWord ++ tailWord_2296408).sum := by decide
  have hdescent : baseEnd_2296408 < baseStart_2296408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296472 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 3, 3]
def baseStart_2296472 : Nat := 118140960795 + 2296472 * 2 ^ 59
def prefixEnd_2296472 : Nat := 4983230072969 + 3 ^ 40 * 2296472 * 2
def baseEnd_2296472 : Nat := 786129297061362850959149

theorem tailTrace_2296472 : CollatzResearch.WordTrace tailWord_2296472 prefixEnd_2296472 786129297061362850959149 := by
  unfold tailWord_2296472
  simp only [CollatzResearch.WordTrace]
  refine ⟨41879607468140812518789835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55839476624187750025053113 41879607468140812518789835)
  ·
    refine ⟨62819411202211218778184753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41879607468140812518789835 62819411202211218778184753)
    ·
      refine ⟨47114558401658414083638565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62819411202211218778184753 47114558401658414083638565)
      ·
        refine ⟨8833979700310952640682231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47114558401658414083638565 8833979700310952640682231)
        ·
          refine ⟨13250969550466428961023347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8833979700310952640682231 13250969550466428961023347)
          ·
            refine ⟨19876454325699643441535021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13250969550466428961023347 19876454325699643441535021)
            ·
              refine ⟨7453670372137366290575633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19876454325699643441535021 7453670372137366290575633)
              ·
                refine ⟨5590252779103024717931725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7453670372137366290575633 5590252779103024717931725)
                ·
                  refine ⟨2096344792163634269224397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5590252779103024717931725 2096344792163634269224397)
                  ·
                    refine ⟨786129297061362850959149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2096344792163634269224397 786129297061362850959149)
                    ·
                      rfl

theorem cell22_2296472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_2296472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296472 prefixEnd_2296472 := by exact prefixLift 2296472
  have htrace : WordTrace (prefixWord ++ tailWord_2296472) baseStart_2296472 baseEnd_2296472 := by
    simpa [prefixWord, tailWord_2296472, baseEnd_2296472] using wordTrace_append hprefix tailTrace_2296472
  have hstable : (prefixWord ++ tailWord_2296472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296472).length < 2 ^ (prefixWord ++ tailWord_2296472).sum := by decide
  have hdescent : baseEnd_2296472 < baseStart_2296472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296474 : List Nat := [3, 1, 1, 6, 1, 1, 3, 6]
def baseStart_2296474 : Nat := 118140960795 + 2296474 * 2 ^ 59
def prefixEnd_2296474 : Nat := 4983230072969 + 3 ^ 40 * 2296474 * 2
def baseEnd_2296474 : Nat := 87347775744692834712127

theorem tailTrace_2296474 : CollatzResearch.WordTrace tailWord_2296474 prefixEnd_2296474 87347775744692834712127 := by
  unfold tailWord_2296474
  simp only [CollatzResearch.WordTrace]
  refine ⟨20939821970568594844788119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55839525254849586252768317 20939821970568594844788119)
  ·
    refine ⟨31409732955852892267182179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20939821970568594844788119 31409732955852892267182179)
    ·
      refine ⟨47114599433779338400773269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31409732955852892267182179 47114599433779338400773269)
      ·
        refine ⟨2208496848458406487536247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47114599433779338400773269 2208496848458406487536247)
        ·
          refine ⟨3312745272687609731304371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208496848458406487536247 3312745272687609731304371)
          ·
            refine ⟨4969117909031414596956557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312745272687609731304371 4969117909031414596956557)
            ·
              refine ⟨1863419215886780473858709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4969117909031414596956557 1863419215886780473858709)
              ·
                refine ⟨87347775744692834712127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1863419215886780473858709 87347775744692834712127)
                ·
                  rfl

theorem cell22_2296474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_2296474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296474 prefixEnd_2296474 := by exact prefixLift 2296474
  have htrace : WordTrace (prefixWord ++ tailWord_2296474) baseStart_2296474 baseEnd_2296474 := by
    simpa [prefixWord, tailWord_2296474, baseEnd_2296474] using wordTrace_append hprefix tailTrace_2296474
  have hstable : (prefixWord ++ tailWord_2296474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296474).length < 2 ^ (prefixWord ++ tailWord_2296474).sum := by decide
  have hdescent : baseEnd_2296474 < baseStart_2296474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296759 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 3, 3]
def baseStart_2296759 : Nat := 118140960795 + 2296759 * 2 ^ 59
def prefixEnd_2296759 : Nat := 4983230072969 + 3 ^ 40 * 2296759 * 2
def baseEnd_2296759 : Nat := 786227543026589769033269

theorem tailTrace_2296759 : CollatzResearch.WordTrace tailWord_2296759 prefixEnd_2296759 786227543026589769033269 := by
  unfold tailWord_2296759
  simp only [CollatzResearch.WordTrace]
  refine ⟨83769682686241873053277331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55846455124161248702184887 83769682686241873053277331)
  ·
    refine ⟨125654524029362809579915997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83769682686241873053277331 125654524029362809579915997)
    ·
      refine ⟨47120446511011053592468499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125654524029362809579915997 47120446511011053592468499)
      ·
        refine ⟨70680669766516580388702749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47120446511011053592468499 70680669766516580388702749)
        ·
          refine ⟨26505251162443717645763531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70680669766516580388702749 26505251162443717645763531)
          ·
            refine ⟨39757876743665576468645297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26505251162443717645763531 39757876743665576468645297)
            ·
              refine ⟨29818407557749182351483973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39757876743665576468645297 29818407557749182351483973)
              ·
                refine ⟨5590951417077971690903245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29818407557749182351483973 5590951417077971690903245)
                ·
                  refine ⟨2096606781404239384088717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5590951417077971690903245 2096606781404239384088717)
                  ·
                    refine ⟨786227543026589769033269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2096606781404239384088717 786227543026589769033269)
                    ·
                      rfl

theorem cell22_2296759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_2296759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296759 prefixEnd_2296759 := by exact prefixLift 2296759
  have htrace : WordTrace (prefixWord ++ tailWord_2296759) baseStart_2296759 baseEnd_2296759 := by
    simpa [prefixWord, tailWord_2296759, baseEnd_2296759] using wordTrace_append hprefix tailTrace_2296759
  have hstable : (prefixWord ++ tailWord_2296759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296759).length < 2 ^ (prefixWord ++ tailWord_2296759).sum := by decide
  have hdescent : baseEnd_2296759 < baseStart_2296759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296793 : List Nat := [1, 2, 1, 2, 5, 2, 1, 4, 1, 3]
def baseStart_2296793 : Nat := 118140960795 + 2296793 * 2 ^ 59
def prefixEnd_2296793 : Nat := 4983230072969 + 3 ^ 40 * 2296793 * 2
def baseEnd_2296793 : Nat := 786239181921425013683165

theorem tailTrace_2296793 : CollatzResearch.WordTrace tailWord_2296793 prefixEnd_2296793 786239181921425013683165 := by
  unfold tailWord_2296793
  simp only [CollatzResearch.WordTrace]
  refine ⟨83770922768118696860015033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55847281845412464573343355 83770922768118696860015033)
  ·
    refine ⟨62828192076089022645011275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83770922768118696860015033 62828192076089022645011275)
    ·
      refine ⟨94242288114133533967516913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62828192076089022645011275 94242288114133533967516913)
      ·
        refine ⟨70681716085600150475637685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94242288114133533967516913 70681716085600150475637685)
        ·
          refine ⟨6626410883025014107091033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70681716085600150475637685 6626410883025014107091033)
          ·
            refine ⟨4969808162268760580318275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6626410883025014107091033 4969808162268760580318275)
            ·
              refine ⟨7454712243403140870477413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4969808162268760580318275 7454712243403140870477413)
              ·
                refine ⟨1397758545638088913214515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7454712243403140870477413 1397758545638088913214515)
                ·
                  refine ⟨2096637818457133369821773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1397758545638088913214515 2096637818457133369821773)
                  ·
                    refine ⟨786239181921425013683165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2096637818457133369821773 786239181921425013683165)
                    ·
                      rfl

theorem cell22_2296793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 1, 3].length) (baseStart_2296793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296793 prefixEnd_2296793 := by exact prefixLift 2296793
  have htrace : WordTrace (prefixWord ++ tailWord_2296793) baseStart_2296793 baseEnd_2296793 := by
    simpa [prefixWord, tailWord_2296793, baseEnd_2296793] using wordTrace_append hprefix tailTrace_2296793
  have hstable : (prefixWord ++ tailWord_2296793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296793).length < 2 ^ (prefixWord ++ tailWord_2296793).sum := by decide
  have hdescent : baseEnd_2296793 < baseStart_2296793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296832 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_2296832 : Nat := 118140960795 + 2296832 * 2 ^ 59
def prefixEnd_2296832 : Nat := 4983230072969 + 3 ^ 40 * 2296832 * 2
def baseEnd_2296832 : Nat := 786252532418441911958045

theorem tailTrace_2296832 : CollatzResearch.WordTrace tailWord_2296832 prefixEnd_2296832 786252532418441911958045 := by
  unfold tailWord_2296832
  simp only [CollatzResearch.WordTrace]
  refine ⟨41886172607488703260342375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55848230143318271013789833 41886172607488703260342375)
  ·
    refine ⟨62829258911233054890513563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41886172607488703260342375 62829258911233054890513563)
    ·
      refine ⟨94243888366849582335770345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62829258911233054890513563 94243888366849582335770345)
      ·
        refine ⟨70682916275137186751827759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94243888366849582335770345 70682916275137186751827759)
        ·
          refine ⟨106024374412705780127741639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70682916275137186751827759 106024374412705780127741639)
          ·
            refine ⟨159036561619058670191612459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106024374412705780127741639 159036561619058670191612459)
            ·
              refine ⟨238554842428588005287418689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159036561619058670191612459 238554842428588005287418689)
              ·
                refine ⟨178916131821441003965564017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238554842428588005287418689 178916131821441003965564017)
                ·
                  refine ⟨134187098866080752974173013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178916131821441003965564017 134187098866080752974173013)
                  ·
                    refine ⟨786252532418441911958045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 134187098866080752974173013 786252532418441911958045)
                    ·
                      rfl

theorem cell22_2296832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_2296832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296832 prefixEnd_2296832 := by exact prefixLift 2296832
  have htrace : WordTrace (prefixWord ++ tailWord_2296832) baseStart_2296832 baseEnd_2296832 := by
    simpa [prefixWord, tailWord_2296832, baseEnd_2296832] using wordTrace_append hprefix tailTrace_2296832
  have hstable : (prefixWord ++ tailWord_2296832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296832).length < 2 ^ (prefixWord ++ tailWord_2296832).sum := by decide
  have hdescent : baseEnd_2296832 < baseStart_2296832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296847 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 2, 10]
def baseStart_2296847 : Nat := 118140960795 + 2296847 * 2 ^ 59
def prefixEnd_2296847 : Nat := 4983230072969 + 3 ^ 40 * 2296847 * 2
def baseEnd_2296847 : Nat := 786257667224986872832999

theorem tailTrace_2296847 : CollatzResearch.WordTrace tailWord_2296847 prefixEnd_2296847 786257667224986872832999 := by
  unfold tailWord_2296847
  simp only [CollatzResearch.WordTrace]
  refine ⟨83772892309923064082480795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55848594873282042721653863 83772892309923064082480795)
  ·
    refine ⟨125659338464884596123721193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83772892309923064082480795 125659338464884596123721193)
    ·
      refine ⟨94244503848663447092790895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125659338464884596123721193 94244503848663447092790895)
      ·
        refine ⟨141366755772995170639186343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94244503848663447092790895 141366755772995170639186343)
        ·
          refine ⟨212050133659492755958779515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141366755772995170639186343 212050133659492755958779515)
          ·
            refine ⟨318075200489239133938169273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212050133659492755958779515 318075200489239133938169273)
            ·
              refine ⟨238556400366929350453626955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318075200489239133938169273 238556400366929350453626955)
              ·
                refine ⟨357834600550394025680440433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238556400366929350453626955 357834600550394025680440433)
                ·
                  refine ⟨268375950412795519260330325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357834600550394025680440433 268375950412795519260330325)
                  ·
                    refine ⟨786257667224986872832999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 268375950412795519260330325 786257667224986872832999)
                    ·
                      rfl

theorem cell22_2296847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_2296847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296847 prefixEnd_2296847 := by exact prefixLift 2296847
  have htrace : WordTrace (prefixWord ++ tailWord_2296847) baseStart_2296847 baseEnd_2296847 := by
    simpa [prefixWord, tailWord_2296847, baseEnd_2296847] using wordTrace_append hprefix tailTrace_2296847
  have hstable : (prefixWord ++ tailWord_2296847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296847).length < 2 ^ (prefixWord ++ tailWord_2296847).sum := by decide
  have hdescent : baseEnd_2296847 < baseStart_2296847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296866 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2296866 : Nat := 118140960795 + 2296866 * 2 ^ 59
def prefixEnd_2296866 : Nat := 4983230072969 + 3 ^ 40 * 2296866 * 2
def baseEnd_2296866 : Nat := 786264171313277156607941

theorem tailTrace_2296866 : CollatzResearch.WordTrace tailWord_2296866 prefixEnd_2296866 786264171313277156607941 := by
  unfold tailWord_2296866
  simp only [CollatzResearch.WordTrace]
  refine ⟨20943396324213557581855613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55849056864569486884948301 20943396324213557581855613)
  ·
    refine ⟨7853773621580084093195855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20943396324213557581855613 7853773621580084093195855)
    ·
      refine ⟨11780660432370126139793783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7853773621580084093195855 11780660432370126139793783)
      ·
        refine ⟨17670990648555189209690675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11780660432370126139793783 17670990648555189209690675)
        ·
          refine ⟨26506485972832783814536013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17670990648555189209690675 26506485972832783814536013)
          ·
            refine ⟨9939932239812293930451005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26506485972832783814536013 9939932239812293930451005)
            ·
              refine ⟨3727474589929610223919127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9939932239812293930451005 3727474589929610223919127)
              ·
                refine ⟨5591211884894415335878691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3727474589929610223919127 5591211884894415335878691)
                ·
                  refine ⟨8386817827341623003818037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5591211884894415335878691 8386817827341623003818037)
                  ·
                    refine ⟨786264171313277156607941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8386817827341623003818037 786264171313277156607941)
                    ·
                      rfl

theorem cell22_2296866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2296866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296866 prefixEnd_2296866 := by exact prefixLift 2296866
  have htrace : WordTrace (prefixWord ++ tailWord_2296866) baseStart_2296866 baseEnd_2296866 := by
    simpa [prefixWord, tailWord_2296866, baseEnd_2296866] using wordTrace_append hprefix tailTrace_2296866
  have hstable : (prefixWord ++ tailWord_2296866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296866).length < 2 ^ (prefixWord ++ tailWord_2296866).sum := by decide
  have hdescent : baseEnd_2296866 < baseStart_2296866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296902 : List Nat := [6, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_2296902 : Nat := 118140960795 + 2296902 * 2 ^ 59
def prefixEnd_2296902 : Nat := 4983230072969 + 3 ^ 40 * 2296902 * 2
def baseEnd_2296902 : Nat := 262092164949661687569277

theorem tailTrace_2296902 : CollatzResearch.WordTrace tailWord_2296902 prefixEnd_2296902 262092164949661687569277 := by
  unfold tailWord_2296902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2617965572647619014866655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55849932216482538983821973 2617965572647619014866655)
  ·
    refine ⟨3926948358971428522299983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2617965572647619014866655 3926948358971428522299983)
    ·
      refine ⟨5890422538457142783449975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3926948358971428522299983 5890422538457142783449975)
      ·
        refine ⟨8835633807685714175174963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5890422538457142783449975 8835633807685714175174963)
        ·
          refine ⟨13253450711528571262762445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8835633807685714175174963 13253450711528571262762445)
          ·
            refine ⟨4970044016823214223535917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13253450711528571262762445 4970044016823214223535917)
            ·
              refine ⟨1863766506308705333825969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4970044016823214223535917 1863766506308705333825969)
              ·
                refine ⟨1397824879731529000369477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1863766506308705333825969 1397824879731529000369477)
                ·
                  refine ⟨262092164949661687569277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1397824879731529000369477 262092164949661687569277)
                  ·
                    rfl

theorem cell22_2296902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_2296902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296902 prefixEnd_2296902 := by exact prefixLift 2296902
  have htrace : WordTrace (prefixWord ++ tailWord_2296902) baseStart_2296902 baseEnd_2296902 := by
    simpa [prefixWord, tailWord_2296902, baseEnd_2296902] using wordTrace_append hprefix tailTrace_2296902
  have hstable : (prefixWord ++ tailWord_2296902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296902).length < 2 ^ (prefixWord ++ tailWord_2296902).sum := by decide
  have hdescent : baseEnd_2296902 < baseStart_2296902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296986 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_2296986 : Nat := 118140960795 + 2296986 * 2 ^ 59
def prefixEnd_2296986 : Nat := 4983230072969 + 3 ^ 40 * 2296986 * 2
def baseEnd_2296986 : Nat := 262101749921878947869191

theorem tailTrace_2296986 : CollatzResearch.WordTrace tailWord_2296986 prefixEnd_2296986 262101749921878947869191 := by
  unfold tailWord_2296986
  simp only [CollatzResearch.WordTrace]
  refine ⟨20944490514104872705447703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55851974704279660547860541 20944490514104872705447703)
  ·
    refine ⟨31416735771157309058171555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20944490514104872705447703 31416735771157309058171555)
    ·
      refine ⟨47125103656735963587257333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31416735771157309058171555 47125103656735963587257333)
      ·
        refine ⟨4417978467818996586305375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47125103656735963587257333 4417978467818996586305375)
        ·
          refine ⟨6626967701728494879458063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4417978467818996586305375 6626967701728494879458063)
          ·
            refine ⟨9940451552592742319187095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6626967701728494879458063 9940451552592742319187095)
            ·
              refine ⟨14910677328889113478780643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9940451552592742319187095 14910677328889113478780643)
              ·
                refine ⟨22366015993333670218170965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14910677328889113478780643 22366015993333670218170965)
                ·
                  refine ⟨262101749921878947869191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22366015993333670218170965 262101749921878947869191)
                  ·
                    rfl

theorem cell22_2296986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_2296986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2296986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2296986 prefixEnd_2296986 := by exact prefixLift 2296986
  have htrace : WordTrace (prefixWord ++ tailWord_2296986) baseStart_2296986 baseEnd_2296986 := by
    simpa [prefixWord, tailWord_2296986, baseEnd_2296986] using wordTrace_append hprefix tailTrace_2296986
  have hstable : (prefixWord ++ tailWord_2296986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296986).length < 2 ^ (prefixWord ++ tailWord_2296986).sum := by decide
  have hdescent : baseEnd_2296986 < baseStart_2296986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297005 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2297005 : Nat := 118140960795 + 2297005 * 2 ^ 59
def prefixEnd_2297005 : Nat := 4983230072969 + 3 ^ 40 * 2297005 * 2
def baseEnd_2297005 : Nat := 786311753853927127382515

theorem tailTrace_2297005 : CollatzResearch.WordTrace tailWord_2297005 prefixEnd_2297005 786311753853927127382515 := by
  unfold tailWord_2297005
  simp only [CollatzResearch.WordTrace]
  refine ⟨83778655043350657066732469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55852436695567104711154979 83778655043350657066732469)
  ·
    refine ⟨7854248910314124100006169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83778655043350657066732469 7854248910314124100006169)
    ·
      refine ⟨5890686682735593075004627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7854248910314124100006169 5890686682735593075004627)
      ·
        refine ⟨8836030024103389612506941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5890686682735593075004627 8836030024103389612506941)
        ·
          refine ⟨3313511259038771104690103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8836030024103389612506941 3313511259038771104690103)
          ·
            refine ⟨4970266888558156657035155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313511259038771104690103 4970266888558156657035155)
            ·
              refine ⟨7455400332837234985552733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4970266888558156657035155 7455400332837234985552733)
              ·
                refine ⟨2795775124813963119582275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7455400332837234985552733 2795775124813963119582275)
                ·
                  refine ⟨4193662687220944679373413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795775124813963119582275 4193662687220944679373413)
                  ·
                    refine ⟨786311753853927127382515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4193662687220944679373413 786311753853927127382515)
                    ·
                      rfl

theorem cell22_2297005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2297005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297005 prefixEnd_2297005 := by exact prefixLift 2297005
  have htrace : WordTrace (prefixWord ++ tailWord_2297005) baseStart_2297005 baseEnd_2297005 := by
    simpa [prefixWord, tailWord_2297005, baseEnd_2297005] using wordTrace_append hprefix tailTrace_2297005
  have hstable : (prefixWord ++ tailWord_2297005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297005).length < 2 ^ (prefixWord ++ tailWord_2297005).sum := by decide
  have hdescent : baseEnd_2297005 < baseStart_2297005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297136 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_2297136 : Nat := 118140960795 + 2297136 * 2 ^ 59
def prefixEnd_2297136 : Nat := 4983230072969 + 3 ^ 40 * 2297136 * 2
def baseEnd_2297136 : Nat := 786356597831086452357113

theorem tailTrace_2297136 : CollatzResearch.WordTrace tailWord_2297136 prefixEnd_2297136 786356597831086452357113 := by
  unfold tailWord_2297136
  simp only [CollatzResearch.WordTrace]
  refine ⟨41891716502938033219875631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55855622003917377626500841 41891716502938033219875631)
  ·
    refine ⟨62837574754407049829813447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41891716502938033219875631 62837574754407049829813447)
    ·
      refine ⟨94256362131610574744720171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62837574754407049829813447 94256362131610574744720171)
      ·
        refine ⟨141384543197415862117080257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94256362131610574744720171 141384543197415862117080257)
        ·
          refine ⟨106038407398061896587810193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141384543197415862117080257 106038407398061896587810193)
          ·
            refine ⟨79528805548546422440857645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106038407398061896587810193 79528805548546422440857645)
            ·
              refine ⟨29823302080704908415321617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79528805548546422440857645 29823302080704908415321617)
              ·
                refine ⟨22367476560528681311491213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29823302080704908415321617 22367476560528681311491213)
                ·
                  refine ⟨8387803710198255491809205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22367476560528681311491213 8387803710198255491809205)
                  ·
                    refine ⟨786356597831086452357113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8387803710198255491809205 786356597831086452357113)
                    ·
                      rfl

theorem cell22_2297136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_2297136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297136 prefixEnd_2297136 := by exact prefixLift 2297136
  have htrace : WordTrace (prefixWord ++ tailWord_2297136) baseStart_2297136 baseEnd_2297136 := by
    simpa [prefixWord, tailWord_2297136, baseEnd_2297136] using wordTrace_append hprefix tailTrace_2297136
  have hstable : (prefixWord ++ tailWord_2297136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297136).length < 2 ^ (prefixWord ++ tailWord_2297136).sum := by decide
  have hdescent : baseEnd_2297136 < baseStart_2297136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297142 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_2297142 : Nat := 118140960795 + 2297142 * 2 ^ 59
def prefixEnd_2297142 : Nat := 4983230072969 + 3 ^ 40 * 2297142 * 2
def baseEnd_2297142 : Nat := 786358651753704436707095

theorem tailTrace_2297142 : CollatzResearch.WordTrace tailWord_2297142 prefixEnd_2297142 786358651753704436707095 := by
  unfold tailWord_2297142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5236478240240895591529355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55855767895902886309646453 5236478240240895591529355)
  ·
    refine ⟨7854717360361343387294033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5236478240240895591529355 7854717360361343387294033)
    ·
      refine ⟨5891038020271007540470525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7854717360361343387294033 5891038020271007540470525)
      ·
        refine ⟨2209139257601627827676447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5891038020271007540470525 2209139257601627827676447)
        ·
          refine ⟨3313708886402441741514671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2209139257601627827676447 3313708886402441741514671)
          ·
            refine ⟨4970563329603662612272007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313708886402441741514671 4970563329603662612272007)
            ·
              refine ⟨7455844994405493918408011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4970563329603662612272007 7455844994405493918408011)
              ·
                refine ⟨11183767491608240877612017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7455844994405493918408011 11183767491608240877612017)
                ·
                  refine ⟨8387825618706180658209013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11183767491608240877612017 8387825618706180658209013)
                  ·
                    refine ⟨786358651753704436707095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8387825618706180658209013 786358651753704436707095)
                    ·
                      rfl

theorem cell22_2297142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_2297142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297142 prefixEnd_2297142 := by exact prefixLift 2297142
  have htrace : WordTrace (prefixWord ++ tailWord_2297142) baseStart_2297142 baseEnd_2297142 := by
    simpa [prefixWord, tailWord_2297142, baseEnd_2297142] using wordTrace_append hprefix tailTrace_2297142
  have hstable : (prefixWord ++ tailWord_2297142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297142).length < 2 ^ (prefixWord ++ tailWord_2297142).sum := by decide
  have hdescent : baseEnd_2297142 < baseStart_2297142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297187 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 2, 3]
def baseStart_2297187 : Nat := 118140960795 + 2297187 * 2 ^ 59
def prefixEnd_2297187 : Nat := 4983230072969 + 3 ^ 40 * 2297187 * 2
def baseEnd_2297187 : Nat := 786374056173339319331957

theorem tailTrace_2297187 : CollatzResearch.WordTrace tailWord_2297187 prefixEnd_2297187 786374056173339319331957 := by
  unfold tailWord_2297187
  simp only [CollatzResearch.WordTrace]
  refine ⟨83785293128691302149857815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55856862085794201433238543 83785293128691302149857815)
  ·
    refine ⟨125677939693036953224786723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83785293128691302149857815 125677939693036953224786723)
    ·
      refine ⟨188516909539555429837180085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125677939693036953224786723 188516909539555429837180085)
      ·
        refine ⟨17673460269333321547235633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188516909539555429837180085 17673460269333321547235633)
        ·
          refine ⟨13255095201999991160426725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17673460269333321547235633 13255095201999991160426725)
          ·
            refine ⟨2485330350374998342580011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13255095201999991160426725 2485330350374998342580011)
            ·
              refine ⟨3727995525562497513870017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485330350374998342580011 3727995525562497513870017)
              ·
                refine ⟨2795996644171873135402513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3727995525562497513870017 2795996644171873135402513)
                ·
                  refine ⟨2096997483128904851551885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2795996644171873135402513 2096997483128904851551885)
                  ·
                    refine ⟨786374056173339319331957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2096997483128904851551885 786374056173339319331957)
                    ·
                      rfl

theorem cell22_2297187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 3].length) (baseStart_2297187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297187 prefixEnd_2297187 := by exact prefixLift 2297187
  have htrace : WordTrace (prefixWord ++ tailWord_2297187) baseStart_2297187 baseEnd_2297187 := by
    simpa [prefixWord, tailWord_2297187, baseEnd_2297187] using wordTrace_append hprefix tailTrace_2297187
  have hstable : (prefixWord ++ tailWord_2297187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297187).length < 2 ^ (prefixWord ++ tailWord_2297187).sum := by decide
  have hdescent : baseEnd_2297187 < baseStart_2297187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297217 : List Nat := [1, 2, 4, 3, 2, 2, 2, 6]
def baseStart_2297217 : Nat := 118140960795 + 2297217 * 2 ^ 59
def prefixEnd_2297217 : Nat := 4983230072969 + 3 ^ 40 * 2297217 * 2
def baseEnd_2297217 : Nat := 87376036198492137897985

theorem tailTrace_2297217 : CollatzResearch.WordTrace tailWord_2297217 prefixEnd_2297217 87376036198492137897985 := by
  unfold tailWord_2297217
  simp only [CollatzResearch.WordTrace]
  refine ⟨83786387318582617273449905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55857591545721744848966603 83786387318582617273449905)
  ·
    refine ⟨62839790488936962955087429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83786387318582617273449905 62839790488936962955087429)
    ·
      refine ⟨11782460716675680554078893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62839790488936962955087429 11782460716675680554078893)
      ·
        refine ⟨4418422768753380207779585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11782460716675680554078893 4418422768753380207779585)
        ·
          refine ⟨3313817076565035155834689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4418422768753380207779585 3313817076565035155834689)
          ·
            refine ⟨2485362807423776366876017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3313817076565035155834689 2485362807423776366876017)
            ·
              refine ⟨1864022105567832275157013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2485362807423776366876017 1864022105567832275157013)
              ·
                refine ⟨87376036198492137897985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1864022105567832275157013 87376036198492137897985)
                ·
                  rfl

theorem cell22_2297217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 6].length) (baseStart_2297217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297217 prefixEnd_2297217 := by exact prefixLift 2297217
  have htrace : WordTrace (prefixWord ++ tailWord_2297217) baseStart_2297217 baseEnd_2297217 := by
    simpa [prefixWord, tailWord_2297217, baseEnd_2297217] using wordTrace_append hprefix tailTrace_2297217
  have hstable : (prefixWord ++ tailWord_2297217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297217).length < 2 ^ (prefixWord ++ tailWord_2297217).sum := by decide
  have hdescent : baseEnd_2297217 < baseStart_2297217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297322 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_2297322 : Nat := 118140960795 + 2297322 * 2 ^ 59
def prefixEnd_2297322 : Nat := 4983230072969 + 3 ^ 40 * 2297322 * 2
def baseEnd_2297322 : Nat := 786420269432243967206543

theorem tailTrace_2297322 : CollatzResearch.WordTrace tailWord_2297322 prefixEnd_2297322 786420269432243967206543 := by
  unfold tailWord_2297322
  simp only [CollatzResearch.WordTrace]
  refine ⟨20947554245800555051505555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55860144655468146804014813 20947554245800555051505555)
  ·
    refine ⟨31421331368700832577258333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20947554245800555051505555 31421331368700832577258333)
    ·
      refine ⟨11782999263262812216471875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31421331368700832577258333 11782999263262812216471875)
      ·
        refine ⟨17674498894894218324707813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11782999263262812216471875 17674498894894218324707813)
        ·
          refine ⟨3313968542792665935882715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17674498894894218324707813 3313968542792665935882715)
          ·
            refine ⟨4970952814188998903824073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313968542792665935882715 4970952814188998903824073)
            ·
              refine ⟨3728214610641749177868055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4970952814188998903824073 3728214610641749177868055)
              ·
                refine ⟨5592321915962623766802083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3728214610641749177868055 5592321915962623766802083)
                ·
                  refine ⟨8388482873943935650203125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5592321915962623766802083 8388482873943935650203125)
                  ·
                    refine ⟨786420269432243967206543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8388482873943935650203125 786420269432243967206543)
                    ·
                      rfl

theorem cell22_2297322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_2297322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297322 prefixEnd_2297322 := by exact prefixLift 2297322
  have htrace : WordTrace (prefixWord ++ tailWord_2297322) baseStart_2297322 baseEnd_2297322 := by
    simpa [prefixWord, tailWord_2297322, baseEnd_2297322] using wordTrace_append hprefix tailTrace_2297322
  have hstable : (prefixWord ++ tailWord_2297322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297322).length < 2 ^ (prefixWord ++ tailWord_2297322).sum := by decide
  have hdescent : baseEnd_2297322 < baseStart_2297322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297356 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 2, 3]
def baseStart_2297356 : Nat := 118140960795 + 2297356 * 2 ^ 59
def prefixEnd_2297356 : Nat := 4983230072969 + 3 ^ 40 * 2297356 * 2
def baseEnd_2297356 : Nat := 786431908327079211856439

theorem tailTrace_2297356 : CollatzResearch.WordTrace tailWord_2297356 prefixEnd_2297356 786431908327079211856439 := by
  unfold tailWord_2297356
  simp only [CollatzResearch.WordTrace]
  refine ⟨41895728532539522006379961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55860971376719362675173281 41895728532539522006379961)
  ·
    refine ⟨31421796399404641504784971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41895728532539522006379961 31421796399404641504784971)
    ·
      refine ⟨47132694599106962257177457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31421796399404641504784971 47132694599106962257177457)
      ·
        refine ⟨35349520949330221692883093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47132694599106962257177457 35349520949330221692883093)
        ·
          refine ⟨1657008794499854141853895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35349520949330221692883093 1657008794499854141853895)
          ·
            refine ⟨2485513191749781212780843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657008794499854141853895 2485513191749781212780843)
            ·
              refine ⟨3728269787624671819171265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485513191749781212780843 3728269787624671819171265)
              ·
                refine ⟨2796202340718503864378449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3728269787624671819171265 2796202340718503864378449)
                ·
                  refine ⟨2097151755538877898283837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2796202340718503864378449 2097151755538877898283837)
                  ·
                    refine ⟨786431908327079211856439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2097151755538877898283837 786431908327079211856439)
                    ·
                      rfl

theorem cell22_2297356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_2297356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297356 prefixEnd_2297356 := by exact prefixLift 2297356
  have htrace : WordTrace (prefixWord ++ tailWord_2297356) baseStart_2297356 baseEnd_2297356 := by
    simpa [prefixWord, tailWord_2297356, baseEnd_2297356] using wordTrace_append hprefix tailTrace_2297356
  have hstable : (prefixWord ++ tailWord_2297356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297356).length < 2 ^ (prefixWord ++ tailWord_2297356).sum := by decide
  have hdescent : baseEnd_2297356 < baseStart_2297356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297401 : List Nat := [1, 2, 1, 5, 1, 4, 1, 3, 1, 3]
def baseStart_2297401 : Nat := 118140960795 + 2297401 * 2 ^ 59
def prefixEnd_2297401 : Nat := 4983230072969 + 3 ^ 40 * 2297401 * 2
def baseEnd_2297401 : Nat := 786447312746714094481301

theorem tailTrace_2297401 : CollatzResearch.WordTrace tailWord_2297401 prefixEnd_2297401 786447312746714094481301 := by
  unfold tailWord_2297401
  simp only [CollatzResearch.WordTrace]
  refine ⟨83793098349916016698148057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55862065566610677798765371 83793098349916016698148057)
  ·
    refine ⟨62844823762437012523611043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83793098349916016698148057 62844823762437012523611043)
    ·
      refine ⟨94267235643655518785416565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62844823762437012523611043 94267235643655518785416565)
      ·
        refine ⟨8837553341592704886132803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94267235643655518785416565 8837553341592704886132803)
        ·
          refine ⟨13256330012389057329199205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8837553341592704886132803 13256330012389057329199205)
          ·
            refine ⟨2485561877322948249224851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13256330012389057329199205 2485561877322948249224851)
            ·
              refine ⟨3728342815984422373837277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485561877322948249224851 3728342815984422373837277)
              ·
                refine ⟨1398128555994158390188979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3728342815984422373837277 1398128555994158390188979)
                ·
                  refine ⟨2097192833991237585283469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398128555994158390188979 2097192833991237585283469)
                  ·
                    refine ⟨786447312746714094481301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2097192833991237585283469 786447312746714094481301)
                    ·
                      rfl

theorem cell22_2297401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 1, 3].length) (baseStart_2297401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297401 prefixEnd_2297401 := by exact prefixLift 2297401
  have htrace : WordTrace (prefixWord ++ tailWord_2297401) baseStart_2297401 baseEnd_2297401 := by
    simpa [prefixWord, tailWord_2297401, baseEnd_2297401] using wordTrace_append hprefix tailTrace_2297401
  have hstable : (prefixWord ++ tailWord_2297401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297401).length < 2 ^ (prefixWord ++ tailWord_2297401).sum := by decide
  have hdescent : baseEnd_2297401 < baseStart_2297401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297440 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_2297440 : Nat := 118140960795 + 2297440 * 2 ^ 59
def prefixEnd_2297440 : Nat := 4983230072969 + 3 ^ 40 * 2297440 * 2
def baseEnd_2297440 : Nat := 786460663243730992756181

theorem tailTrace_2297440 : CollatzResearch.WordTrace tailWord_2297440 prefixEnd_2297440 786460663243730992756181 := by
  unfold tailWord_2297440
  simp only [CollatzResearch.WordTrace]
  refine ⟨41897260398387363179408887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55863013864516484239211849 41897260398387363179408887)
  ·
    refine ⟨62845890597581044769113331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41897260398387363179408887 62845890597581044769113331)
    ·
      refine ⟨94268835896371567153669997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62845890597581044769113331 94268835896371567153669997)
      ·
        refine ⟨35350813461139337682626249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94268835896371567153669997 35350813461139337682626249)
        ·
          refine ⟨26513110095854503261969687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35350813461139337682626249 26513110095854503261969687)
          ·
            refine ⟨39769665143781754892954531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26513110095854503261969687 39769665143781754892954531)
            ·
              refine ⟨59654497715672632339431797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39769665143781754892954531 59654497715672632339431797)
              ·
                refine ⟨5592609160844309281821731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59654497715672632339431797 5592609160844309281821731)
                ·
                  refine ⟨8388913741266463922732597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5592609160844309281821731 8388913741266463922732597)
                  ·
                    refine ⟨786460663243730992756181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8388913741266463922732597 786460663243730992756181)
                    ·
                      rfl

theorem cell22_2297440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_2297440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297440 prefixEnd_2297440 := by exact prefixLift 2297440
  have htrace : WordTrace (prefixWord ++ tailWord_2297440) baseStart_2297440 baseEnd_2297440 := by
    simpa [prefixWord, tailWord_2297440, baseEnd_2297440] using wordTrace_append hprefix tailTrace_2297440
  have hstable : (prefixWord ++ tailWord_2297440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297440).length < 2 ^ (prefixWord ++ tailWord_2297440).sum := by decide
  have hdescent : baseEnd_2297440 < baseStart_2297440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297444 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_2297444 : Nat := 118140960795 + 2297444 * 2 ^ 59
def prefixEnd_2297444 : Nat := 4983230072969 + 3 ^ 40 * 2297444 * 2
def baseEnd_2297444 : Nat := 786462032525476315656169

theorem tailTrace_2297444 : CollatzResearch.WordTrace tailWord_2297444 prefixEnd_2297444 786462032525476315656169 := by
  unfold tailWord_2297444
  simp only [CollatzResearch.WordTrace]
  refine ⟨41897333344380117520981693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55863111125840156694642257 41897333344380117520981693)
  ·
    refine ⟨15711500004142544070368135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41897333344380117520981693 15711500004142544070368135)
    ·
      refine ⟨23567250006213816105552203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15711500004142544070368135 23567250006213816105552203)
      ·
        refine ⟨35350875009320724158328305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23567250006213816105552203 35350875009320724158328305)
        ·
          refine ⟨26513156256990543118746229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35350875009320724158328305 26513156256990543118746229)
          ·
            refine ⟨2485608399092863417382459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26513156256990543118746229 2485608399092863417382459)
            ·
              refine ⟨3728412598639295126073689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485608399092863417382459 3728412598639295126073689)
              ·
                refine ⟨2796309448979471344555267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3728412598639295126073689 2796309448979471344555267)
                ·
                  refine ⟨4194464173469207016832901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796309448979471344555267 4194464173469207016832901)
                  ·
                    refine ⟨786462032525476315656169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4194464173469207016832901 786462032525476315656169)
                    ·
                      rfl

theorem cell22_2297444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_2297444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297444 prefixEnd_2297444 := by exact prefixLift 2297444
  have htrace : WordTrace (prefixWord ++ tailWord_2297444) baseStart_2297444 baseEnd_2297444 := by
    simpa [prefixWord, tailWord_2297444, baseEnd_2297444] using wordTrace_append hprefix tailTrace_2297444
  have hstable : (prefixWord ++ tailWord_2297444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297444).length < 2 ^ (prefixWord ++ tailWord_2297444).sum := by decide
  have hdescent : baseEnd_2297444 < baseStart_2297444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297461 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2297461 : Nat := 118140960795 + 2297461 * 2 ^ 59
def prefixEnd_2297461 : Nat := 4983230072969 + 3 ^ 40 * 2297461 * 2
def baseEnd_2297461 : Nat := 786467851972893937981117

theorem tailTrace_2297461 : CollatzResearch.WordTrace tailWord_2297461 prefixEnd_2297461 786467851972893937981117 := by
  unfold tailWord_2297461
  simp only [CollatzResearch.WordTrace]
  refine ⟨83795286729698646945332237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55863524486465764630221491 83795286729698646945332237)
  ·
    refine ⟨31423232523636992604499589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83795286729698646945332237 31423232523636992604499589)
    ·
      refine ⟨5891856098181936113343673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31423232523636992604499589 5891856098181936113343673)
      ·
        refine ⟨4418892073636452085007755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5891856098181936113343673 4418892073636452085007755)
        ·
          refine ⟨6628338110454678127511633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4418892073636452085007755 6628338110454678127511633)
          ·
            refine ⟨4971253582841008595633725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6628338110454678127511633 4971253582841008595633725)
            ·
              refine ⟨1864220093565378223362647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4971253582841008595633725 1864220093565378223362647)
              ·
                refine ⟨2796330140348067335043971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864220093565378223362647 2796330140348067335043971)
                ·
                  refine ⟨4194495210522101002565957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796330140348067335043971 4194495210522101002565957)
                  ·
                    refine ⟨786467851972893937981117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4194495210522101002565957 786467851972893937981117)
                    ·
                      rfl

theorem cell22_2297461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2297461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297461 prefixEnd_2297461 := by exact prefixLift 2297461
  have htrace : WordTrace (prefixWord ++ tailWord_2297461) baseStart_2297461 baseEnd_2297461 := by
    simpa [prefixWord, tailWord_2297461, baseEnd_2297461] using wordTrace_append hprefix tailTrace_2297461
  have hstable : (prefixWord ++ tailWord_2297461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297461).length < 2 ^ (prefixWord ++ tailWord_2297461).sum := by decide
  have hdescent : baseEnd_2297461 < baseStart_2297461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297512 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2297512 : Nat := 118140960795 + 2297512 * 2 ^ 59
def prefixEnd_2297512 : Nat := 4983230072969 + 3 ^ 40 * 2297512 * 2
def baseEnd_2297512 : Nat := 786485310315146804955961

theorem tailTrace_2297512 : CollatzResearch.WordTrace tailWord_2297512 prefixEnd_2297512 786485310315146804955961 := by
  unfold tailWord_2297512
  simp only [CollatzResearch.WordTrace]
  refine ⟨41898573426256941327719395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55864764568342588436959193 41898573426256941327719395)
  ·
    refine ⟨62847860139385411991579093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41898573426256941327719395 62847860139385411991579093)
    ·
      refine ⟨1472996722016845593552635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 62847860139385411991579093 1472996722016845593552635)
      ·
        refine ⟨2209495083025268390328953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472996722016845593552635 2209495083025268390328953)
        ·
          refine ⟨1657121312268951292746715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2209495083025268390328953 1657121312268951292746715)
          ·
            refine ⟨2485681968403426939120073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657121312268951292746715 2485681968403426939120073)
            ·
              refine ⟨1864261476302570204340055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2485681968403426939120073 1864261476302570204340055)
              ·
                refine ⟨2796392214453855306510083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864261476302570204340055 2796392214453855306510083)
                ·
                  refine ⟨4194588321680782959765125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796392214453855306510083 4194588321680782959765125)
                  ·
                    refine ⟨786485310315146804955961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4194588321680782959765125 786485310315146804955961)
                    ·
                      rfl

theorem cell22_2297512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2297512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297512 prefixEnd_2297512 := by exact prefixLift 2297512
  have htrace : WordTrace (prefixWord ++ tailWord_2297512) baseStart_2297512 baseEnd_2297512 := by
    simpa [prefixWord, tailWord_2297512, baseEnd_2297512] using wordTrace_append hprefix tailTrace_2297512
  have hstable : (prefixWord ++ tailWord_2297512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297512).length < 2 ^ (prefixWord ++ tailWord_2297512).sum := by decide
  have hdescent : baseEnd_2297512 < baseStart_2297512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297532 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 7]
def baseStart_2297532 : Nat := 118140960795 + 2297532 * 2 ^ 59
def prefixEnd_2297532 : Nat := 4983230072969 + 3 ^ 40 * 2297532 * 2
def baseEnd_2297532 : Nat := 262164052241291139818633

theorem tailTrace_2297532 : CollatzResearch.WordTrace tailWord_2297532 prefixEnd_2297532 262164052241291139818633 := by
  unfold tailWord_2297532
  simp only [CollatzResearch.WordTrace]
  refine ⟨41898938156220713035583425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55865250874960950714111233 41898938156220713035583425)
  ·
    refine ⟨31424203617165534776687569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41898938156220713035583425 31424203617165534776687569)
    ·
      refine ⟨23568152712874151082515677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31424203617165534776687569 23568152712874151082515677)
      ·
        refine ⟨8838057267327806655943379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23568152712874151082515677 8838057267327806655943379)
        ·
          refine ⟨13257085900991709983915069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8838057267327806655943379 13257085900991709983915069)
          ·
            refine ⟨4971407212871891243968151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13257085900991709983915069 4971407212871891243968151)
            ·
              refine ⟨7457110819307836865952227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4971407212871891243968151 7457110819307836865952227)
              ·
                refine ⟨11185666228961755298928341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7457110819307836865952227 11185666228961755298928341)
                ·
                  refine ⟨262164052241291139818633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11185666228961755298928341 262164052241291139818633)
                  ·
                    rfl

theorem cell22_2297532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_2297532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297532 prefixEnd_2297532 := by exact prefixLift 2297532
  have htrace : WordTrace (prefixWord ++ tailWord_2297532) baseStart_2297532 baseEnd_2297532 := by
    simpa [prefixWord, tailWord_2297532, baseEnd_2297532] using wordTrace_append hprefix tailTrace_2297532
  have hstable : (prefixWord ++ tailWord_2297532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297532).length < 2 ^ (prefixWord ++ tailWord_2297532).sum := by decide
  have hdescent : baseEnd_2297532 < baseStart_2297532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297731 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 1, 4]
def baseStart_2297731 : Nat := 118140960795 + 2297731 * 2 ^ 59
def prefixEnd_2297731 : Nat := 4983230072969 + 3 ^ 40 * 2297731 * 2
def baseEnd_2297731 : Nat := 786560278490703233730289

theorem tailTrace_2297731 : CollatzResearch.WordTrace tailWord_2297731 prefixEnd_2297731 786560278490703233730289 := by
  unfold tailWord_2297731
  simp only [CollatzResearch.WordTrace]
  refine ⟨83805134438720483057661047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55870089625813655371774031 83805134438720483057661047)
  ·
    refine ⟨125707701658080724586491571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83805134438720483057661047 125707701658080724586491571)
    ·
      refine ⟨188561552487121086879737357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125707701658080724586491571 188561552487121086879737357)
      ·
        refine ⟨70710582182670407579901509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188561552487121086879737357 70710582182670407579901509)
        ·
          refine ⟨13258234159250701421231533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70710582182670407579901509 13258234159250701421231533)
          ·
            refine ⟨4971837809719013032961825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13258234159250701421231533 4971837809719013032961825)
            ·
              refine ⟨3728878357289259774721369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4971837809719013032961825 3728878357289259774721369)
              ·
                refine ⟨2796658767966944831041027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3728878357289259774721369 2796658767966944831041027)
                ·
                  refine ⟨4194988151950417246561541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796658767966944831041027 4194988151950417246561541)
                  ·
                    refine ⟨786560278490703233730289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4194988151950417246561541 786560278490703233730289)
                    ·
                      rfl

theorem cell22_2297731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 4].length) (baseStart_2297731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297731 prefixEnd_2297731 := by exact prefixLift 2297731
  have htrace : WordTrace (prefixWord ++ tailWord_2297731) baseStart_2297731 baseEnd_2297731 := by
    simpa [prefixWord, tailWord_2297731, baseEnd_2297731] using wordTrace_append hprefix tailTrace_2297731
  have hstable : (prefixWord ++ tailWord_2297731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297731).length < 2 ^ (prefixWord ++ tailWord_2297731).sum := by decide
  have hdescent : baseEnd_2297731 < baseStart_2297731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297744 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 4, 3]
def baseStart_2297744 : Nat := 118140960795 + 2297744 * 2 ^ 59
def prefixEnd_2297744 : Nat := 4983230072969 + 3 ^ 40 * 2297744 * 2
def baseEnd_2297744 : Nat := 786564728656375533155249

theorem tailTrace_2297744 : CollatzResearch.WordTrace tailWord_2297744 prefixEnd_2297744 786564728656375533155249 := by
  unfold tailWord_2297744
  simp only [CollatzResearch.WordTrace]
  refine ⟨41902804293836693138942143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55870405725115590851922857 41902804293836693138942143)
  ·
    refine ⟨62854206440755039708413215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41902804293836693138942143 62854206440755039708413215)
    ·
      refine ⟨94281309661132559562619823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62854206440755039708413215 94281309661132559562619823)
      ·
        refine ⟨141421964491698839343929735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94281309661132559562619823 141421964491698839343929735)
        ·
          refine ⟨212132946737548259015894603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141421964491698839343929735 212132946737548259015894603)
          ·
            refine ⟨318199420106322388523841905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212132946737548259015894603 318199420106322388523841905)
            ·
              refine ⟨238649565079741791392881429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318199420106322388523841905 238649565079741791392881429)
              ·
                refine ⟨11186698363112896471541317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 238649565079741791392881429 11186698363112896471541317)
                ·
                  refine ⟨2097505943083668088413997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11186698363112896471541317 2097505943083668088413997)
                  ·
                    refine ⟨786564728656375533155249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2097505943083668088413997 786564728656375533155249)
                    ·
                      rfl

theorem cell22_2297744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4, 3].length) (baseStart_2297744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297744 prefixEnd_2297744 := by exact prefixLift 2297744
  have htrace : WordTrace (prefixWord ++ tailWord_2297744) baseStart_2297744 baseEnd_2297744 := by
    simpa [prefixWord, tailWord_2297744, baseEnd_2297744] using wordTrace_append hprefix tailTrace_2297744
  have hstable : (prefixWord ++ tailWord_2297744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297744).length < 2 ^ (prefixWord ++ tailWord_2297744).sum := by decide
  have hdescent : baseEnd_2297744 < baseStart_2297744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297814 : List Nat := [5, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_2297814 : Nat := 118140960795 + 2297814 * 2 ^ 59
def prefixEnd_2297814 : Nat := 4983230072969 + 3 ^ 40 * 2297814 * 2
def baseEnd_2297814 : Nat := 262196230362306227968345

theorem tailTrace_2297814 : CollatzResearch.WordTrace tailWord_2297814 prefixEnd_2297814 262196230362306227968345 := by
  unfold tailWord_2297814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5238010106088736764558281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55872107798279858821954997 5238010106088736764558281)
  ·
    refine ⟨3928507579566552573418711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5238010106088736764558281 3928507579566552573418711)
    ·
      refine ⟨5892761369349828860128067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3928507579566552573418711 5892761369349828860128067)
      ·
        refine ⟨8839142054024743290192101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5892761369349828860128067 8839142054024743290192101)
        ·
          refine ⟨1657339135129639366911019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8839142054024743290192101 1657339135129639366911019)
          ·
            refine ⟨2486008702694459050366529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657339135129639366911019 2486008702694459050366529)
            ·
              refine ⟨1864506527020844287774897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486008702694459050366529 1864506527020844287774897)
              ·
                refine ⟨1398379895265633215831173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864506527020844287774897 1398379895265633215831173)
                ·
                  refine ⟨262196230362306227968345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398379895265633215831173 262196230362306227968345)
                  ·
                    rfl

theorem cell22_2297814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_2297814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297814 prefixEnd_2297814 := by exact prefixLift 2297814
  have htrace : WordTrace (prefixWord ++ tailWord_2297814) baseStart_2297814 baseEnd_2297814 := by
    simpa [prefixWord, tailWord_2297814, baseEnd_2297814] using wordTrace_append hprefix tailTrace_2297814
  have hstable : (prefixWord ++ tailWord_2297814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297814).length < 2 ^ (prefixWord ++ tailWord_2297814).sum := by decide
  have hdescent : baseEnd_2297814 < baseStart_2297814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297864 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 8]
def baseStart_2297864 : Nat := 118140960795 + 2297864 * 2 ^ 59
def prefixEnd_2297864 : Nat := 4983230072969 + 3 ^ 40 * 2297864 * 2
def baseEnd_2297864 : Nat := 262201935702911740051627

theorem tailTrace_2297864 : CollatzResearch.WordTrace tailWord_2297864 prefixEnd_2297864 262201935702911740051627 := by
  unfold tailWord_2297864
  simp only [CollatzResearch.WordTrace]
  refine ⟨41904992673619323386126323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55873323564825764514835097 41904992673619323386126323)
  ·
    refine ⟨62857489010428985079189485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41904992673619323386126323 62857489010428985079189485)
    ·
      refine ⟨23571558378910869404696057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62857489010428985079189485 23571558378910869404696057)
      ·
        refine ⟨17678668784183152053522043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23571558378910869404696057 17678668784183152053522043)
        ·
          refine ⟨26518003176274728080283065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17678668784183152053522043 26518003176274728080283065)
          ·
            refine ⟨19888502382206046060212299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26518003176274728080283065 19888502382206046060212299)
            ·
              refine ⟨29832753573309069090318449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19888502382206046060212299 29832753573309069090318449)
              ·
                refine ⟨22374565179981801817738837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29832753573309069090318449 22374565179981801817738837)
                ·
                  refine ⟨262201935702911740051627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22374565179981801817738837 262201935702911740051627)
                  ·
                    rfl

theorem cell22_2297864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_2297864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297864 prefixEnd_2297864 := by exact prefixLift 2297864
  have htrace : WordTrace (prefixWord ++ tailWord_2297864) baseStart_2297864 baseEnd_2297864 := by
    simpa [prefixWord, tailWord_2297864, baseEnd_2297864] using wordTrace_append hprefix tailTrace_2297864
  have hstable : (prefixWord ++ tailWord_2297864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297864).length < 2 ^ (prefixWord ++ tailWord_2297864).sum := by decide
  have hdescent : baseEnd_2297864 < baseStart_2297864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297988 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 5]
def baseStart_2297988 : Nat := 118140960795 + 2297988 * 2 ^ 59
def prefixEnd_2297988 : Nat := 4983230072969 + 3 ^ 40 * 2297988 * 2
def baseEnd_2297988 : Nat := 262216084947613410018167

theorem tailTrace_2297988 : CollatzResearch.WordTrace tailWord_2297988 prefixEnd_2297988 262216084947613410018167 := by
  unfold tailWord_2297988
  simp only [CollatzResearch.WordTrace]
  refine ⟨41907253999394707974883309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55876338665859610633177745 41907253999394707974883309)
  ·
    refine ⟨15715220249773015490581241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41907253999394707974883309 15715220249773015490581241)
    ·
      refine ⟨11786415187329761617935931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15715220249773015490581241 11786415187329761617935931)
      ·
        refine ⟨17679622780994642426903897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11786415187329761617935931 17679622780994642426903897)
        ·
          refine ⟨13259717085745981820177923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17679622780994642426903897 13259717085745981820177923)
          ·
            refine ⟨19889575628618972730266885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13259717085745981820177923 19889575628618972730266885)
            ·
              refine ⟨3729295430366057386925041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19889575628618972730266885 3729295430366057386925041)
              ·
                refine ⟨2796971572774543040193781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3729295430366057386925041 2796971572774543040193781)
                ·
                  refine ⟨262216084947613410018167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2796971572774543040193781 262216084947613410018167)
                  ·
                    rfl

theorem cell22_2297988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_2297988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297988 prefixEnd_2297988 := by exact prefixLift 2297988
  have htrace : WordTrace (prefixWord ++ tailWord_2297988) baseStart_2297988 baseEnd_2297988 := by
    simpa [prefixWord, tailWord_2297988, baseEnd_2297988] using wordTrace_append hprefix tailTrace_2297988
  have hstable : (prefixWord ++ tailWord_2297988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297988).length < 2 ^ (prefixWord ++ tailWord_2297988).sum := by decide
  have hdescent : baseEnd_2297988 < baseStart_2297988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297992 : List Nat := [2, 1, 3, 4, 1, 2, 1, 4, 1, 3]
def baseStart_2297992 : Nat := 118140960795 + 2297992 * 2 ^ 59
def prefixEnd_2297992 : Nat := 4983230072969 + 3 ^ 40 * 2297992 * 2
def baseEnd_2297992 : Nat := 786649624124585552954489

theorem tailTrace_2297992 : CollatzResearch.WordTrace tailWord_2297992 prefixEnd_2297992 786649624124585552954489 := by
  unfold tailWord_2297992
  simp only [CollatzResearch.WordTrace]
  refine ⟨41907326945387462316456115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55876435927183283088608153 41907326945387462316456115)
  ·
    refine ⟨62860990418081193474684173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41907326945387462316456115 62860990418081193474684173)
    ·
      refine ⟨23572871406780447553006565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62860990418081193474684173 23572871406780447553006565)
      ·
        refine ⟨4419913388771333916188731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23572871406780447553006565 4419913388771333916188731)
        ·
          refine ⟨6629870083157000874283097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4419913388771333916188731 6629870083157000874283097)
          ·
            refine ⟨4972402562367750655712323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6629870083157000874283097 4972402562367750655712323)
            ·
              refine ⟨7458603843551625983568485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4972402562367750655712323 7458603843551625983568485)
              ·
                refine ⟨1398488220665929871919091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7458603843551625983568485 1398488220665929871919091)
                ·
                  refine ⟨2097732330998894807878637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398488220665929871919091 2097732330998894807878637)
                  ·
                    refine ⟨786649624124585552954489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2097732330998894807878637 786649624124585552954489)
                    ·
                      rfl

theorem cell22_2297992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_2297992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2297992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2297992 prefixEnd_2297992 := by exact prefixLift 2297992
  have htrace : WordTrace (prefixWord ++ tailWord_2297992) baseStart_2297992 baseEnd_2297992 := by
    simpa [prefixWord, tailWord_2297992, baseEnd_2297992] using wordTrace_append hprefix tailTrace_2297992
  have hstable : (prefixWord ++ tailWord_2297992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297992).length < 2 ^ (prefixWord ++ tailWord_2297992).sum := by decide
  have hdescent : baseEnd_2297992 < baseStart_2297992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298016 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 8]
def baseStart_2298016 : Nat := 118140960795 + 2298016 * 2 ^ 59
def prefixEnd_2298016 : Nat := 4983230072969 + 3 ^ 40 * 2298016 * 2
def baseEnd_2298016 : Nat := 262219279938352496784805

theorem tailTrace_2298016 : CollatzResearch.WordTrace tailWord_2298016 prefixEnd_2298016 262219279938352496784805 := by
  unfold tailWord_2298016
  simp only [CollatzResearch.WordTrace]
  refine ⟨41907764621343988365892951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55877019495125317821190601 41907764621343988365892951)
  ·
    refine ⟨62861646932015982548839427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41907764621343988365892951 62861646932015982548839427)
    ·
      refine ⟨94292470398023973823259141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62861646932015982548839427 94292470398023973823259141)
      ·
        refine ⟨17679838199629495091861089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94292470398023973823259141 17679838199629495091861089)
        ·
          refine ⟨13259878649722121318895817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17679838199629495091861089 13259878649722121318895817)
          ·
            refine ⟨9944908987291590989171863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13259878649722121318895817 9944908987291590989171863)
            ·
              refine ⟨14917363480937386483757795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9944908987291590989171863 14917363480937386483757795)
              ·
                refine ⟨22376045221406079725636693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14917363480937386483757795 22376045221406079725636693)
                ·
                  refine ⟨262219279938352496784805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22376045221406079725636693 262219279938352496784805)
                  ·
                    rfl

theorem cell22_2298016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_2298016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298016 prefixEnd_2298016 := by exact prefixLift 2298016
  have htrace : WordTrace (prefixWord ++ tailWord_2298016) baseStart_2298016 baseEnd_2298016 := by
    simpa [prefixWord, tailWord_2298016, baseEnd_2298016] using wordTrace_append hprefix tailTrace_2298016
  have hstable : (prefixWord ++ tailWord_2298016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298016).length < 2 ^ (prefixWord ++ tailWord_2298016).sum := by decide
  have hdescent : baseEnd_2298016 < baseStart_2298016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298116 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_2298116 : Nat := 118140960795 + 2298116 * 2 ^ 59
def prefixEnd_2298116 : Nat := 4983230072969 + 3 ^ 40 * 2298116 * 2
def baseEnd_2298116 : Nat := 786692071858690562854109

theorem tailTrace_2298116 : CollatzResearch.WordTrace tailWord_2298116 prefixEnd_2298116 786692071858690562854109 := by
  unfold tailWord_2298116
  simp only [CollatzResearch.WordTrace]
  refine ⟨41909588271162846905213101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55879451028217129206950801 41909588271162846905213101)
  ·
    refine ⟨15716095601686067589454913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41909588271162846905213101 15716095601686067589454913)
    ·
      refine ⟨11787071701264550692091185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15716095601686067589454913 11787071701264550692091185)
      ·
        refine ⟨8840303775948413019068389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11787071701264550692091185 8840303775948413019068389)
        ·
          refine ⟨1657556957990327441075323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8840303775948413019068389 1657556957990327441075323)
          ·
            refine ⟨2486335436985491161612985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657556957990327441075323 2486335436985491161612985)
            ·
              refine ⟨1864751577739118371209739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486335436985491161612985 1864751577739118371209739)
              ·
                refine ⟨2797127366608677556814609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864751577739118371209739 2797127366608677556814609)
                ·
                  refine ⟨2097845524956508167610957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2797127366608677556814609 2097845524956508167610957)
                  ·
                    refine ⟨786692071858690562854109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2097845524956508167610957 786692071858690562854109)
                    ·
                      rfl

theorem cell22_2298116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_2298116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298116 prefixEnd_2298116 := by exact prefixLift 2298116
  have htrace : WordTrace (prefixWord ++ tailWord_2298116) baseStart_2298116 baseEnd_2298116 := by
    simpa [prefixWord, tailWord_2298116, baseEnd_2298116] using wordTrace_append hprefix tailTrace_2298116
  have hstable : (prefixWord ++ tailWord_2298116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298116).length < 2 ^ (prefixWord ++ tailWord_2298116).sum := by decide
  have hdescent : baseEnd_2298116 < baseStart_2298116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298123 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 5]
def baseStart_2298123 : Nat := 118140960795 + 2298123 * 2 ^ 59
def prefixEnd_2298123 : Nat := 4983230072969 + 3 ^ 40 * 2298123 * 2
def baseEnd_2298123 : Nat := 262231489367248292643029

theorem tailTrace_2298123 : CollatzResearch.WordTrace tailWord_2298123 prefixEnd_2298123 262231489367248292643029 := by
  unfold tailWord_2298123
  simp only [CollatzResearch.WordTrace]
  refine ⟨83819431853300334005931023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55879621235533556003954015 83819431853300334005931023)
  ·
    refine ⟨125729147779950501008896535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83819431853300334005931023 125729147779950501008896535)
    ·
      refine ⟨188593721669925751513344803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125729147779950501008896535 188593721669925751513344803)
      ·
        refine ⟨282890582504888627270017205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188593721669925751513344803 282890582504888627270017205)
        ·
          refine ⟨26520992109833308806564113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 282890582504888627270017205 26520992109833308806564113)
          ·
            refine ⟨19890744082374981604923085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26520992109833308806564113 19890744082374981604923085)
            ·
              refine ⟨7459029030890618101846157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19890744082374981604923085 7459029030890618101846157)
              ·
                refine ⟨2797135886583981788192309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7459029030890618101846157 2797135886583981788192309)
                ·
                  refine ⟨262231489367248292643029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2797135886583981788192309 262231489367248292643029)
                  ·
                    rfl

theorem cell22_2298123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 5].length) (baseStart_2298123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298123 prefixEnd_2298123 := by exact prefixLift 2298123
  have htrace : WordTrace (prefixWord ++ tailWord_2298123) baseStart_2298123 baseEnd_2298123 := by
    simpa [prefixWord, tailWord_2298123, baseEnd_2298123] using wordTrace_append hprefix tailTrace_2298123
  have hstable : (prefixWord ++ tailWord_2298123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298123).length < 2 ^ (prefixWord ++ tailWord_2298123).sum := by decide
  have hdescent : baseEnd_2298123 < baseStart_2298123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298161 : List Nat := [1, 2, 2, 3, 4, 2, 2, 2, 1, 3]
def baseStart_2298161 : Nat := 118140960795 + 2298161 * 2 ^ 59
def prefixEnd_2298161 : Nat := 4983230072969 + 3 ^ 40 * 2298161 * 2
def baseEnd_2298161 : Nat := 786707476278325445478971

theorem tailTrace_2298161 : CollatzResearch.WordTrace tailWord_2298161 prefixEnd_2298161 786707476278325445478971 := by
  unfold tailWord_2298161
  simp only [CollatzResearch.WordTrace]
  refine ⟨83820817827162666495814337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55880545218108444330542891 83820817827162666495814337)
  ·
    refine ⟨62865613370371999871860753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83820817827162666495814337 62865613370371999871860753)
    ·
      refine ⟨47149210027778999903895565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62865613370371999871860753 47149210027778999903895565)
      ·
        refine ⟨17680953760417124963960837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47149210027778999903895565 17680953760417124963960837)
        ·
          refine ⟨3315178830078210930742657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17680953760417124963960837 3315178830078210930742657)
          ·
            refine ⟨2486384122558658198056993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3315178830078210930742657 2486384122558658198056993)
            ·
              refine ⟨1864788091918993648542745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486384122558658198056993 1864788091918993648542745)
              ·
                refine ⟨1398591068939245236407059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864788091918993648542745 1398591068939245236407059)
                ·
                  refine ⟨2097886603408867854610589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398591068939245236407059 2097886603408867854610589)
                  ·
                    refine ⟨786707476278325445478971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2097886603408867854610589 786707476278325445478971)
                    ·
                      rfl

theorem cell22_2298161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_2298161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298161 prefixEnd_2298161 := by exact prefixLift 2298161
  have htrace : WordTrace (prefixWord ++ tailWord_2298161) baseStart_2298161 baseEnd_2298161 := by
    simpa [prefixWord, tailWord_2298161, baseEnd_2298161] using wordTrace_append hprefix tailTrace_2298161
  have hstable : (prefixWord ++ tailWord_2298161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298161).length < 2 ^ (prefixWord ++ tailWord_2298161).sum := by decide
  have hdescent : baseEnd_2298161 < baseStart_2298161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298204 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2298204 : Nat := 118140960795 + 2298204 * 2 ^ 59
def prefixEnd_2298204 : Nat := 4983230072969 + 3 ^ 40 * 2298204 * 2
def baseEnd_2298204 : Nat := 786722196057087666653839

theorem tailTrace_2298204 : CollatzResearch.WordTrace tailWord_2298204 prefixEnd_2298204 786722196057087666653839 := by
  unfold tailWord_2298204
  simp only [CollatzResearch.WordTrace]
  refine ⟨41911193083003442419814833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55881590777337923226419777 41911193083003442419814833)
  ·
    refine ⟨31433394812252581814861125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41911193083003442419814833 31433394812252581814861125)
    ·
      refine ⟨5893761527297359090286461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31433394812252581814861125 5893761527297359090286461)
      ·
        refine ⟨2210160572736509658857423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5893761527297359090286461 2210160572736509658857423)
        ·
          refine ⟨3315240859104764488286135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2210160572736509658857423 3315240859104764488286135)
          ·
            refine ⟨4972861288657146732429203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3315240859104764488286135 4972861288657146732429203)
            ·
              refine ⟨7459291932985720098643805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4972861288657146732429203 7459291932985720098643805)
              ·
                refine ⟨2797234474869645036991427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7459291932985720098643805 2797234474869645036991427)
                ·
                  refine ⟨4195851712304467555487141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2797234474869645036991427 4195851712304467555487141)
                  ·
                    refine ⟨786722196057087666653839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4195851712304467555487141 786722196057087666653839)
                    ·
                      rfl

theorem cell22_2298204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2298204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298204 prefixEnd_2298204 := by exact prefixLift 2298204
  have htrace : WordTrace (prefixWord ++ tailWord_2298204) baseStart_2298204 baseEnd_2298204 := by
    simpa [prefixWord, tailWord_2298204, baseEnd_2298204] using wordTrace_append hprefix tailTrace_2298204
  have hstable : (prefixWord ++ tailWord_2298204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298204).length < 2 ^ (prefixWord ++ tailWord_2298204).sum := by decide
  have hdescent : baseEnd_2298204 < baseStart_2298204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298213 : List Nat := [1, 3, 1, 3, 1, 4, 9]
def baseStart_2298213 : Nat := 118140960795 + 2298213 * 2 ^ 59
def prefixEnd_2298213 : Nat := 4983230072969 + 3 ^ 40 * 2298213 * 2
def baseEnd_2298213 : Nat := 29137973220037579376993

theorem tailTrace_2298213 : CollatzResearch.WordTrace tailWord_2298213 prefixEnd_2298213 29137973220037579376993 := by
  unfold tailWord_2298213
  simp only [CollatzResearch.WordTrace]
  refine ⟨83822714422974279376707293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55881809615316186251138195 83822714422974279376707293)
  ·
    refine ⟨31433517908615354766265235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83822714422974279376707293 31433517908615354766265235)
    ·
      refine ⟨47150276862923032149397853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31433517908615354766265235 47150276862923032149397853)
      ·
        refine ⟨17681353823596137056024195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47150276862923032149397853 17681353823596137056024195)
        ·
          refine ⟨26522030735394205584036293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17681353823596137056024195 26522030735394205584036293)
          ·
            refine ⟨4972880762886413547006805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26522030735394205584036293 4972880762886413547006805)
            ·
              refine ⟨29137973220037579376993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4972880762886413547006805 29137973220037579376993)
              ·
                rfl

theorem cell22_2298213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 9].length) (baseStart_2298213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298213 prefixEnd_2298213 := by exact prefixLift 2298213
  have htrace : WordTrace (prefixWord ++ tailWord_2298213) baseStart_2298213 baseEnd_2298213 := by
    simpa [prefixWord, tailWord_2298213, baseEnd_2298213] using wordTrace_append hprefix tailTrace_2298213
  have hstable : (prefixWord ++ tailWord_2298213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298213).length < 2 ^ (prefixWord ++ tailWord_2298213).sum := by decide
  have hdescent : baseEnd_2298213 < baseStart_2298213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298279 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2298279 : Nat := 118140960795 + 2298279 * 2 ^ 59
def prefixEnd_2298279 : Nat := 4983230072969 + 3 ^ 40 * 2298279 * 2
def baseEnd_2298279 : Nat := 786747870089812471028609

theorem tailTrace_2298279 : CollatzResearch.WordTrace tailWord_2298279 prefixEnd_2298279 786747870089812471028609 := by
  unfold tailWord_2298279
  simp only [CollatzResearch.WordTrace]
  refine ⟨83825121640735172648609891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55883414427156781765739927 83825121640735172648609891)
  ·
    refine ⟨125737682461102758972914837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83825121640735172648609891 125737682461102758972914837)
    ·
      refine ⟨5893953865364191826855383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 125737682461102758972914837 5893953865364191826855383)
      ·
        refine ⟨8840930798046287740283075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5893953865364191826855383 8840930798046287740283075)
        ·
          refine ⟨13261396197069431610424613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8840930798046287740283075 13261396197069431610424613)
          ·
            refine ⟨2486511786950518426954615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13261396197069431610424613 2486511786950518426954615)
            ·
              refine ⟨3729767680425777640431923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486511786950518426954615 3729767680425777640431923)
              ·
                refine ⟨5594651520638666460647885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3729767680425777640431923 5594651520638666460647885)
                ·
                  refine ⟨2097994320239499922742957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5594651520638666460647885 2097994320239499922742957)
                  ·
                    refine ⟨786747870089812471028609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2097994320239499922742957 786747870089812471028609)
                    ·
                      rfl

theorem cell22_2298279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2298279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298279 prefixEnd_2298279 := by exact prefixLift 2298279
  have htrace : WordTrace (prefixWord ++ tailWord_2298279) baseStart_2298279 baseEnd_2298279 := by
    simpa [prefixWord, tailWord_2298279, baseEnd_2298279] using wordTrace_append hprefix tailTrace_2298279
  have hstable : (prefixWord ++ tailWord_2298279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298279).length < 2 ^ (prefixWord ++ tailWord_2298279).sum := by decide
  have hdescent : baseEnd_2298279 < baseStart_2298279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298337 : List Nat := [1, 2, 3, 1, 2, 2, 3, 4, 4]
def baseStart_2298337 : Nat := 118140960795 + 2298337 * 2 ^ 59
def prefixEnd_2298337 : Nat := 4983230072969 + 3 ^ 40 * 2298337 * 2
def baseEnd_2298337 : Nat := 262255908225039884359477

theorem tailTrace_2298337 : CollatzResearch.WordTrace tailWord_2298337 prefixEnd_2298337 262255908225039884359477 := by
  unfold tailWord_2298337
  simp only [CollatzResearch.WordTrace]
  refine ⟨83827237074525048554221265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55884824716350032369480843 83827237074525048554221265)
  ·
    refine ⟨62870427805893786415665949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83827237074525048554221265 62870427805893786415665949)
    ·
      refine ⟨23576410427210169905874731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62870427805893786415665949 23576410427210169905874731)
      ·
        refine ⟨35364615640815254858812097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23576410427210169905874731 35364615640815254858812097)
        ·
          refine ⟨26523461730611441144109073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35364615640815254858812097 26523461730611441144109073)
          ·
            refine ⟨19892596297958580858081805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26523461730611441144109073 19892596297958580858081805)
            ·
              refine ⟨7459723611734467821780677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19892596297958580858081805 7459723611734467821780677)
              ·
                refine ⟨1398698177200212716583877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7459723611734467821780677 1398698177200212716583877)
                ·
                  refine ⟨262255908225039884359477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398698177200212716583877 262255908225039884359477)
                  ·
                    rfl

theorem cell22_2298337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 4].length) (baseStart_2298337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298337 prefixEnd_2298337 := by exact prefixLift 2298337
  have htrace : WordTrace (prefixWord ++ tailWord_2298337) baseStart_2298337 baseEnd_2298337 := by
    simpa [prefixWord, tailWord_2298337, baseEnd_2298337] using wordTrace_append hprefix tailTrace_2298337
  have hstable : (prefixWord ++ tailWord_2298337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298337).length < 2 ^ (prefixWord ++ tailWord_2298337).sum := by decide
  have hdescent : baseEnd_2298337 < baseStart_2298337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298352 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 2, 3]
def baseStart_2298352 : Nat := 118140960795 + 2298352 * 2 ^ 59
def prefixEnd_2298352 : Nat := 4983230072969 + 3 ^ 40 * 2298352 * 2
def baseEnd_2298352 : Nat := 786772859481664613953385

theorem tailTrace_2298352 : CollatzResearch.WordTrace tailWord_2298352 prefixEnd_2298352 786772859481664613953385 := by
  unfold tailWord_2298352
  simp only [CollatzResearch.WordTrace]
  refine ⟨41913892084735353058008655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55885189446313804077344873 41913892084735353058008655)
  ·
    refine ⟨62870838127103029587012983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41913892084735353058008655 62870838127103029587012983)
    ·
      refine ⟨94306257190654544380519475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62870838127103029587012983 94306257190654544380519475)
      ·
        refine ⟨141459385785981816570779213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94306257190654544380519475 141459385785981816570779213)
        ·
          refine ⟨53047269669743181214042205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141459385785981816570779213 53047269669743181214042205)
          ·
            refine ⟨19892726126153692955265827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53047269669743181214042205 19892726126153692955265827)
            ·
              refine ⟨29839089189230539432898741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19892726126153692955265827 29839089189230539432898741)
              ·
                refine ⟨2797414611490363071834257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29839089189230539432898741 2797414611490363071834257)
                ·
                  refine ⟨2098060958617772303875693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2797414611490363071834257 2098060958617772303875693)
                  ·
                    refine ⟨786772859481664613953385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2098060958617772303875693 786772859481664613953385)
                    ·
                      rfl

theorem cell22_2298352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2, 3].length) (baseStart_2298352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298352 prefixEnd_2298352 := by exact prefixLift 2298352
  have htrace : WordTrace (prefixWord ++ tailWord_2298352) baseStart_2298352 baseEnd_2298352 := by
    simpa [prefixWord, tailWord_2298352, baseEnd_2298352] using wordTrace_append hprefix tailTrace_2298352
  have hstable : (prefixWord ++ tailWord_2298352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298352).length < 2 ^ (prefixWord ++ tailWord_2298352).sum := by decide
  have hdescent : baseEnd_2298352 < baseStart_2298352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298487 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 6, 3]
def baseStart_2298487 : Nat := 118140960795 + 2298487 * 2 ^ 59
def prefixEnd_2298487 : Nat := 4983230072969 + 3 ^ 40 * 2298487 * 2
def baseEnd_2298487 : Nat := 786819072740569261827971

theorem tailTrace_2298487 : CollatzResearch.WordTrace tailWord_2298487 prefixEnd_2298487 786819072740569261827971 := by
  unfold tailWord_2298487
  simp only [CollatzResearch.WordTrace]
  refine ⟨83832708023981624172181715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55888472015987749448121143 83832708023981624172181715)
  ·
    refine ⟨125749062035972436258272573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83832708023981624172181715 125749062035972436258272573)
    ·
      refine ⟨47155898263489663596852215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125749062035972436258272573 47155898263489663596852215)
      ·
        refine ⟨70733847395234495395278323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47155898263489663596852215 70733847395234495395278323)
        ·
          refine ⟨106100771092851743092917485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70733847395234495395278323 106100771092851743092917485)
          ·
            refine ⟨39787789159819403659844057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106100771092851743092917485 39787789159819403659844057)
            ·
              refine ⟨29840841869864552744883043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39787789159819403659844057 29840841869864552744883043)
              ·
                refine ⟨44761262804796829117324565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29840841869864552744883043 44761262804796829117324565)
                ·
                  refine ⟨2098184193974851364874589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44761262804796829117324565 2098184193974851364874589)
                  ·
                    refine ⟨786819072740569261827971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2098184193974851364874589 786819072740569261827971)
                    ·
                      rfl

theorem cell22_2298487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_2298487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298487 prefixEnd_2298487 := by exact prefixLift 2298487
  have htrace : WordTrace (prefixWord ++ tailWord_2298487) baseStart_2298487 baseEnd_2298487 := by
    simpa [prefixWord, tailWord_2298487, baseEnd_2298487] using wordTrace_append hprefix tailTrace_2298487
  have hstable : (prefixWord ++ tailWord_2298487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298487).length < 2 ^ (prefixWord ++ tailWord_2298487).sum := by decide
  have hdescent : baseEnd_2298487 < baseStart_2298487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298506 : List Nat := [3, 1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_2298506 : Nat := 118140960795 + 2298506 * 2 ^ 59
def prefixEnd_2298506 : Nat := 4983230072969 + 3 ^ 40 * 2298506 * 2
def baseEnd_2298506 : Nat := 262275192276286515200971

theorem tailTrace_2298506 : CollatzResearch.WordTrace tailWord_2298506 prefixEnd_2298506 262275192276286515200971 := by
  unfold tailWord_2298506
  simp only [CollatzResearch.WordTrace]
  refine ⟨20958350252728197604280843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55888934007275193611415581 20958350252728197604280843)
  ·
    refine ⟨31437525379092296406421265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20958350252728197604280843 31437525379092296406421265)
    ·
      refine ⟨23578144034319222304815949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31437525379092296406421265 23578144034319222304815949)
      ·
        refine ⟨8841804012869708364305981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23578144034319222304815949 8841804012869708364305981)
        ·
          refine ⟨3315676504826140636614743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8841804012869708364305981 3315676504826140636614743)
          ·
            refine ⟨4973514757239210954922115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3315676504826140636614743 4973514757239210954922115)
            ·
              refine ⟨7460272135858816432383173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973514757239210954922115 7460272135858816432383173)
              ·
                refine ⟨1398801025473528081071845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7460272135858816432383173 1398801025473528081071845)
                ·
                  refine ⟨262275192276286515200971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398801025473528081071845 262275192276286515200971)
                  ·
                    rfl

theorem cell22_2298506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_2298506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298506 prefixEnd_2298506 := by exact prefixLift 2298506
  have htrace : WordTrace (prefixWord ++ tailWord_2298506) baseStart_2298506 baseEnd_2298506 := by
    simpa [prefixWord, tailWord_2298506, baseEnd_2298506] using wordTrace_append hprefix tailTrace_2298506
  have hstable : (prefixWord ++ tailWord_2298506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298506).length < 2 ^ (prefixWord ++ tailWord_2298506).sum := by decide
  have hdescent : baseEnd_2298506 < baseStart_2298506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298577 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_2298577 : Nat := 118140960795 + 2298577 * 2 ^ 59
def prefixEnd_2298577 : Nat := 4983230072969 + 3 ^ 40 * 2298577 * 2
def baseEnd_2298577 : Nat := 786849881579839027077695

theorem tailTrace_2298577 : CollatzResearch.WordTrace tailWord_2298577 prefixEnd_2298577 786849881579839027077695 := by
  unfold tailWord_2298577
  simp only [CollatzResearch.WordTrace]
  refine ⟨83835990593655569542957985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55890660395770379695305323 83835990593655569542957985)
  ·
    refine ⟨62876992945241677157218489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83835990593655569542957985 62876992945241677157218489)
    ·
      refine ⟨47157744708931257867913867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62876992945241677157218489 47157744708931257867913867)
      ·
        refine ⟨70736617063396886801870801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47157744708931257867913867 70736617063396886801870801)
        ·
          refine ⟨53052462797547665101403101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70736617063396886801870801 53052462797547665101403101)
          ·
            refine ⟨19894673549080374413026163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53052462797547665101403101 19894673549080374413026163)
            ·
              refine ⟨29842010323620561619539245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19894673549080374413026163 29842010323620561619539245)
              ·
                refine ⟨11190753871357710607327217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29842010323620561619539245 11190753871357710607327217)
                ·
                  refine ⟨8393065403518282955495413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11190753871357710607327217 8393065403518282955495413)
                  ·
                    refine ⟨786849881579839027077695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8393065403518282955495413 786849881579839027077695)
                    ·
                      rfl

theorem cell22_2298577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_2298577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298577 prefixEnd_2298577 := by exact prefixLift 2298577
  have htrace : WordTrace (prefixWord ++ tailWord_2298577) baseStart_2298577 baseEnd_2298577 := by
    simpa [prefixWord, tailWord_2298577, baseEnd_2298577] using wordTrace_append hprefix tailTrace_2298577
  have hstable : (prefixWord ++ tailWord_2298577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298577).length < 2 ^ (prefixWord ++ tailWord_2298577).sum := by decide
  have hdescent : baseEnd_2298577 < baseStart_2298577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298600 : List Nat := [2, 1, 4, 1, 4, 2, 1, 3, 1, 3]
def baseStart_2298600 : Nat := 118140960795 + 2298600 * 2 ^ 59
def prefixEnd_2298600 : Nat := 4983230072969 + 3 ^ 40 * 2298600 * 2
def baseEnd_2298600 : Nat := 786857754949874633752625

theorem tailTrace_2298600 : CollatzResearch.WordTrace tailWord_2298600 prefixEnd_2298600 786857754949874633752625 := by
  unfold tailWord_2298600
  simp only [CollatzResearch.WordTrace]
  refine ⟨41918414736286122235522627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55891219648381496314030169 41918414736286122235522627)
  ·
    refine ⟨62877622104429183353283941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41918414736286122235522627 62877622104429183353283941)
    ·
      refine ⟨11789554144580471878740739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62877622104429183353283941 11789554144580471878740739)
      ·
        refine ⟨17684331216870707818111109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11789554144580471878740739 17684331216870707818111109)
        ·
          refine ⟨3315812103163257715895833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17684331216870707818111109 3315812103163257715895833)
          ·
            refine ⟨2486859077372443286921875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3315812103163257715895833 2486859077372443286921875)
            ·
              refine ⟨3730288616058664930382813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486859077372443286921875 3730288616058664930382813)
              ·
                refine ⟨1398858231021999348893555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3730288616058664930382813 1398858231021999348893555)
                ·
                  refine ⟨2098287346532999023340333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398858231021999348893555 2098287346532999023340333)
                  ·
                    refine ⟨786857754949874633752625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2098287346532999023340333 786857754949874633752625)
                    ·
                      rfl

theorem cell22_2298600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_2298600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298600 prefixEnd_2298600 := by exact prefixLift 2298600
  have htrace : WordTrace (prefixWord ++ tailWord_2298600) baseStart_2298600 baseEnd_2298600 := by
    simpa [prefixWord, tailWord_2298600, baseEnd_2298600] using wordTrace_append hprefix tailTrace_2298600
  have hstable : (prefixWord ++ tailWord_2298600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298600).length < 2 ^ (prefixWord ++ tailWord_2298600).sum := by decide
  have hdescent : baseEnd_2298600 < baseStart_2298600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298609 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 1, 4]
def baseStart_2298609 : Nat := 118140960795 + 2298609 * 2 ^ 59
def prefixEnd_2298609 : Nat := 4983230072969 + 3 ^ 40 * 2298609 * 2
def baseEnd_2298609 : Nat := 786860835833801610277597

theorem tailTrace_2298609 : CollatzResearch.WordTrace tailWord_2298609 prefixEnd_2298609 786860835833801610277597 := by
  unfold tailWord_2298609
  simp only [CollatzResearch.WordTrace]
  refine ⟨83837157729539639008122881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55891438486359759338748587 83837157729539639008122881)
  ·
    refine ⟨62877868297154729256092161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83837157729539639008122881 62877868297154729256092161)
    ·
      refine ⟨47158401222866046942069121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62877868297154729256092161 47158401222866046942069121)
      ·
        refine ⟨35368800917149535206551841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47158401222866046942069121 35368800917149535206551841)
        ·
          refine ⟨26526600687862151404913881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35368800917149535206551841 26526600687862151404913881)
          ·
            refine ⟨19894950515896613553685411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26526600687862151404913881 19894950515896613553685411)
            ·
              refine ⟨29842425773844920330528117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19894950515896613553685411 29842425773844920330528117)
              ·
                refine ⟨2797727416297961280987011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29842425773844920330528117 2797727416297961280987011)
                ·
                  refine ⟨4196591124446941921480517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2797727416297961280987011 4196591124446941921480517)
                  ·
                    refine ⟨786860835833801610277597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4196591124446941921480517 786860835833801610277597)
                    ·
                      rfl

theorem cell22_2298609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_2298609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298609 prefixEnd_2298609 := by exact prefixLift 2298609
  have htrace : WordTrace (prefixWord ++ tailWord_2298609) baseStart_2298609 baseEnd_2298609 := by
    simpa [prefixWord, tailWord_2298609, baseEnd_2298609] using wordTrace_append hprefix tailTrace_2298609
  have hstable : (prefixWord ++ tailWord_2298609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298609).length < 2 ^ (prefixWord ++ tailWord_2298609).sum := by decide
  have hdescent : baseEnd_2298609 < baseStart_2298609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298744 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_2298744 : Nat := 118140960795 + 2298744 * 2 ^ 59
def prefixEnd_2298744 : Nat := 4983230072969 + 3 ^ 40 * 2298744 * 2
def baseEnd_2298744 : Nat := 786907049092706258152183

theorem tailTrace_2298744 : CollatzResearch.WordTrace tailWord_2298744 prefixEnd_2298744 786907049092706258152183 := by
  unfold tailWord_2298744
  simp only [CollatzResearch.WordTrace]
  refine ⟨41921040792025278532143643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55894721056033704709524857 41921040792025278532143643)
  ·
    refine ⟨62881561188037917798215465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41921040792025278532143643 62881561188037917798215465)
    ·
      refine ⟨47161170891028438348661599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62881561188037917798215465 47161170891028438348661599)
      ·
        refine ⟨70741756336542657522992399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47161170891028438348661599 70741756336542657522992399)
        ·
          refine ⟨106112634504813986284488599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70741756336542657522992399 106112634504813986284488599)
          ·
            refine ⟨159168951757220979426732899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106112634504813986284488599 159168951757220979426732899)
            ·
              refine ⟨238753427635831469140099349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159168951757220979426732899 238753427635831469140099349)
              ·
                refine ⟨11191566920429600115942157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 238753427635831469140099349 11191566920429600115942157)
                ·
                  refine ⟨4196837595161100043478309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11191566920429600115942157 4196837595161100043478309)
                  ·
                    refine ⟨786907049092706258152183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4196837595161100043478309 786907049092706258152183)
                    ·
                      rfl

theorem cell22_2298744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_2298744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298744 prefixEnd_2298744 := by exact prefixLift 2298744
  have htrace : WordTrace (prefixWord ++ tailWord_2298744) baseStart_2298744 baseEnd_2298744 := by
    simpa [prefixWord, tailWord_2298744, baseEnd_2298744] using wordTrace_append hprefix tailTrace_2298744
  have hstable : (prefixWord ++ tailWord_2298744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298744).length < 2 ^ (prefixWord ++ tailWord_2298744).sum := by decide
  have hdescent : baseEnd_2298744 < baseStart_2298744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298761 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 1, 4]
def baseStart_2298761 : Nat := 118140960795 + 2298761 * 2 ^ 59
def prefixEnd_2298761 : Nat := 4983230072969 + 3 ^ 40 * 2298761 * 2
def baseEnd_2298761 : Nat := 786912868540123880477131

theorem tailTrace_2298761 : CollatzResearch.WordTrace tailWord_2298761 prefixEnd_2298761 786912868540123880477131 := by
  unfold tailWord_2298761
  simp only [CollatzResearch.WordTrace]
  refine ⟨83842701624988968967656137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55895134416659312645104091 83842701624988968967656137)
  ·
    refine ⟨62882026218741726725742103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83842701624988968967656137 62882026218741726725742103)
    ·
      refine ⟨94323039328112590088613155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62882026218741726725742103 94323039328112590088613155)
      ·
        refine ⟨141484558992168885132919733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94323039328112590088613155 141484558992168885132919733)
        ·
          refine ⟨13264177405515832981211225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141484558992168885132919733 13264177405515832981211225)
          ·
            refine ⟨9948133054136874735908419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13264177405515832981211225 9948133054136874735908419)
            ·
              refine ⟨14922199581205312103862629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9948133054136874735908419 14922199581205312103862629)
              ·
                refine ⟨2797912421475996019474243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14922199581205312103862629 2797912421475996019474243)
                ·
                  refine ⟨4196868632213994029211365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2797912421475996019474243 4196868632213994029211365)
                  ·
                    refine ⟨786912868540123880477131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4196868632213994029211365 786912868540123880477131)
                    ·
                      rfl

theorem cell22_2298761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_2298761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298761 prefixEnd_2298761 := by exact prefixLift 2298761
  have htrace : WordTrace (prefixWord ++ tailWord_2298761) baseStart_2298761 baseEnd_2298761 := by
    simpa [prefixWord, tailWord_2298761, baseEnd_2298761] using wordTrace_append hprefix tailTrace_2298761
  have hstable : (prefixWord ++ tailWord_2298761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298761).length < 2 ^ (prefixWord ++ tailWord_2298761).sum := by decide
  have hdescent : baseEnd_2298761 < baseStart_2298761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298793 : List Nat := [1, 2, 1, 1, 1, 1, 9, 2, 4]
def baseStart_2298793 : Nat := 118140960795 + 2298793 * 2 ^ 59
def prefixEnd_2298793 : Nat := 4983230072969 + 3 ^ 40 * 2298793 * 2
def baseEnd_2298793 : Nat := 262307940931362154559011

theorem tailTrace_2298793 : CollatzResearch.WordTrace tailWord_2298793 prefixEnd_2298793 262307940931362154559011 := by
  unfold tailWord_2298793
  simp only [CollatzResearch.WordTrace]
  refine ⟨83843868760873038432821033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55895912507248692288547355 83843868760873038432821033)
  ·
    refine ⟨62882901570654778824615775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83843868760873038432821033 62882901570654778824615775)
    ·
      refine ⟨94324352355982168236923663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62882901570654778824615775 94324352355982168236923663)
      ·
        refine ⟨141486528533973252355385495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94324352355982168236923663 141486528533973252355385495)
        ·
          refine ⟨212229792800959878533078243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141486528533973252355385495 212229792800959878533078243)
          ·
            refine ⟨318344689201439817799617365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212229792800959878533078243 318344689201439817799617365)
            ·
              refine ⟨1865300913289686432419633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 318344689201439817799617365 1865300913289686432419633)
              ·
                refine ⟨1398975684967264824314725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1865300913289686432419633 1398975684967264824314725)
                ·
                  refine ⟨262307940931362154559011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398975684967264824314725 262307940931362154559011)
                  ·
                    rfl

theorem cell22_2298793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 4].length) (baseStart_2298793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298793 prefixEnd_2298793 := by exact prefixLift 2298793
  have htrace : WordTrace (prefixWord ++ tailWord_2298793) baseStart_2298793 baseEnd_2298793 := by
    simpa [prefixWord, tailWord_2298793, baseEnd_2298793] using wordTrace_append hprefix tailTrace_2298793
  have hstable : (prefixWord ++ tailWord_2298793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298793).length < 2 ^ (prefixWord ++ tailWord_2298793).sum := by decide
  have hdescent : baseEnd_2298793 < baseStart_2298793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298808 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 2, 3]
def baseStart_2298808 : Nat := 118140960795 + 2298808 * 2 ^ 59
def prefixEnd_2298808 : Nat := 4983230072969 + 3 ^ 40 * 2298808 * 2
def baseEnd_2298808 : Nat := 786928957600631424551987

theorem tailTrace_2298808 : CollatzResearch.WordTrace tailWord_2298808 prefixEnd_2298808 786928957600631424551987 := by
  unfold tailWord_2298808
  simp only [CollatzResearch.WordTrace]
  refine ⟨41922207927909347997308539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55896277237212463996411385 41922207927909347997308539)
  ·
    refine ⟨62883311891864021995962809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41922207927909347997308539 62883311891864021995962809)
    ·
      refine ⟨47162483918898016496972107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62883311891864021995962809 47162483918898016496972107)
      ·
        refine ⟨70743725878347024745458161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47162483918898016496972107 70743725878347024745458161)
        ·
          refine ⟨53057794408760268559093621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70743725878347024745458161 53057794408760268559093621)
          ·
            refine ⟨4974168225821275177415027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53057794408760268559093621 4974168225821275177415027)
            ·
              refine ⟨7461252338731912766122541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4974168225821275177415027 7461252338731912766122541)
              ·
                refine ⟨2797969627024467287295953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7461252338731912766122541 2797969627024467287295953)
                ·
                  refine ⟨2098477220268350465471965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2797969627024467287295953 2098477220268350465471965)
                  ·
                    refine ⟨786928957600631424551987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2098477220268350465471965 786928957600631424551987)
                    ·
                      rfl

theorem cell22_2298808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_2298808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298808 prefixEnd_2298808 := by exact prefixLift 2298808
  have htrace : WordTrace (prefixWord ++ tailWord_2298808) baseStart_2298808 baseEnd_2298808 := by
    simpa [prefixWord, tailWord_2298808, baseEnd_2298808] using wordTrace_append hprefix tailTrace_2298808
  have hstable : (prefixWord ++ tailWord_2298808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298808).length < 2 ^ (prefixWord ++ tailWord_2298808).sum := by decide
  have hdescent : baseEnd_2298808 < baseStart_2298808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298870 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_2298870 : Nat := 118140960795 + 2298870 * 2 ^ 59
def prefixEnd_2298870 : Nat := 4983230072969 + 3 ^ 40 * 2298870 * 2
def baseEnd_2298870 : Nat := 786950181467683929501797

theorem tailTrace_2298870 : CollatzResearch.WordTrace tailWord_2298870 prefixEnd_2298870 786950181467683929501797 := by
  unfold tailWord_2298870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5240417323849630036460879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55897784787729387055582709 5240417323849630036460879)
  ·
    refine ⟨7860625985774445054691319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5240417323849630036460879 7860625985774445054691319)
    ·
      refine ⟨11790938978661667582036979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7860625985774445054691319 11790938978661667582036979)
      ·
        refine ⟨17686408467992501373055469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11790938978661667582036979 17686408467992501373055469)
        ·
          refine ⟨6632403175497188014895801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17686408467992501373055469 6632403175497188014895801)
          ·
            refine ⟨4974302381622891011171851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6632403175497188014895801 4974302381622891011171851)
            ·
              refine ⟨7461453572434336516757777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4974302381622891011171851 7461453572434336516757777)
              ·
                refine ⟨5596090179325752387568333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7461453572434336516757777 5596090179325752387568333)
                ·
                  refine ⟨2098533817247157145338125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5596090179325752387568333 2098533817247157145338125)
                  ·
                    refine ⟨786950181467683929501797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2098533817247157145338125 786950181467683929501797)
                    ·
                      rfl

theorem cell22_2298870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_2298870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298870 prefixEnd_2298870 := by exact prefixLift 2298870
  have htrace : WordTrace (prefixWord ++ tailWord_2298870) baseStart_2298870 baseEnd_2298870 := by
    simpa [prefixWord, tailWord_2298870, baseEnd_2298870] using wordTrace_append hprefix tailTrace_2298870
  have hstable : (prefixWord ++ tailWord_2298870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298870).length < 2 ^ (prefixWord ++ tailWord_2298870).sum := by decide
  have hdescent : baseEnd_2298870 < baseStart_2298870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298911 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 6]
def baseStart_2298911 : Nat := 118140960795 + 2298911 * 2 ^ 59
def prefixEnd_2298911 : Nat := 4983230072969 + 3 ^ 40 * 2298911 * 2
def baseEnd_2298911 : Nat := 262321405535191163075557

theorem tailTrace_2298911 : CollatzResearch.WordTrace tailWord_2298911 prefixEnd_2298911 262321405535191163075557 := by
  unfold tailWord_2298911
  simp only [CollatzResearch.WordTrace]
  refine ⟨83848172574445544585616587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55898781716297029723744391 83848172574445544585616587)
  ·
    refine ⟨125772258861668316878424881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83848172574445544585616587 125772258861668316878424881)
    ·
      refine ⟨94329194146251237658818661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125772258861668316878424881 94329194146251237658818661)
      ·
        refine ⟨17686723902422107061028499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94329194146251237658818661 17686723902422107061028499)
        ·
          refine ⟨26530085853633160591542749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17686723902422107061028499 26530085853633160591542749)
          ·
            refine ⟨9948782195112435221828531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26530085853633160591542749 9948782195112435221828531)
            ·
              refine ⟨14923173292668652832742797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9948782195112435221828531 14923173292668652832742797)
              ·
                refine ⟨5596189984750744812278549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14923173292668652832742797 5596189984750744812278549)
                ·
                  refine ⟨262321405535191163075557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5596189984750744812278549 262321405535191163075557)
                  ·
                    rfl

theorem cell22_2298911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 6].length) (baseStart_2298911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298911 prefixEnd_2298911 := by exact prefixLift 2298911
  have htrace : WordTrace (prefixWord ++ tailWord_2298911) baseStart_2298911 baseEnd_2298911 := by
    simpa [prefixWord, tailWord_2298911, baseEnd_2298911] using wordTrace_append hprefix tailTrace_2298911
  have hstable : (prefixWord ++ tailWord_2298911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298911).length < 2 ^ (prefixWord ++ tailWord_2298911).sum := by decide
  have hdescent : baseEnd_2298911 < baseStart_2298911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298958 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2298958 : Nat := 118140960795 + 2298958 * 2 ^ 59
def prefixEnd_2298958 : Nat := 4983230072969 + 3 ^ 40 * 2298958 * 2
def baseEnd_2298958 : Nat := 786980305666081033301527

theorem tailTrace_2298958 : CollatzResearch.WordTrace tailWord_2298958 prefixEnd_2298958 786980305666081033301527 := by
  unfold tailWord_2298958
  simp only [CollatzResearch.WordTrace]
  refine ⟨10481235850659408951572191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55899924536850181075051685 10481235850659408951572191)
  ·
    refine ⟨15721853775989113427358287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10481235850659408951572191 15721853775989113427358287)
    ·
      refine ⟨23582780663983670141037431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15721853775989113427358287 23582780663983670141037431)
      ·
        refine ⟨35374170995975505211556147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23582780663983670141037431 35374170995975505211556147)
        ·
          refine ⟨53061256493963257817334221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35374170995975505211556147 53061256493963257817334221)
          ·
            refine ⟨19897971185236221681500333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53061256493963257817334221 19897971185236221681500333)
            ·
              refine ⟨7461739194463583130562625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19897971185236221681500333 7461739194463583130562625)
              ·
                refine ⟨5596304395847687347921969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7461739194463583130562625 5596304395847687347921969)
                ·
                  refine ⟨4197228296885765510941477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5596304395847687347921969 4197228296885765510941477)
                  ·
                    refine ⟨786980305666081033301527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4197228296885765510941477 786980305666081033301527)
                    ·
                      rfl

theorem cell22_2298958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2298958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298958 prefixEnd_2298958 := by exact prefixLift 2298958
  have htrace : WordTrace (prefixWord ++ tailWord_2298958) baseStart_2298958 baseEnd_2298958 := by
    simpa [prefixWord, tailWord_2298958, baseEnd_2298958] using wordTrace_append hprefix tailTrace_2298958
  have hstable : (prefixWord ++ tailWord_2298958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298958).length < 2 ^ (prefixWord ++ tailWord_2298958).sum := by decide
  have hdescent : baseEnd_2298958 < baseStart_2298958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298962 : List Nat := [3, 2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_2298962 : Nat := 118140960795 + 2298962 * 2 ^ 59
def prefixEnd_2298962 : Nat := 4983230072969 + 3 ^ 40 * 2298962 * 2
def baseEnd_2298962 : Nat := 262327224982608785400505

theorem tailTrace_2298962 : CollatzResearch.WordTrace tailWord_2298962 prefixEnd_2298962 262327224982608785400505 := by
  unfold tailWord_2298962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20962508174315195073930785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55900021798173853530482093 20962508174315195073930785)
  ·
    refine ⟨15721881130736396305448089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20962508174315195073930785 15721881130736396305448089)
    ·
      refine ⟨11791410848052297229086067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15721881130736396305448089 11791410848052297229086067)
      ·
        refine ⟨17687116272078445843629101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11791410848052297229086067 17687116272078445843629101)
        ·
          refine ⟨6632668602029417191360913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17687116272078445843629101 6632668602029417191360913)
          ·
            refine ⟨4974501451522062893520685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6632668602029417191360913 4974501451522062893520685)
            ·
              refine ⟨1865438044320773585070257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4974501451522062893520685 1865438044320773585070257)
              ·
                refine ⟨1399078533240580188802693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1865438044320773585070257 1399078533240580188802693)
                ·
                  refine ⟨262327224982608785400505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399078533240580188802693 262327224982608785400505)
                  ·
                    rfl

theorem cell22_2298962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_2298962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298962 prefixEnd_2298962 := by exact prefixLift 2298962
  have htrace : WordTrace (prefixWord ++ tailWord_2298962) baseStart_2298962 baseEnd_2298962 := by
    simpa [prefixWord, tailWord_2298962, baseEnd_2298962] using wordTrace_append hprefix tailTrace_2298962
  have hstable : (prefixWord ++ tailWord_2298962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298962).length < 2 ^ (prefixWord ++ tailWord_2298962).sum := by decide
  have hdescent : baseEnd_2298962 < baseStart_2298962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298988 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 5, 3]
def baseStart_2298988 : Nat := 118140960795 + 2298988 * 2 ^ 59
def prefixEnd_2298988 : Nat := 4983230072969 + 3 ^ 40 * 2298988 * 2
def baseEnd_2298988 : Nat := 786990575279170955051435

theorem tailTrace_2298988 : CollatzResearch.WordTrace tailWord_2298988 prefixEnd_2298988 786990575279170955051435 := by
  unfold tailWord_2298988
  simp only [CollatzResearch.WordTrace]
  refine ⟨41925490497583293368084809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55900653996777724490779745 41925490497583293368084809)
  ·
    refine ⟨31444117873187470026063607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41925490497583293368084809 31444117873187470026063607)
    ·
      refine ⟨47166176809781205039095411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31444117873187470026063607 47166176809781205039095411)
      ·
        refine ⟨70749265214671807558643117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47166176809781205039095411 70749265214671807558643117)
        ·
          refine ⟨26530974455501927834491169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70749265214671807558643117 26530974455501927834491169)
          ·
            refine ⟨19898230841626445875868377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26530974455501927834491169 19898230841626445875868377)
            ·
              refine ⟨14923673131219834406901283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19898230841626445875868377 14923673131219834406901283)
              ·
                refine ⟨22385509696829751610351925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14923673131219834406901283 22385509696829751610351925)
                ·
                  refine ⟨2098641534077789213470493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22385509696829751610351925 2098641534077789213470493)
                  ·
                    refine ⟨786990575279170955051435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2098641534077789213470493 786990575279170955051435)
                    ·
                      rfl

theorem cell22_2298988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_2298988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2298988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2298988 prefixEnd_2298988 := by exact prefixLift 2298988
  have htrace : WordTrace (prefixWord ++ tailWord_2298988) baseStart_2298988 baseEnd_2298988 := by
    simpa [prefixWord, tailWord_2298988, baseEnd_2298988] using wordTrace_append hprefix tailTrace_2298988
  have hstable : (prefixWord ++ tailWord_2298988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298988).length < 2 ^ (prefixWord ++ tailWord_2298988).sum := by decide
  have hdescent : baseEnd_2298988 < baseStart_2298988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299065 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 1, 4]
def baseStart_2299065 : Nat := 118140960795 + 2299065 * 2 ^ 59
def prefixEnd_2299065 : Nat := 4983230072969 + 3 ^ 40 * 2299065 * 2
def baseEnd_2299065 : Nat := 787016933952768420876199

theorem tailTrace_2299065 : CollatzResearch.WordTrace tailWord_2299065 prefixEnd_2299065 787016933952768420876199 := by
  unfold tailWord_2299065
  simp only [CollatzResearch.WordTrace]
  refine ⟨83853789415887628886722649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55902526277258419257815099 83853789415887628886722649)
  ·
    refine ⟨62890342061915721665041987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83853789415887628886722649 62890342061915721665041987)
    ·
      refine ⟨94335513092873582497562981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62890342061915721665041987 94335513092873582497562981)
      ·
        refine ⟨17687908704913796718293059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94335513092873582497562981 17687908704913796718293059)
        ·
          refine ⟨26531863057370695077439589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17687908704913796718293059 26531863057370695077439589)
          ·
            refine ⟨4974724323257005327019923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26531863057370695077439589 4974724323257005327019923)
            ·
              refine ⟨7462086484885507990529885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4974724323257005327019923 7462086484885507990529885)
              ·
                refine ⟨2798282431832065496448707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7462086484885507990529885 2798282431832065496448707)
                ·
                  refine ⟨4197423647748098244673061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798282431832065496448707 4197423647748098244673061)
                  ·
                    refine ⟨787016933952768420876199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4197423647748098244673061 787016933952768420876199)
                    ·
                      rfl

theorem cell22_2299065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_2299065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299065 prefixEnd_2299065 := by exact prefixLift 2299065
  have htrace : WordTrace (prefixWord ++ tailWord_2299065) baseStart_2299065 baseEnd_2299065 := by
    simpa [prefixWord, tailWord_2299065, baseEnd_2299065] using wordTrace_append hprefix tailTrace_2299065
  have hstable : (prefixWord ++ tailWord_2299065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299065).length < 2 ^ (prefixWord ++ tailWord_2299065).sum := by decide
  have hdescent : baseEnd_2299065 < baseStart_2299065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299080 : List Nat := [2, 1, 3, 1, 2, 1, 4, 4, 4]
def baseStart_2299080 : Nat := 118140960795 + 2299080 * 2 ^ 59
def prefixEnd_2299080 : Nat := 4983230072969 + 3 ^ 40 * 2299080 * 2
def baseEnd_2299080 : Nat := 262340689586437793917051

theorem tailTrace_2299080 : CollatzResearch.WordTrace tailWord_2299080 prefixEnd_2299080 262340689586437793917051 := by
  unfold tailWord_2299080
  simp only [CollatzResearch.WordTrace]
  refine ⟨41927168255416643224259347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55902891007222190965679129 41927168255416643224259347)
  ·
    refine ⟨62890752383124964836389021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41927168255416643224259347 62890752383124964836389021)
    ·
      refine ⟨23584032143671861813645883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62890752383124964836389021 23584032143671861813645883)
      ·
        refine ⟨35376048215507792720468825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23584032143671861813645883 35376048215507792720468825)
        ·
          refine ⟨26532036161630844540351619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35376048215507792720468825 26532036161630844540351619)
          ·
            refine ⟨39798054242446266810527429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26532036161630844540351619 39798054242446266810527429)
            ·
              refine ⟨7462135170458675026973893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39798054242446266810527429 7462135170458675026973893)
              ·
                refine ⟨1399150344461001567557605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7462135170458675026973893 1399150344461001567557605)
                ·
                  refine ⟨262340689586437793917051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399150344461001567557605 262340689586437793917051)
                  ·
                    rfl

theorem cell22_2299080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 4].length) (baseStart_2299080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299080 prefixEnd_2299080 := by exact prefixLift 2299080
  have htrace : WordTrace (prefixWord ++ tailWord_2299080) baseStart_2299080 baseEnd_2299080 := by
    simpa [prefixWord, tailWord_2299080, baseEnd_2299080] using wordTrace_append hprefix tailTrace_2299080
  have hstable : (prefixWord ++ tailWord_2299080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299080).length < 2 ^ (prefixWord ++ tailWord_2299080).sum := by decide
  have hdescent : baseEnd_2299080 < baseStart_2299080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299095 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 2, 3]
def baseStart_2299095 : Nat := 118140960795 + 2299095 * 2 ^ 59
def prefixEnd_2299095 : Nat := 4983230072969 + 3 ^ 40 * 2299095 * 2
def baseEnd_2299095 : Nat := 787027203565858342626107

theorem tailTrace_2299095 : CollatzResearch.WordTrace tailWord_2299095 prefixEnd_2299095 787027203565858342626107 := by
  unfold tailWord_2299095
  simp only [CollatzResearch.WordTrace]
  refine ⟨83854883605778944010314739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55903255737185962673543159 83854883605778944010314739)
  ·
    refine ⟨125782325408668416015472109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83854883605778944010314739 125782325408668416015472109)
    ·
      refine ⟨47168372028250656005802041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125782325408668416015472109 47168372028250656005802041)
      ·
        refine ⟨35376279021187992004351531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47168372028250656005802041 35376279021187992004351531)
        ·
          refine ⟨53064418531781988006527297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35376279021187992004351531 53064418531781988006527297)
          ·
            refine ⟨39798313898836491004895473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53064418531781988006527297 39798313898836491004895473)
            ·
              refine ⟨29848735424127368253671605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39798313898836491004895473 29848735424127368253671605)
              ·
                refine ⟨2798318946011940773781713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29848735424127368253671605 2798318946011940773781713)
                ·
                  refine ⟨2098739209508955580336285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2798318946011940773781713 2098739209508955580336285)
                  ·
                    refine ⟨787027203565858342626107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2098739209508955580336285 787027203565858342626107)
                    ·
                      rfl

theorem cell22_2299095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_2299095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299095 prefixEnd_2299095 := by exact prefixLift 2299095
  have htrace : WordTrace (prefixWord ++ tailWord_2299095) baseStart_2299095 baseEnd_2299095 := by
    simpa [prefixWord, tailWord_2299095, baseEnd_2299095] using wordTrace_append hprefix tailTrace_2299095
  have hstable : (prefixWord ++ tailWord_2299095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299095).length < 2 ^ (prefixWord ++ tailWord_2299095).sum := by decide
  have hdescent : baseEnd_2299095 < baseStart_2299095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299232 : List Nat := [2, 1, 1, 3, 4, 1, 1, 5, 4]
def baseStart_2299232 : Nat := 118140960795 + 2299232 * 2 ^ 59
def prefixEnd_2299232 : Nat := 4983230072969 + 3 ^ 40 * 2299232 * 2
def baseEnd_2299232 : Nat := 262358033821878550650229

theorem tailTrace_2299232 : CollatzResearch.WordTrace tailWord_2299232 prefixEnd_2299232 262358033821878550650229 := by
  unfold tailWord_2299232
  simp only [CollatzResearch.WordTrace]
  refine ⟨41929940203141308204025975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55906586937521744272034633 41929940203141308204025975)
  ·
    refine ⟨62894910304711962306038963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41929940203141308204025975 62894910304711962306038963)
    ·
      refine ⟨94342365457067943459058445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62894910304711962306038963 94342365457067943459058445)
      ·
        refine ⟨35378387046400478797146917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94342365457067943459058445 35378387046400478797146917)
        ·
          refine ⟨6633447571200089774465047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35378387046400478797146917 6633447571200089774465047)
          ·
            refine ⟨9950171356800134661697571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6633447571200089774465047 9950171356800134661697571)
            ·
              refine ⟨14925257035200201992546357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9950171356800134661697571 14925257035200201992546357)
              ·
                refine ⟨1399242847050018936801221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14925257035200201992546357 1399242847050018936801221)
                ·
                  refine ⟨262358033821878550650229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399242847050018936801221 262358033821878550650229)
                  ·
                    rfl

theorem cell22_2299232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 4].length) (baseStart_2299232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299232 prefixEnd_2299232 := by exact prefixLift 2299232
  have htrace : WordTrace (prefixWord ++ tailWord_2299232) baseStart_2299232 baseEnd_2299232 := by
    simpa [prefixWord, tailWord_2299232, baseEnd_2299232] using wordTrace_append hprefix tailTrace_2299232
  have hstable : (prefixWord ++ tailWord_2299232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299232).length < 2 ^ (prefixWord ++ tailWord_2299232).sum := by decide
  have hdescent : baseEnd_2299232 < baseStart_2299232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299294 : List Nat := [4, 3, 1, 2, 2, 2, 8]
def baseStart_2299294 : Nat := 118140960795 + 2299294 * 2 ^ 59
def prefixEnd_2299294 : Nat := 4983230072969 + 3 ^ 40 * 2299294 * 2
def baseEnd_2299294 : Nat := 29151678716025487292611

theorem tailTrace_2299294 : CollatzResearch.WordTrace tailWord_2299294 prefixEnd_2299294 29151678716025487292611 := by
  unfold tailWord_2299294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10482767716507250124601117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55908094488038667331205957 10482767716507250124601117)
  ·
    refine ⟨3931037893690218796725419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10482767716507250124601117 3931037893690218796725419)
    ·
      refine ⟨5896556840535328195088129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3931037893690218796725419 5896556840535328195088129)
      ·
        refine ⟨4422417630401496146316097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5896556840535328195088129 4422417630401496146316097)
        ·
          refine ⟨3316813222801122109737073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4422417630401496146316097 3316813222801122109737073)
          ·
            refine ⟨2487609917100841582302805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3316813222801122109737073 2487609917100841582302805)
            ·
              refine ⟨29151678716025487292611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2487609917100841582302805 29151678716025487292611)
              ·
                rfl

theorem cell22_2299294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 8].length) (baseStart_2299294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299294 prefixEnd_2299294 := by exact prefixLift 2299294
  have htrace : WordTrace (prefixWord ++ tailWord_2299294) baseStart_2299294 baseEnd_2299294 := by
    simpa [prefixWord, tailWord_2299294, baseEnd_2299294] using wordTrace_append hprefix tailTrace_2299294
  have hstable : (prefixWord ++ tailWord_2299294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299294).length < 2 ^ (prefixWord ++ tailWord_2299294).sum := by decide
  have hdescent : baseEnd_2299294 < baseStart_2299294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299320 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_2299320 : Nat := 118140960795 + 2299320 * 2 ^ 59
def prefixEnd_2299320 : Nat := 4983230072969 + 3 ^ 40 * 2299320 * 2
def baseEnd_2299320 : Nat := 787104225664032755750417

theorem tailTrace_2299320 : CollatzResearch.WordTrace tailWord_2299320 prefixEnd_2299320 787104225664032755750417 := by
  unfold tailWord_2299320
  simp only [CollatzResearch.WordTrace]
  refine ⟨41931545014981903718627707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55908726686642538291503609 41931545014981903718627707)
  ·
    refine ⟨62897317522472855577941561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41931545014981903718627707 62897317522472855577941561)
    ·
      refine ⟨47172988141854641683456171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62897317522472855577941561 47172988141854641683456171)
      ·
        refine ⟨70759482212781962525184257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47172988141854641683456171 70759482212781962525184257)
        ·
          refine ⟨53069611659586471893888193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70759482212781962525184257 53069611659586471893888193)
          ·
            refine ⟨39802208744689853920416145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53069611659586471893888193 39802208744689853920416145)
            ·
              refine ⟨29851656558517390440312109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39802208744689853920416145 29851656558517390440312109)
              ·
                refine ⟨11194371209444021415117041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29851656558517390440312109 11194371209444021415117041)
                ·
                  refine ⟨8395778407083016061337781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11194371209444021415117041 8395778407083016061337781)
                  ·
                    refine ⟨787104225664032755750417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8395778407083016061337781 787104225664032755750417)
                    ·
                      rfl

theorem cell22_2299320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_2299320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299320 prefixEnd_2299320 := by exact prefixLift 2299320
  have htrace : WordTrace (prefixWord ++ tailWord_2299320) baseStart_2299320 baseEnd_2299320 := by
    simpa [prefixWord, tailWord_2299320, baseEnd_2299320] using wordTrace_append hprefix tailTrace_2299320
  have hstable : (prefixWord ++ tailWord_2299320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299320).length < 2 ^ (prefixWord ++ tailWord_2299320).sum := by decide
  have hdescent : baseEnd_2299320 < baseStart_2299320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299330 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2299330 : Nat := 118140960795 + 2299330 * 2 ^ 59
def prefixEnd_2299330 : Nat := 4983230072969 + 3 ^ 40 * 2299330 * 2
def baseEnd_2299330 : Nat := 787107648868396063000387

theorem tailTrace_2299330 : CollatzResearch.WordTrace tailWord_2299330 prefixEnd_2299330 787107648868396063000387 := by
  unfold tailWord_2299330
  simp only [CollatzResearch.WordTrace]
  refine ⟨20965863689981894786279861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55908969839951719430079629 20965863689981894786279861)
  ·
    refine ⟨1965549720935802636213737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20965863689981894786279861 1965549720935802636213737)
    ·
      refine ⟨1474162290701851977160303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1965549720935802636213737 1474162290701851977160303)
      ·
        refine ⟨2211243436052777965740455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474162290701851977160303 2211243436052777965740455)
        ·
          refine ⟨3316865154079166948610683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2211243436052777965740455 3316865154079166948610683)
          ·
            refine ⟨4975297731118750422916025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316865154079166948610683 4975297731118750422916025)
            ·
              refine ⟨3731473298339062817187019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4975297731118750422916025 3731473298339062817187019)
              ·
                refine ⟨5597209947508594225780529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3731473298339062817187019 5597209947508594225780529)
                ·
                  refine ⟨4197907460631445669335397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5597209947508594225780529 4197907460631445669335397)
                  ·
                    refine ⟨787107648868396063000387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4197907460631445669335397 787107648868396063000387)
                    ·
                      rfl

theorem cell22_2299330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2299330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299330 prefixEnd_2299330 := by exact prefixLift 2299330
  have htrace : WordTrace (prefixWord ++ tailWord_2299330) baseStart_2299330 baseEnd_2299330 := by
    simpa [prefixWord, tailWord_2299330, baseEnd_2299330] using wordTrace_append hprefix tailTrace_2299330
  have hstable : (prefixWord ++ tailWord_2299330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299330).length < 2 ^ (prefixWord ++ tailWord_2299330).sum := by decide
  have hdescent : baseEnd_2299330 < baseStart_2299330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299352 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 1, 4]
def baseStart_2299352 : Nat := 118140960795 + 2299352 * 2 ^ 59
def prefixEnd_2299352 : Nat := 4983230072969 + 3 ^ 40 * 2299352 * 2
def baseEnd_2299352 : Nat := 787115179917995338950319

theorem tailTrace_2299352 : CollatzResearch.WordTrace tailWord_2299352 prefixEnd_2299352 787115179917995338950319 := by
  unfold tailWord_2299352
  simp only [CollatzResearch.WordTrace]
  refine ⟨41932128582923938451210155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55909504777231917934946873 41932128582923938451210155)
  ·
    refine ⟨62898192874385907676815233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41932128582923938451210155 62898192874385907676815233)
    ·
      refine ⟨47173644655789430757611425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62898192874385907676815233 47173644655789430757611425)
      ·
        refine ⟨35380233491842073068208569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47173644655789430757611425 35380233491842073068208569)
        ·
          refine ⟨26535175118881554801156427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35380233491842073068208569 26535175118881554801156427)
          ·
            refine ⟨39802762678322332201734641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26535175118881554801156427 39802762678322332201734641)
            ·
              refine ⟨29852072008741749151300981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39802762678322332201734641 29852072008741749151300981)
              ·
                refine ⟨2798631750819538982934467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29852072008741749151300981 2798631750819538982934467)
                ·
                  refine ⟨4197947626229308474401701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798631750819538982934467 4197947626229308474401701)
                  ·
                    refine ⟨787115179917995338950319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4197947626229308474401701 787115179917995338950319)
                    ·
                      rfl

theorem cell22_2299352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_2299352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299352 prefixEnd_2299352 := by exact prefixLift 2299352
  have htrace : WordTrace (prefixWord ++ tailWord_2299352) baseStart_2299352 baseEnd_2299352 := by
    simpa [prefixWord, tailWord_2299352, baseEnd_2299352] using wordTrace_append hprefix tailTrace_2299352
  have hstable : (prefixWord ++ tailWord_2299352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299352).length < 2 ^ (prefixWord ++ tailWord_2299352).sum := by decide
  have hdescent : baseEnd_2299352 < baseStart_2299352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299403 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 1, 4]
def baseStart_2299403 : Nat := 118140960795 + 2299403 * 2 ^ 59
def prefixEnd_2299403 : Nat := 4983230072969 + 3 ^ 40 * 2299403 * 2
def baseEnd_2299403 : Nat := 787132638260248205925163

theorem tailTrace_2299403 : CollatzResearch.WordTrace tailWord_2299403 prefixEnd_2299403 787132638260248205925163 := by
  unfold tailWord_2299403
  simp only [CollatzResearch.WordTrace]
  refine ⟨83866117288663112612526863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55910744859108741741684575 83866117288663112612526863)
  ·
    refine ⟨125799175932994668918790295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83866117288663112612526863 125799175932994668918790295)
    ·
      refine ⟨188698763899492003378185443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125799175932994668918790295 188698763899492003378185443)
      ·
        refine ⟨283048145849238005067278165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188698763899492003378185443 283048145849238005067278165)
        ·
          refine ⟨1658485229585378935941083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 283048145849238005067278165 1658485229585378935941083)
          ·
            refine ⟨2487727844378068403911625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658485229585378935941083 2487727844378068403911625)
            ·
              refine ⟨1865795883283551302933719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2487727844378068403911625 1865795883283551302933719)
              ·
                refine ⟨2798693824925326954400579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865795883283551302933719 2798693824925326954400579)
                ·
                  refine ⟨4198040737387990431600869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798693824925326954400579 4198040737387990431600869)
                  ·
                    refine ⟨787132638260248205925163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4198040737387990431600869 787132638260248205925163)
                    ·
                      rfl

theorem cell22_2299403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 4].length) (baseStart_2299403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299403 prefixEnd_2299403 := by exact prefixLift 2299403
  have htrace : WordTrace (prefixWord ++ tailWord_2299403) baseStart_2299403 baseEnd_2299403 := by
    simpa [prefixWord, tailWord_2299403, baseEnd_2299403] using wordTrace_append hprefix tailTrace_2299403
  have hstable : (prefixWord ++ tailWord_2299403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299403).length < 2 ^ (prefixWord ++ tailWord_2299403).sum := by decide
  have hdescent : baseEnd_2299403 < baseStart_2299403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299457 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 9]
def baseStart_2299457 : Nat := 118140960795 + 2299457 * 2 ^ 59
def prefixEnd_2299457 : Nat := 4983230072969 + 3 ^ 40 * 2299457 * 2
def baseEnd_2299457 : Nat := 262383707854603355024999

theorem tailTrace_2299457 : CollatzResearch.WordTrace tailWord_2299457 prefixEnd_2299457 262383707854603355024999 := by
  unfold tailWord_2299457
  simp only [CollatzResearch.WordTrace]
  refine ⟨83868086830467479834992625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55912057886978319889995083 83868086830467479834992625)
  ·
    refine ⟨62901065122850609876244469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83868086830467479834992625 62901065122850609876244469)
    ·
      refine ⟨5896974855267244675897919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62901065122850609876244469 5896974855267244675897919)
      ·
        refine ⟨8845462282900867013846879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5896974855267244675897919 8845462282900867013846879)
        ·
          refine ⟨13268193424351300520770319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8845462282900867013846879 13268193424351300520770319)
          ·
            refine ⟨19902290136526950781155479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13268193424351300520770319 19902290136526950781155479)
            ·
              refine ⟨29853435204790426171733219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19902290136526950781155479 29853435204790426171733219)
              ·
                refine ⟨44780152807185639257599829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29853435204790426171733219 44780152807185639257599829)
                ·
                  refine ⟨262383707854603355024999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44780152807185639257599829 262383707854603355024999)
                  ·
                    rfl

theorem cell22_2299457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_2299457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299457 prefixEnd_2299457 := by exact prefixLift 2299457
  have htrace : WordTrace (prefixWord ++ tailWord_2299457) baseStart_2299457 baseEnd_2299457 := by
    simpa [prefixWord, tailWord_2299457, baseEnd_2299457] using wordTrace_append hprefix tailTrace_2299457
  have hstable : (prefixWord ++ tailWord_2299457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299457).length < 2 ^ (prefixWord ++ tailWord_2299457).sum := by decide
  have hdescent : baseEnd_2299457 < baseStart_2299457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299491 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 5]
def baseStart_2299491 : Nat := 118140960795 + 2299491 * 2 ^ 59
def prefixEnd_2299491 : Nat := 4983230072969 + 3 ^ 40 * 2299491 * 2
def baseEnd_2299491 : Nat := 262387587486215103241631

theorem tailTrace_2299491 : CollatzResearch.WordTrace tailWord_2299491 prefixEnd_2299491 262387587486215103241631 := by
  unfold tailWord_2299491
  simp only [CollatzResearch.WordTrace]
  refine ⟨83869326912344303641730327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55912884608229535761153551 83869326912344303641730327)
  ·
    refine ⟨125803990368516455462595491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83869326912344303641730327 125803990368516455462595491)
    ·
      refine ⟨188705985552774683193893237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125803990368516455462595491 188705985552774683193893237)
      ·
        refine ⟨17691186145572626549427491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188705985552774683193893237 17691186145572626549427491)
        ·
          refine ⟨26536779218358939824141237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17691186145572626549427491 26536779218358939824141237)
          ·
            refine ⟨2487823051721150608513241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26536779218358939824141237 2487823051721150608513241)
            ·
              refine ⟨1865867288790862956384931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2487823051721150608513241 1865867288790862956384931)
              ·
                refine ⟨2798800933186294434577397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865867288790862956384931 2798800933186294434577397)
                ·
                  refine ⟨262387587486215103241631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2798800933186294434577397 262387587486215103241631)
                  ·
                    rfl

theorem cell22_2299491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 5].length) (baseStart_2299491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299491 prefixEnd_2299491 := by exact prefixLift 2299491
  have htrace : WordTrace (prefixWord ++ tailWord_2299491) baseStart_2299491 baseEnd_2299491 := by
    simpa [prefixWord, tailWord_2299491, baseEnd_2299491] using wordTrace_append hprefix tailTrace_2299491
  have hstable : (prefixWord ++ tailWord_2299491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299491).length < 2 ^ (prefixWord ++ tailWord_2299491).sum := by decide
  have hdescent : baseEnd_2299491 < baseStart_2299491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299504 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_2299504 : Nat := 118140960795 + 2299504 * 2 ^ 59
def prefixEnd_2299504 : Nat := 4983230072969 + 3 ^ 40 * 2299504 * 2
def baseEnd_2299504 : Nat := 787167212624317609149853

theorem tailTrace_2299504 : CollatzResearch.WordTrace tailWord_2299504 prefixEnd_2299504 787167212624317609149853 := by
  unfold tailWord_2299504
  simp only [CollatzResearch.WordTrace]
  refine ⟨41934900530648603430976783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55913200707531471241302377 41934900530648603430976783)
  ·
    refine ⟨62902350795972905146465175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41934900530648603430976783 62902350795972905146465175)
    ·
      refine ⟨94353526193959357719697763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62902350795972905146465175 94353526193959357719697763)
      ·
        refine ⟨141530289290939036579546645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94353526193959357719697763 141530289290939036579546645)
        ·
          refine ⟨6634232310512767339666249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 141530289290939036579546645 6634232310512767339666249)
          ·
            refine ⟨4975674232884575504749687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6634232310512767339666249 4975674232884575504749687)
            ·
              refine ⟨7463511349326863257124531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4975674232884575504749687 7463511349326863257124531)
              ·
                refine ⟨11195267023990294885686797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7463511349326863257124531 11195267023990294885686797)
                ·
                  refine ⟨4198225133996360582132549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11195267023990294885686797 4198225133996360582132549)
                  ·
                    refine ⟨787167212624317609149853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4198225133996360582132549 787167212624317609149853)
                    ·
                      rfl

theorem cell22_2299504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_2299504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299504 prefixEnd_2299504 := by exact prefixLift 2299504
  have htrace : WordTrace (prefixWord ++ tailWord_2299504) baseStart_2299504 baseEnd_2299504 := by
    simpa [prefixWord, tailWord_2299504, baseEnd_2299504] using wordTrace_append hprefix tailTrace_2299504
  have hstable : (prefixWord ++ tailWord_2299504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299504).length < 2 ^ (prefixWord ++ tailWord_2299504).sum := by decide
  have hdescent : baseEnd_2299504 < baseStart_2299504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299699 : List Nat := [1, 1, 1, 2, 7, 10]
def baseStart_2299699 : Nat := 118140960795 + 2299699 * 2 ^ 59
def prefixEnd_2299699 : Nat := 4983230072969 + 3 ^ 40 * 2299699 * 2
def baseEnd_2299699 : Nat := 9718937840856816055855

theorem tailTrace_2299699 : CollatzResearch.WordTrace tailWord_2299699 prefixEnd_2299699 9718937840856816055855 := by
  unfold tailWord_2299699
  simp only [CollatzResearch.WordTrace]
  refine ⟨83876913295590755165302151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55917942197060503443534767 83876913295590755165302151)
  ·
    refine ⟨125815369943386132747953227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83876913295590755165302151 125815369943386132747953227)
    ·
      refine ⟨188723054915079199121929841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125815369943386132747953227 188723054915079199121929841)
      ·
        refine ⟨141542291186309399341447381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188723054915079199121929841 141542291186309399341447381)
        ·
          refine ⟨3317397449679126547065173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 141542291186309399341447381 3317397449679126547065173)
          ·
            refine ⟨9718937840856816055855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3317397449679126547065173 9718937840856816055855)
            ·
              rfl

theorem cell22_2299699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 10].length) (baseStart_2299699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299699 prefixEnd_2299699 := by exact prefixLift 2299699
  have htrace : WordTrace (prefixWord ++ tailWord_2299699) baseStart_2299699 baseEnd_2299699 := by
    simpa [prefixWord, tailWord_2299699, baseEnd_2299699] using wordTrace_append hprefix tailTrace_2299699
  have hstable : (prefixWord ++ tailWord_2299699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299699).length < 2 ^ (prefixWord ++ tailWord_2299699).sum := by decide
  have hdescent : baseEnd_2299699 < baseStart_2299699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299705 : List Nat := [1, 2, 1, 7, 1, 1, 1, 4, 4]
def baseStart_2299705 : Nat := 118140960795 + 2299705 * 2 ^ 59
def prefixEnd_2299705 : Nat := 4983230072969 + 3 ^ 40 * 2299705 * 2
def baseEnd_2299705 : Nat := 262412006344006694958079

theorem tailTrace_2299705 : CollatzResearch.WordTrace tailWord_2299705 prefixEnd_2299705 262412006344006694958079 := by
  unfold tailWord_2299705
  simp only [CollatzResearch.WordTrace]
  refine ⟨83877132133569018190020569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55918088089046012126680379 83877132133569018190020569)
  ·
    refine ⟨62907849100176763642515427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83877132133569018190020569 62907849100176763642515427)
    ·
      refine ⟨94361773650265145463773141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62907849100176763642515427 94361773650265145463773141)
      ·
        refine ⟨2211604069928089346807183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 94361773650265145463773141 2211604069928089346807183)
        ·
          refine ⟨3317406104892134020210775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2211604069928089346807183 3317406104892134020210775)
          ·
            refine ⟨4976109157338201030316163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317406104892134020210775 4976109157338201030316163)
            ·
              refine ⟨7464163736007301545474245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976109157338201030316163 7464163736007301545474245)
              ·
                refine ⟨1399530700501369039776421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7464163736007301545474245 1399530700501369039776421)
                ·
                  refine ⟨262412006344006694958079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399530700501369039776421 262412006344006694958079)
                  ·
                    rfl

theorem cell22_2299705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 4].length) (baseStart_2299705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299705 prefixEnd_2299705 := by exact prefixLift 2299705
  have htrace : WordTrace (prefixWord ++ tailWord_2299705) baseStart_2299705 baseEnd_2299705 := by
    simpa [prefixWord, tailWord_2299705, baseEnd_2299705] using wordTrace_append hprefix tailTrace_2299705
  have hstable : (prefixWord ++ tailWord_2299705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299705).length < 2 ^ (prefixWord ++ tailWord_2299705).sum := by decide
  have hdescent : baseEnd_2299705 < baseStart_2299705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299735 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 2, 4]
def baseStart_2299735 : Nat := 118140960795 + 2299735 * 2 ^ 59
def prefixEnd_2299735 : Nat := 4983230072969 + 3 ^ 40 * 2299735 * 2
def baseEnd_2299735 : Nat := 787246288645110006624145

theorem tailTrace_2299735 : CollatzResearch.WordTrace tailWord_2299735 prefixEnd_2299735 787246288645110006624145 := by
  unfold tailWord_2299735
  simp only [CollatzResearch.WordTrace]
  refine ⟨83878226323460333313612659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55918817548973555542408439 83878226323460333313612659)
  ·
    refine ⟨125817339485190499970418989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83878226323460333313612659 125817339485190499970418989)
    ·
      refine ⟨47181502306946437488907121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125817339485190499970418989 47181502306946437488907121)
      ·
        refine ⟨35386126730209828116680341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47181502306946437488907121 35386126730209828116680341)
        ·
          refine ⟨1658724690478585692969391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35386126730209828116680341 1658724690478585692969391)
          ·
            refine ⟨2488087035717878539454087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658724690478585692969391 2488087035717878539454087)
            ·
              refine ⟨3732130553576817809181131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488087035717878539454087 3732130553576817809181131)
              ·
                refine ⟨5598195830365226713771697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732130553576817809181131 5598195830365226713771697)
                ·
                  refine ⟨4198646872773920035328773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5598195830365226713771697 4198646872773920035328773)
                  ·
                    refine ⟨787246288645110006624145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4198646872773920035328773 787246288645110006624145)
                    ·
                      rfl

theorem cell22_2299735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_2299735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299735 prefixEnd_2299735 := by exact prefixLift 2299735
  have htrace : WordTrace (prefixWord ++ tailWord_2299735) baseStart_2299735 baseEnd_2299735 := by
    simpa [prefixWord, tailWord_2299735, baseEnd_2299735] using wordTrace_append hprefix tailTrace_2299735
  have hstable : (prefixWord ++ tailWord_2299735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299735).length < 2 ^ (prefixWord ++ tailWord_2299735).sum := by decide
  have hdescent : baseEnd_2299735 < baseStart_2299735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299754 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 2, 3]
def baseStart_2299754 : Nat := 118140960795 + 2299754 * 2 ^ 59
def prefixEnd_2299754 : Nat := 4983230072969 + 3 ^ 40 * 2299754 * 2
def baseEnd_2299754 : Nat := 787252792733400290399087

theorem tailTrace_2299754 : CollatzResearch.WordTrace tailWord_2299754 prefixEnd_2299754 787252792733400290399087 := by
  unfold tailWord_2299754
  simp only [CollatzResearch.WordTrace]
  refine ⟨20969729827597874889638579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55919279540260999705702877 20969729827597874889638579)
  ·
    refine ⟨31454594741396812334457869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20969729827597874889638579 31454594741396812334457869)
    ·
      refine ⟨11795473028023804625421701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31454594741396812334457869 11795473028023804625421701)
      ·
        refine ⟨2211651192754463367266569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11795473028023804625421701 2211651192754463367266569)
        ·
          refine ⟨1658738394565847525449927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2211651192754463367266569 1658738394565847525449927)
          ·
            refine ⟨2488107591848771288174891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658738394565847525449927 2488107591848771288174891)
            ·
              refine ⟨3732161387773156932262337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488107591848771288174891 3732161387773156932262337)
              ·
                refine ⟨2799121040829867699196753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3732161387773156932262337 2799121040829867699196753)
                ·
                  refine ⟨2099340780622400774397565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2799121040829867699196753 2099340780622400774397565)
                  ·
                    refine ⟨787252792733400290399087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2099340780622400774397565 787252792733400290399087)
                    ·
                      rfl

theorem cell22_2299754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_2299754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299754 prefixEnd_2299754 := by exact prefixLift 2299754
  have htrace : WordTrace (prefixWord ++ tailWord_2299754) baseStart_2299754 baseEnd_2299754 := by
    simpa [prefixWord, tailWord_2299754, baseEnd_2299754] using wordTrace_append hprefix tailTrace_2299754
  have hstable : (prefixWord ++ tailWord_2299754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299754).length < 2 ^ (prefixWord ++ tailWord_2299754).sum := by decide
  have hdescent : baseEnd_2299754 < baseStart_2299754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299765 : List Nat := [1, 3, 4, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2299765 : Nat := 118140960795 + 2299765 * 2 ^ 59
def prefixEnd_2299765 : Nat := 4983230072969 + 3 ^ 40 * 2299765 * 2
def baseEnd_2299765 : Nat := 787256558258199928374053

theorem tailTrace_2299765 : CollatzResearch.WordTrace tailWord_2299765 prefixEnd_2299765 787256558258199928374053 := by
  unfold tailWord_2299765
  simp only [CollatzResearch.WordTrace]
  refine ⟨83879320513351648437204749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55919547008901098958136499 83879320513351648437204749)
  ·
    refine ⟨31454745192506868163951781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83879320513351648437204749 31454745192506868163951781)
    ·
      refine ⟨5897764723595037780740959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31454745192506868163951781 5897764723595037780740959)
      ·
        refine ⟨8846647085392556671111439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5897764723595037780740959 8846647085392556671111439)
        ·
          refine ⟨13269970628088835006667159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8846647085392556671111439 13269970628088835006667159)
          ·
            refine ⟨19904955942133252510000739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13269970628088835006667159 19904955942133252510000739)
            ·
              refine ⟨29857433913199878765001109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19904955942133252510000739 29857433913199878765001109)
              ·
                refine ⟨1399567214681244317109427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29857433913199878765001109 1399567214681244317109427)
                ·
                  refine ⟨2099350822021866475664141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399567214681244317109427 2099350822021866475664141)
                  ·
                    refine ⟨787256558258199928374053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2099350822021866475664141 787256558258199928374053)
                    ·
                      rfl

theorem cell22_2299765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2299765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299765 prefixEnd_2299765 := by exact prefixLift 2299765
  have htrace : WordTrace (prefixWord ++ tailWord_2299765) baseStart_2299765 baseEnd_2299765 := by
    simpa [prefixWord, tailWord_2299765, baseEnd_2299765] using wordTrace_append hprefix tailTrace_2299765
  have hstable : (prefixWord ++ tailWord_2299765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299765).length < 2 ^ (prefixWord ++ tailWord_2299765).sum := by decide
  have hdescent : baseEnd_2299765 < baseStart_2299765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299816 : List Nat := [2, 1, 6, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2299816 : Nat := 118140960795 + 2299816 * 2 ^ 59
def prefixEnd_2299816 : Nat := 4983230072969 + 3 ^ 40 * 2299816 * 2
def baseEnd_2299816 : Nat := 787274016600452795348897

theorem tailTrace_2299816 : CollatzResearch.WordTrace tailWord_2299816 prefixEnd_2299816 787274016600452795348897 := by
  unfold tailWord_2299816
  simp only [CollatzResearch.WordTrace]
  refine ⟨41940590318083442073655651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55920787090777922764874201 41940590318083442073655651)
  ·
    refine ⟨62910885477125163110483477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41940590318083442073655651 62910885477125163110483477)
    ·
      refine ⟨2948947756740242020803913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62910885477125163110483477 2948947756740242020803913)
      ·
        refine ⟨2211710817555181515602935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2948947756740242020803913 2211710817555181515602935)
        ·
          refine ⟨3317566226332772273404403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2211710817555181515602935 3317566226332772273404403)
          ·
            refine ⟨4976349339499158410106605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317566226332772273404403 4976349339499158410106605)
            ·
              refine ⟨1866131002312184403789977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4976349339499158410106605 1866131002312184403789977)
              ·
                refine ⟨1399598251734138302842483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866131002312184403789977 1399598251734138302842483)
                ·
                  refine ⟨2099397377601207454263725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399598251734138302842483 2099397377601207454263725)
                  ·
                    refine ⟨787274016600452795348897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2099397377601207454263725 787274016600452795348897)
                    ·
                      rfl

theorem cell22_2299816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2299816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299816 prefixEnd_2299816 := by exact prefixLift 2299816
  have htrace : WordTrace (prefixWord ++ tailWord_2299816) baseStart_2299816 baseEnd_2299816 := by
    simpa [prefixWord, tailWord_2299816, baseEnd_2299816] using wordTrace_append hprefix tailTrace_2299816
  have hstable : (prefixWord ++ tailWord_2299816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299816).length < 2 ^ (prefixWord ++ tailWord_2299816).sum := by decide
  have hdescent : baseEnd_2299816 < baseStart_2299816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299910 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2299910 : Nat := 118140960795 + 2299910 * 2 ^ 59
def prefixEnd_2299910 : Nat := 4983230072969 + 3 ^ 40 * 2299910 * 2
def baseEnd_2299910 : Nat := 787306194721467883498609

theorem tailTrace_2299910 : CollatzResearch.WordTrace tailWord_2299910 prefixEnd_2299910 787306194721467883498609 := by
  unfold tailWord_2299910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621394034307073068788537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55923072731884225467488789 2621394034307073068788537)
  ·
    refine ⟨1966045525730304801591403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2621394034307073068788537 1966045525730304801591403)
    ·
      refine ⟨2949068288595457202387105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1966045525730304801591403 2949068288595457202387105)
      ·
        refine ⟨2211801216446592901790329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2949068288595457202387105 2211801216446592901790329)
        ·
          refine ⟨1658850912334944676342747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2211801216446592901790329 1658850912334944676342747)
          ·
            refine ⟨2488276368502417014514121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658850912334944676342747 2488276368502417014514121)
            ·
              refine ⟨1866207276376812760885591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488276368502417014514121 1866207276376812760885591)
              ·
                refine ⟨2799310914565219141328387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866207276376812760885591 2799310914565219141328387)
                ·
                  refine ⟨4198966371847828711992581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799310914565219141328387 4198966371847828711992581)
                  ·
                    refine ⟨787306194721467883498609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4198966371847828711992581 787306194721467883498609)
                    ·
                      rfl

theorem cell22_2299910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2299910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299910 prefixEnd_2299910 := by exact prefixLift 2299910
  have htrace : WordTrace (prefixWord ++ tailWord_2299910) baseStart_2299910 baseEnd_2299910 := by
    simpa [prefixWord, tailWord_2299910, baseEnd_2299910] using wordTrace_append hprefix tailTrace_2299910
  have hstable : (prefixWord ++ tailWord_2299910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299910).length < 2 ^ (prefixWord ++ tailWord_2299910).sum := by decide
  have hdescent : baseEnd_2299910 < baseStart_2299910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299930 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_2299930 : Nat := 118140960795 + 2299930 * 2 ^ 59
def prefixEnd_2299930 : Nat := 4983230072969 + 3 ^ 40 * 2299930 * 2
def baseEnd_2299930 : Nat := 262437680376731499332849

theorem tailTrace_2299930 : CollatzResearch.WordTrace tailWord_2299930 prefixEnd_2299930 262437680376731499332849 := by
  unfold tailWord_2299930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20971334639438470404240311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55923559038502587744640829 20971334639438470404240311)
  ·
    refine ⟨31457001959157705606360467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20971334639438470404240311 31457001959157705606360467)
    ·
      refine ⟨47185502938736558409540701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31457001959157705606360467 47185502938736558409540701)
      ·
        refine ⟨17694563602026209403577763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47185502938736558409540701 17694563602026209403577763)
        ·
          refine ⟨26541845403039314105366645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17694563602026209403577763 26541845403039314105366645)
          ·
            refine ⟨2488298006534935697378123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26541845403039314105366645 2488298006534935697378123)
            ·
              refine ⟨3732447009802403546067185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488298006534935697378123 3732447009802403546067185)
              ·
                refine ⟨2799335257351802659550389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3732447009802403546067185 2799335257351802659550389)
                ·
                  refine ⟨262437680376731499332849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2799335257351802659550389 262437680376731499332849)
                  ·
                    rfl

theorem cell22_2299930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_2299930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299930 prefixEnd_2299930 := by exact prefixLift 2299930
  have htrace : WordTrace (prefixWord ++ tailWord_2299930) baseStart_2299930 baseEnd_2299930 := by
    simpa [prefixWord, tailWord_2299930, baseEnd_2299930] using wordTrace_append hprefix tailTrace_2299930
  have hstable : (prefixWord ++ tailWord_2299930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299930).length < 2 ^ (prefixWord ++ tailWord_2299930).sum := by decide
  have hdescent : baseEnd_2299930 < baseStart_2299930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299992 : List Nat := [2, 1, 2, 2, 1, 5, 3, 2, 4]
def baseStart_2299992 : Nat := 118140960795 + 2299992 * 2 ^ 59
def prefixEnd_2299992 : Nat := 4983230072969 + 3 ^ 40 * 2299992 * 2
def baseEnd_2299992 : Nat := 262444754999082334316119

theorem tailTrace_2299992 : CollatzResearch.WordTrace tailWord_2299992 prefixEnd_2299992 262444754999082334316119 := by
  unfold tailWord_2299992
  simp only [CollatzResearch.WordTrace]
  refine ⟨41943799941764633102859115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55925066589019510803812153 41943799941764633102859115)
  ·
    refine ⟨62915699912646949654288673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41943799941764633102859115 62915699912646949654288673)
    ·
      refine ⟨47186774934485212240716505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62915699912646949654288673 47186774934485212240716505)
      ·
        refine ⟨35390081200863909180537379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47186774934485212240716505 35390081200863909180537379)
        ·
          refine ⟨53085121801295863770806069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35390081200863909180537379 53085121801295863770806069)
          ·
            refine ⟨4976730168871487228513069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53085121801295863770806069 4976730168871487228513069)
            ·
              refine ⟨1866273813326807710692401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4976730168871487228513069 1866273813326807710692401)
              ·
                refine ⟨1399705359995105783019301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866273813326807710692401 1399705359995105783019301)
                ·
                  refine ⟨262444754999082334316119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399705359995105783019301 262444754999082334316119)
                  ·
                    rfl

theorem cell22_2299992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 4].length) (baseStart_2299992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299992 prefixEnd_2299992 := by exact prefixLift 2299992
  have htrace : WordTrace (prefixWord ++ tailWord_2299992) baseStart_2299992 baseEnd_2299992 := by
    simpa [prefixWord, tailWord_2299992, baseEnd_2299992] using wordTrace_append hprefix tailTrace_2299992
  have hstable : (prefixWord ++ tailWord_2299992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299992).length < 2 ^ (prefixWord ++ tailWord_2299992).sum := by decide
  have hdescent : baseEnd_2299992 < baseStart_2299992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299998 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2299998 : Nat := 118140960795 + 2299998 * 2 ^ 59
def prefixEnd_2299998 : Nat := 4983230072969 + 3 ^ 40 * 2299998 * 2
def baseEnd_2299998 : Nat := 262445439639954995766113

theorem tailTrace_2299998 : CollatzResearch.WordTrace tailWord_2299998 prefixEnd_2299998 262445439639954995766113 := by
  unfold tailWord_2299998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10485977340188441153804581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55925212481005019486957765 10485977340188441153804581)
  ·
    refine ⟨1966120751285332716338359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10485977340188441153804581 1966120751285332716338359)
    ·
      refine ⟨2949181126927999074507539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1966120751285332716338359 2949181126927999074507539)
      ·
        refine ⟨4423771690391998611761309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2949181126927999074507539 4423771690391998611761309)
        ·
          refine ⟨1658914383896999479410491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4423771690391998611761309 1658914383896999479410491)
          ·
            refine ⟨2488371575845499219115737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658914383896999479410491 2488371575845499219115737)
            ·
              refine ⟨1866278681884124414336803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488371575845499219115737 1866278681884124414336803)
              ·
                refine ⟨2799418022826186621505205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866278681884124414336803 2799418022826186621505205)
                ·
                  refine ⟨262445439639954995766113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2799418022826186621505205 262445439639954995766113)
                  ·
                    rfl

theorem cell22_2299998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2299998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2299998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2299998 prefixEnd_2299998 := by exact prefixLift 2299998
  have htrace : WordTrace (prefixWord ++ tailWord_2299998) baseStart_2299998 baseEnd_2299998 := by
    simpa [prefixWord, tailWord_2299998, baseEnd_2299998] using wordTrace_append hprefix tailTrace_2299998
  have hstable : (prefixWord ++ tailWord_2299998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299998).length < 2 ^ (prefixWord ++ tailWord_2299998).sum := by decide
  have hdescent : baseEnd_2299998 < baseStart_2299998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300022 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_2300022 : Nat := 118140960795 + 2300022 * 2 ^ 59
def prefixEnd_2300022 : Nat := 4983230072969 + 3 ^ 40 * 2300022 * 2
def baseEnd_2300022 : Nat := 787344534610336924698265

theorem tailTrace_2300022 : CollatzResearch.WordTrace tailWord_2300022 prefixEnd_2300022 787344534610336924698265 := by
  unfold tailWord_2300022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5243043379588786333081895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55925796048947054219540213 5243043379588786333081895)
  ·
    refine ⟨7864565069383179499622843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5243043379588786333081895 7864565069383179499622843)
    ·
      refine ⟨11796847604074769249434265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7864565069383179499622843 11796847604074769249434265)
      ·
        refine ⟨8847635703056076937075699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11796847604074769249434265 8847635703056076937075699)
        ·
          refine ⟨13271453554584115405613549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8847635703056076937075699 13271453554584115405613549)
          ·
            refine ⟨4976795082969043277105081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13271453554584115405613549 4976795082969043277105081)
            ·
              refine ⟨3732596312226782457828811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4976795082969043277105081 3732596312226782457828811)
              ·
                refine ⟨5598894468340173686743217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732596312226782457828811 5598894468340173686743217)
                ·
                  refine ⟨4199170851255130265057413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5598894468340173686743217 4199170851255130265057413)
                  ·
                    refine ⟨787344534610336924698265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4199170851255130265057413 787344534610336924698265)
                    ·
                      rfl

theorem cell22_2300022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_2300022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300022 prefixEnd_2300022 := by exact prefixLift 2300022
  have htrace : WordTrace (prefixWord ++ tailWord_2300022) baseStart_2300022 baseEnd_2300022 := by
    simpa [prefixWord, tailWord_2300022, baseEnd_2300022] using wordTrace_append hprefix tailTrace_2300022
  have hstable : (prefixWord ++ tailWord_2300022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300022).length < 2 ^ (prefixWord ++ tailWord_2300022).sum := by decide
  have hdescent : baseEnd_2300022 < baseStart_2300022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300065 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 5]
def baseStart_2300065 : Nat := 118140960795 + 2300065 * 2 ^ 59
def prefixEnd_2300065 : Nat := 4983230072969 + 3 ^ 40 * 2300065 * 2
def baseEnd_2300065 : Nat := 262453084796366381957711

theorem tailTrace_2300065 : CollatzResearch.WordTrace tailWord_2300065 prefixEnd_2300065 262453084796366381957711 := by
  unfold tailWord_2300065
  simp only [CollatzResearch.WordTrace]
  refine ⟨83890262412264799673125649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55926841608176533115417099 83890262412264799673125649)
  ·
    refine ⟨62917696809198599754844237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83890262412264799673125649 62917696809198599754844237)
    ·
      refine ⟨23594136303449474908066589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62917696809198599754844237 23594136303449474908066589)
      ·
        refine ⟨8847801113793553090524971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23594136303449474908066589 8847801113793553090524971)
        ·
          refine ⟨13271701670690329635787457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8847801113793553090524971 13271701670690329635787457)
          ·
            refine ⟨9953776253017747226840593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13271701670690329635787457 9953776253017747226840593)
            ·
              refine ⟨7465332189763310420130445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9953776253017747226840593 7465332189763310420130445)
              ·
                refine ⟨2799499571161241407548917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7465332189763310420130445 2799499571161241407548917)
                ·
                  refine ⟨262453084796366381957711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2799499571161241407548917 262453084796366381957711)
                  ·
                    rfl

theorem cell22_2300065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_2300065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300065 prefixEnd_2300065 := by exact prefixLift 2300065
  have htrace : WordTrace (prefixWord ++ tailWord_2300065) baseStart_2300065 baseEnd_2300065 := by
    simpa [prefixWord, tailWord_2300065, baseEnd_2300065] using wordTrace_append hprefix tailTrace_2300065
  have hstable : (prefixWord ++ tailWord_2300065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300065).length < 2 ^ (prefixWord ++ tailWord_2300065).sum := by decide
  have hdescent : baseEnd_2300065 < baseStart_2300065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300093 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 10]
def baseStart_2300093 : Nat := 118140960795 + 2300093 * 2 ^ 59
def prefixEnd_2300093 : Nat := 4983230072969 + 3 ^ 40 * 2300093 * 2
def baseEnd_2300093 : Nat := 262456279787105468724349

theorem tailTrace_2300093 : CollatzResearch.WordTrace tailWord_2300093 prefixEnd_2300093 262456279787105468724349 := by
  unfold tailWord_2300093
  simp only [CollatzResearch.WordTrace]
  refine ⟨83891283656163360455144933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55927522437442240303429955 83891283656163360455144933)
  ·
    refine ⟨15729615685530630085339675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83891283656163360455144933 15729615685530630085339675)
    ·
      refine ⟨23594423528295945128009513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15729615685530630085339675 23594423528295945128009513)
      ·
        refine ⟨17695817646221958846007135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23594423528295945128009513 17695817646221958846007135)
        ·
          refine ⟨26543726469332938269010703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17695817646221958846007135 26543726469332938269010703)
          ·
            refine ⟨39815589703999407403516055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26543726469332938269010703 39815589703999407403516055)
            ·
              refine ⟨59723384555999111105274083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39815589703999407403516055 59723384555999111105274083)
              ·
                refine ⟨89585076833998666657911125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59723384555999111105274083 89585076833998666657911125)
                ·
                  refine ⟨262456279787105468724349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89585076833998666657911125 262456279787105468724349)
                  ·
                    rfl

theorem cell22_2300093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_2300093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300093 prefixEnd_2300093 := by exact prefixLift 2300093
  have htrace : WordTrace (prefixWord ++ tailWord_2300093) baseStart_2300093 baseEnd_2300093 := by
    simpa [prefixWord, tailWord_2300093, baseEnd_2300093] using wordTrace_append hprefix tailTrace_2300093
  have hstable : (prefixWord ++ tailWord_2300093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300093).length < 2 ^ (prefixWord ++ tailWord_2300093).sum := by decide
  have hdescent : baseEnd_2300093 < baseStart_2300093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300110 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_2300110 : Nat := 118140960795 + 2300110 * 2 ^ 59
def prefixEnd_2300110 : Nat := 4983230072969 + 3 ^ 40 * 2300110 * 2
def baseEnd_2300110 : Nat := 262458219602911342832665

theorem tailTrace_2300110 : CollatzResearch.WordTrace tailWord_2300110 prefixEnd_2300110 262458219602911342832665 := by
  unfold tailWord_2300110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10486487962137721544814223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55927935798067848239009189 10486487962137721544814223)
  ·
    refine ⟨15729731943206582317221335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10486487962137721544814223 15729731943206582317221335)
    ·
      refine ⟨23594597914809873475832003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15729731943206582317221335 23594597914809873475832003)
      ·
        refine ⟨35391896872214810213748005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23594597914809873475832003 35391896872214810213748005)
        ·
          refine ⟨6635980663540276915077751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35391896872214810213748005 6635980663540276915077751)
          ·
            refine ⟨9953970995310415372616627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6635980663540276915077751 9953970995310415372616627)
            ·
              refine ⟨14930956492965623058924941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9953970995310415372616627 14930956492965623058924941)
              ·
                refine ⟨5599108684862108647096853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14930956492965623058924941 5599108684862108647096853)
                ·
                  refine ⟨262458219602911342832665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5599108684862108647096853 262458219602911342832665)
                  ·
                    rfl

theorem cell22_2300110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_2300110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300110 prefixEnd_2300110 := by exact prefixLift 2300110
  have htrace : WordTrace (prefixWord ++ tailWord_2300110) baseStart_2300110 baseEnd_2300110 := by
    simpa [prefixWord, tailWord_2300110, baseEnd_2300110] using wordTrace_append hprefix tailTrace_2300110
  have hstable : (prefixWord ++ tailWord_2300110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300110).length < 2 ^ (prefixWord ++ tailWord_2300110).sum := by decide
  have hdescent : baseEnd_2300110 < baseStart_2300110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300123 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 1, 6]
def baseStart_2300123 : Nat := 118140960795 + 2300123 * 2 ^ 59
def prefixEnd_2300123 : Nat := 4983230072969 + 3 ^ 40 * 2300123 * 2
def baseEnd_2300123 : Nat := 787379108974406327922955

theorem tailTrace_2300123 : CollatzResearch.WordTrace tailWord_2300123 prefixEnd_2300123 787379108974406327922955 := by
  unfold tailWord_2300123
  simp only [CollatzResearch.WordTrace]
  refine ⟨83892377846054675578737023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55928251897369783719158015 83892377846054675578737023)
  ·
    refine ⟨125838566769082013368105535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83892377846054675578737023 125838566769082013368105535)
    ·
      refine ⟨188757850153623020052158303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125838566769082013368105535 188757850153623020052158303)
      ·
        refine ⟨283136775230434530078237455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188757850153623020052158303 283136775230434530078237455)
        ·
          refine ⟨424705162845651795117356183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283136775230434530078237455 424705162845651795117356183)
          ·
            refine ⟨637057744268477692676034275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424705162845651795117356183 637057744268477692676034275)
            ·
              refine ⟨955586616402716539014051413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637057744268477692676034275 955586616402716539014051413)
              ·
                refine ⟨11198280660969334441570915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 955586616402716539014051413 11198280660969334441570915)
                ·
                  refine ⟨16797420991454001662356373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11198280660969334441570915 16797420991454001662356373)
                  ·
                    refine ⟨787379108974406327922955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16797420991454001662356373 787379108974406327922955)
                    ·
                      rfl

theorem cell22_2300123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_2300123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300123 prefixEnd_2300123 := by exact prefixLift 2300123
  have htrace : WordTrace (prefixWord ++ tailWord_2300123) baseStart_2300123 baseEnd_2300123 := by
    simpa [prefixWord, tailWord_2300123, baseEnd_2300123] using wordTrace_append hprefix tailTrace_2300123
  have hstable : (prefixWord ++ tailWord_2300123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300123).length < 2 ^ (prefixWord ++ tailWord_2300123).sum := by decide
  have hdescent : baseEnd_2300123 < baseStart_2300123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300140 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_2300140 : Nat := 118140960795 + 2300140 * 2 ^ 59
def prefixEnd_2300140 : Nat := 4983230072969 + 3 ^ 40 * 2300140 * 2
def baseEnd_2300140 : Nat := 787384928421823950247903

theorem tailTrace_2300140 : CollatzResearch.WordTrace tailWord_2300140 prefixEnd_2300140 787384928421823950247903 := by
  unfold tailWord_2300140
  simp only [CollatzResearch.WordTrace]
  refine ⟨41946498943496543741052937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55928665257995391654737249 41946498943496543741052937)
  ·
    refine ⟨31459874207622407805789703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41946498943496543741052937 31459874207622407805789703)
    ·
      refine ⟨47189811311433611708684555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31459874207622407805789703 47189811311433611708684555)
      ·
        refine ⟨70784716967150417563026833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47189811311433611708684555 70784716967150417563026833)
        ·
          refine ⟨53088537725362813172270125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70784716967150417563026833 53088537725362813172270125)
          ·
            refine ⟨19908201647011054939601297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53088537725362813172270125 19908201647011054939601297)
            ·
              refine ⟨14931151235258291204700973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19908201647011054939601297 14931151235258291204700973)
              ·
                refine ⟨5599181713221859201762865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14931151235258291204700973 5599181713221859201762865)
                ·
                  refine ⟨4199386284916394401322149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5599181713221859201762865 4199386284916394401322149)
                  ·
                    refine ⟨787384928421823950247903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4199386284916394401322149 787384928421823950247903)
                    ·
                      rfl

theorem cell22_2300140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_2300140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300140 prefixEnd_2300140 := by exact prefixLift 2300140
  have htrace : WordTrace (prefixWord ++ tailWord_2300140) baseStart_2300140 baseEnd_2300140 := by
    simpa [prefixWord, tailWord_2300140, baseEnd_2300140] using wordTrace_append hprefix tailTrace_2300140
  have hstable : (prefixWord ++ tailWord_2300140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300140).length < 2 ^ (prefixWord ++ tailWord_2300140).sum := by decide
  have hdescent : baseEnd_2300140 < baseStart_2300140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300217 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 5]
def baseStart_2300217 : Nat := 118140960795 + 2300217 * 2 ^ 59
def prefixEnd_2300217 : Nat := 4983230072969 + 3 ^ 40 * 2300217 * 2
def baseEnd_2300217 : Nat := 262470429031807138690889

theorem tailTrace_2300217 : CollatzResearch.WordTrace tailWord_2300217 prefixEnd_2300217 262470429031807138690889 := by
  unfold tailWord_2300217
  simp only [CollatzResearch.WordTrace]
  refine ⟨83895806307714129632658905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55930537538476086421772603 83895806307714129632658905)
  ·
    refine ⟨62921854730785597224494179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83895806307714129632658905 62921854730785597224494179)
    ·
      refine ⟨94382782096178395836741269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62921854730785597224494179 94382782096178395836741269)
      ·
        refine ⟨4424192910758362304847247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94382782096178395836741269 4424192910758362304847247)
        ·
          refine ⟨6636289366137543457270871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4424192910758362304847247 6636289366137543457270871)
          ·
            refine ⟨9954434049206315185906307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6636289366137543457270871 9954434049206315185906307)
            ·
              refine ⟨14931651073809472778859461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9954434049206315185906307 14931651073809472778859461)
              ·
                refine ⟨2799684576339276146036149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14931651073809472778859461 2799684576339276146036149)
                ·
                  refine ⟨262470429031807138690889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2799684576339276146036149 262470429031807138690889)
                  ·
                    rfl

theorem cell22_2300217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_2300217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300217 prefixEnd_2300217 := by exact prefixLift 2300217
  have htrace : WordTrace (prefixWord ++ tailWord_2300217) baseStart_2300217 baseEnd_2300217 := by
    simpa [prefixWord, tailWord_2300217, baseEnd_2300217] using wordTrace_append hprefix tailTrace_2300217
  have hstable : (prefixWord ++ tailWord_2300217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300217).length < 2 ^ (prefixWord ++ tailWord_2300217).sum := by decide
  have hdescent : baseEnd_2300217 < baseStart_2300217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300247 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 1, 4]
def baseStart_2300247 : Nat := 118140960795 + 2300247 * 2 ^ 59
def prefixEnd_2300247 : Nat := 4983230072969 + 3 ^ 40 * 2300247 * 2
def baseEnd_2300247 : Nat := 787421556708511337822575

theorem tailTrace_2300247 : CollatzResearch.WordTrace tailWord_2300247 prefixEnd_2300247 787421556708511337822575 := by
  unfold tailWord_2300247
  simp only [CollatzResearch.WordTrace]
  refine ⟨83896900497605444756250995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55931266998403629837500663 83896900497605444756250995)
  ·
    refine ⟨125845350746408167134376493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83896900497605444756250995 125845350746408167134376493)
    ·
      refine ⟨47192006529903062675391185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125845350746408167134376493 47192006529903062675391185)
      ·
        refine ⟨35394004897427297006543389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47192006529903062675391185 35394004897427297006543389)
        ·
          refine ⟨13272751836535236377453771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35394004897427297006543389 13272751836535236377453771)
          ·
            refine ⟨19909127754802854566180657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13272751836535236377453771 19909127754802854566180657)
            ·
              refine ⟨14931845816102140924635493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19909127754802854566180657 14931845816102140924635493)
              ·
                refine ⟨2799721090519151423369155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14931845816102140924635493 2799721090519151423369155)
                ·
                  refine ⟨4199581635778727135053733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799721090519151423369155 4199581635778727135053733)
                  ·
                    refine ⟨787421556708511337822575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4199581635778727135053733 787421556708511337822575)
                    ·
                      rfl

theorem cell22_2300247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_2300247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300247 prefixEnd_2300247 := by exact prefixLift 2300247
  have htrace : WordTrace (prefixWord ++ tailWord_2300247) baseStart_2300247 baseEnd_2300247 := by
    simpa [prefixWord, tailWord_2300247, baseEnd_2300247] using wordTrace_append hprefix tailTrace_2300247
  have hstable : (prefixWord ++ tailWord_2300247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300247).length < 2 ^ (prefixWord ++ tailWord_2300247).sum := by decide
  have hdescent : baseEnd_2300247 < baseStart_2300247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300264 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 1, 4]
def baseStart_2300264 : Nat := 118140960795 + 2300264 * 2 ^ 59
def prefixEnd_2300264 : Nat := 4983230072969 + 3 ^ 40 * 2300264 * 2
def baseEnd_2300264 : Nat := 787427376155928960147523

theorem tailTrace_2300264 : CollatzResearch.WordTrace tailWord_2300264 prefixEnd_2300264 787427376155928960147523 := by
  unfold tailWord_2300264
  simp only [CollatzResearch.WordTrace]
  refine ⟨41948760269271928329809923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55931680359029237773079897 41948760269271928329809923)
  ·
    refine ⟨62923140403907892494714885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41948760269271928329809923 62923140403907892494714885)
    ·
      refine ⟨11798088825732729842759041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62923140403907892494714885 11798088825732729842759041)
      ·
        refine ⟨8848566619299547382069281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11798088825732729842759041 8848566619299547382069281)
        ·
          refine ⟨6636424964474660536551961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8848566619299547382069281 6636424964474660536551961)
          ·
            refine ⟨4977318723355995402413971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6636424964474660536551961 4977318723355995402413971)
            ·
              refine ⟨7465978085033993103620957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4977318723355995402413971 7465978085033993103620957)
              ·
                refine ⟨2799741781887747413857859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7465978085033993103620957 2799741781887747413857859)
                ·
                  refine ⟨4199612672831621120786789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799741781887747413857859 4199612672831621120786789)
                  ·
                    refine ⟨787427376155928960147523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4199612672831621120786789 787427376155928960147523)
                    ·
                      rfl

theorem cell22_2300264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_2300264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300264 prefixEnd_2300264 := by exact prefixLift 2300264
  have htrace : WordTrace (prefixWord ++ tailWord_2300264) baseStart_2300264 baseEnd_2300264 := by
    simpa [prefixWord, tailWord_2300264, baseEnd_2300264] using wordTrace_append hprefix tailTrace_2300264
  have hstable : (prefixWord ++ tailWord_2300264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300264).length < 2 ^ (prefixWord ++ tailWord_2300264).sum := by decide
  have hdescent : baseEnd_2300264 < baseStart_2300264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300330 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_2300330 : Nat := 118140960795 + 2300330 * 2 ^ 59
def prefixEnd_2300330 : Nat := 4983230072969 + 3 ^ 40 * 2300330 * 2
def baseEnd_2300330 : Nat := 262483323101575595999107

theorem tailTrace_2300330 : CollatzResearch.WordTrace tailWord_2300330 prefixEnd_2300330 262483323101575595999107 := by
  unfold tailWord_2300330
  simp only [CollatzResearch.WordTrace]
  refine ⟨20974981939076187482880611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55933285170869833287681629 20974981939076187482880611)
  ·
    refine ⟨31462472908614281224320917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20974981939076187482880611 31462472908614281224320917)
    ·
      refine ⟨1474803417591294432390043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31462472908614281224320917 1474803417591294432390043)
      ·
        refine ⟨2212205126386941648585065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474803417591294432390043 2212205126386941648585065)
        ·
          refine ⟨1659153844790206236438799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2212205126386941648585065 1659153844790206236438799)
          ·
            refine ⟨2488730767185309354658199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659153844790206236438799 2488730767185309354658199)
            ·
              refine ⟨3733096150777964031987299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488730767185309354658199 3733096150777964031987299)
              ·
                refine ⟨5599644226166946047980949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3733096150777964031987299 5599644226166946047980949)
                ·
                  refine ⟨262483323101575595999107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5599644226166946047980949 262483323101575595999107)
                  ·
                    rfl

theorem cell22_2300330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_2300330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300330 prefixEnd_2300330 := by exact prefixLift 2300330
  have htrace : WordTrace (prefixWord ++ tailWord_2300330) baseStart_2300330 baseEnd_2300330 := by
    simpa [prefixWord, tailWord_2300330, baseEnd_2300330] using wordTrace_append hprefix tailTrace_2300330
  have hstable : (prefixWord ++ tailWord_2300330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300330).length < 2 ^ (prefixWord ++ tailWord_2300330).sum := by decide
  have hdescent : baseEnd_2300330 < baseStart_2300330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300476 : List Nat := [2, 2, 2, 2, 3, 3, 2, 6]
def baseStart_2300476 : Nat := 118140960795 + 2300476 * 2 ^ 59
def prefixEnd_2300476 : Nat := 4983230072969 + 3 ^ 40 * 2300476 * 2
def baseEnd_2300476 : Nat := 87499994232047897094097

theorem tailTrace_2300476 : CollatzResearch.WordTrace tailWord_2300476 prefixEnd_2300476 87499994232047897094097 := by
  unfold tailWord_2300476
  simp only [CollatzResearch.WordTrace]
  refine ⟨41952626406887908433168641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55936835209183877910891521 41952626406887908433168641)
  ·
    refine ⟨31464469805165931324876481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41952626406887908433168641 31464469805165931324876481)
    ·
      refine ⟨23598352353874448493657361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31464469805165931324876481 23598352353874448493657361)
      ·
        refine ⟨17698764265405836370243021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23598352353874448493657361 17698764265405836370243021)
        ·
          refine ⟨6637036599527188638841133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17698764265405836370243021 6637036599527188638841133)
          ·
            refine ⟨2488888724822695739565425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6637036599527188638841133 2488888724822695739565425)
            ·
              refine ⟨1866666543617021804674069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488888724822695739565425 1866666543617021804674069)
              ·
                refine ⟨87499994232047897094097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1866666543617021804674069 87499994232047897094097)
                ·
                  rfl

theorem cell22_2300476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 6].length) (baseStart_2300476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300476 prefixEnd_2300476 := by exact prefixLift 2300476
  have htrace : WordTrace (prefixWord ++ tailWord_2300476) baseStart_2300476 baseEnd_2300476 := by
    simpa [prefixWord, tailWord_2300476, baseEnd_2300476] using wordTrace_append hprefix tailTrace_2300476
  have hstable : (prefixWord ++ tailWord_2300476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300476).length < 2 ^ (prefixWord ++ tailWord_2300476).sum := by decide
  have hdescent : baseEnd_2300476 < baseStart_2300476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300510 : List Nat := [4, 4, 1, 2, 1, 1, 2, 7]
def baseStart_2300510 : Nat := 118140960795 + 2300510 * 2 ^ 59
def prefixEnd_2300510 : Nat := 4983230072969 + 3 ^ 40 * 2300510 * 2
def baseEnd_2300510 : Nat := 87501287442585146499641

theorem tailTrace_2300510 : CollatzResearch.WordTrace tailWord_2300510 prefixEnd_2300510 87501287442585146499641 := by
  unfold tailWord_2300510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10488311611956580084134373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55937661930435093782049989 10488311611956580084134373)
  ·
    refine ⟨1966558427241858765775195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10488311611956580084134373 1966558427241858765775195)
    ·
      refine ⟨2949837640862788148662793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1966558427241858765775195 2949837640862788148662793)
      ·
        refine ⟨2212378230647091111497095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2949837640862788148662793 2212378230647091111497095)
        ·
          refine ⟨3318567345970636667245643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212378230647091111497095 3318567345970636667245643)
          ·
            refine ⟨4977851018955955000868465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3318567345970636667245643 4977851018955955000868465)
            ·
              refine ⟨3733388264216966250651349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4977851018955955000868465 3733388264216966250651349)
              ·
                refine ⟨87501287442585146499641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3733388264216966250651349 87501287442585146499641)
                ·
                  rfl

theorem cell22_2300510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_2300510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300510 prefixEnd_2300510 := by exact prefixLift 2300510
  have htrace : WordTrace (prefixWord ++ tailWord_2300510) baseStart_2300510 baseEnd_2300510 := by
    simpa [prefixWord, tailWord_2300510, baseEnd_2300510] using wordTrace_append hprefix tailTrace_2300510
  have hstable : (prefixWord ++ tailWord_2300510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300510).length < 2 ^ (prefixWord ++ tailWord_2300510).sum := by decide
  have hdescent : baseEnd_2300510 < baseStart_2300510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300514 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2300514 : Nat := 118140960795 + 2300514 * 2 ^ 59
def prefixEnd_2300514 : Nat := 4983230072969 + 3 ^ 40 * 2300514 * 2
def baseEnd_2300514 : Nat := 787512956265011641396757

theorem tailTrace_2300514 : CollatzResearch.WordTrace tailWord_2300514 prefixEnd_2300514 787512956265011641396757 := by
  unfold tailWord_2300514
  simp only [CollatzResearch.WordTrace]
  refine ⟨20976659696909537339055149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55937759191758766237480397 20976659696909537339055149)
  ·
    refine ⟨7866247386341076502145681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20976659696909537339055149 7866247386341076502145681)
    ·
      refine ⟨5899685539755807376609261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7866247386341076502145681 5899685539755807376609261)
      ·
        refine ⟨2212382077408427766228473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5899685539755807376609261 2212382077408427766228473)
        ·
          refine ⟨1659286558056320824671355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2212382077408427766228473 1659286558056320824671355)
          ·
            refine ⟨2488929837084481237007033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659286558056320824671355 2488929837084481237007033)
            ·
              refine ⟨1866697377813360927755275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488929837084481237007033 1866697377813360927755275)
              ·
                refine ⟨2800046066720041391632913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866697377813360927755275 2800046066720041391632913)
                ·
                  refine ⟨2100034550040031043724685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2800046066720041391632913 2100034550040031043724685)
                  ·
                    refine ⟨787512956265011641396757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2100034550040031043724685 787512956265011641396757)
                    ·
                      rfl

theorem cell22_2300514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2300514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300514 prefixEnd_2300514 := by exact prefixLift 2300514
  have htrace : WordTrace (prefixWord ++ tailWord_2300514) baseStart_2300514 baseEnd_2300514 := by
    simpa [prefixWord, tailWord_2300514, baseEnd_2300514] using wordTrace_append hprefix tailTrace_2300514
  have hstable : (prefixWord ++ tailWord_2300514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300514).length < 2 ^ (prefixWord ++ tailWord_2300514).sum := by decide
  have hdescent : baseEnd_2300514 < baseStart_2300514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300583 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 6]
def baseStart_2300583 : Nat := 118140960795 + 2300583 * 2 ^ 59
def prefixEnd_2300583 : Nat := 4983230072969 + 3 ^ 40 * 2300583 * 2
def baseEnd_2300583 : Nat := 262512192125039487140515

theorem tailTrace_2300583 : CollatzResearch.WordTrace tailWord_2300583 prefixEnd_2300583 262512192125039487140515 := by
  unfold tailWord_2300583
  simp only [CollatzResearch.WordTrace]
  refine ⟨83909155424388174140482403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55939436949592116093654935 83909155424388174140482403)
  ·
    refine ⟨125863733136582261210723605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83909155424388174140482403 125863733136582261210723605)
    ·
      refine ⟨5899862490777293494252669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 125863733136582261210723605 5899862490777293494252669)
      ·
        refine ⟨2212448434041485060344751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5899862490777293494252669 2212448434041485060344751)
        ·
          refine ⟨3318672651062227590517127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212448434041485060344751 3318672651062227590517127)
          ·
            refine ⟨4978008976593341385775691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3318672651062227590517127 4978008976593341385775691)
            ·
              refine ⟨7467013464890012078663537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978008976593341385775691 7467013464890012078663537)
              ·
                refine ⟨5600260098667509058997653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7467013464890012078663537 5600260098667509058997653)
                ·
                  refine ⟨262512192125039487140515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5600260098667509058997653 262512192125039487140515)
                  ·
                    rfl

theorem cell22_2300583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 6].length) (baseStart_2300583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300583 prefixEnd_2300583 := by exact prefixLift 2300583
  have htrace : WordTrace (prefixWord ++ tailWord_2300583) baseStart_2300583 baseEnd_2300583 := by
    simpa [prefixWord, tailWord_2300583, baseEnd_2300583] using wordTrace_append hprefix tailTrace_2300583
  have hstable : (prefixWord ++ tailWord_2300583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300583).length < 2 ^ (prefixWord ++ tailWord_2300583).sum := by decide
  have hdescent : baseEnd_2300583 < baseStart_2300583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300643 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 3, 3]
def baseStart_2300643 : Nat := 118140960795 + 2300643 * 2 ^ 59
def prefixEnd_2300643 : Nat := 4983230072969 + 3 ^ 40 * 2300643 * 2
def baseEnd_2300643 : Nat := 787557115601298304921361

theorem tailTrace_2300643 : CollatzResearch.WordTrace tailWord_2300643 prefixEnd_2300643 787557115601298304921361 := by
  unfold tailWord_2300643
  simp only [CollatzResearch.WordTrace]
  refine ⟨83911343804170804387666583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55940895869447202925111055 83911343804170804387666583)
  ·
    refine ⟨125867015706256206581499875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83911343804170804387666583 125867015706256206581499875)
    ·
      refine ⟨188800523559384309872249813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125867015706256206581499875 188800523559384309872249813)
      ·
        refine ⟨4425012270923069762630855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 188800523559384309872249813 4425012270923069762630855)
        ·
          refine ⟨6637518406384604643946283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425012270923069762630855 6637518406384604643946283)
          ·
            refine ⟨9956277609576906965919425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6637518406384604643946283 9956277609576906965919425)
            ·
              refine ⟨7467208207182680224439569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9956277609576906965919425 7467208207182680224439569)
              ·
                refine ⟨5600406155387010168329677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7467208207182680224439569 5600406155387010168329677)
                ·
                  refine ⟨2100152308270128813123629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5600406155387010168329677 2100152308270128813123629)
                  ·
                    refine ⟨787557115601298304921361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2100152308270128813123629 787557115601298304921361)
                    ·
                      rfl

theorem cell22_2300643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 3].length) (baseStart_2300643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300643 prefixEnd_2300643 := by exact prefixLift 2300643
  have htrace : WordTrace (prefixWord ++ tailWord_2300643) baseStart_2300643 baseEnd_2300643 := by
    simpa [prefixWord, tailWord_2300643, baseEnd_2300643] using wordTrace_append hprefix tailTrace_2300643
  have hstable : (prefixWord ++ tailWord_2300643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300643).length < 2 ^ (prefixWord ++ tailWord_2300643).sum := by decide
  have hdescent : baseEnd_2300643 < baseStart_2300643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300686 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2300686 : Nat := 118140960795 + 2300686 * 2 ^ 59
def prefixEnd_2300686 : Nat := 4983230072969 + 3 ^ 40 * 2300686 * 2
def baseEnd_2300686 : Nat := 787571835380060526096229

theorem tailTrace_2300686 : CollatzResearch.WordTrace tailWord_2300686 prefixEnd_2300686 787571835380060526096229 := by
  unfold tailWord_2300686
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489114017876877841435239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55941941428676681820987941 10489114017876877841435239)
  ·
    refine ⟨15733671026815316762152859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10489114017876877841435239 15733671026815316762152859)
    ·
      refine ⟨23600506540222975143229289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15733671026815316762152859 23600506540222975143229289)
      ·
        refine ⟨17700379905167231357421967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23600506540222975143229289 17700379905167231357421967)
        ·
          refine ⟨26550569857750847036132951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17700379905167231357421967 26550569857750847036132951)
          ·
            refine ⟨39825854786626270554199427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26550569857750847036132951 39825854786626270554199427)
            ·
              refine ⟨59738782179939405831299141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39825854786626270554199427 59738782179939405831299141)
              ·
                refine ⟨11201021658738638593368589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59738782179939405831299141 11201021658738638593368589)
                ·
                  refine ⟨4200383122026989472513221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11201021658738638593368589 4200383122026989472513221)
                  ·
                    refine ⟨787571835380060526096229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4200383122026989472513221 787571835380060526096229)
                    ·
                      rfl

theorem cell22_2300686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2300686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300686 prefixEnd_2300686 := by exact prefixLift 2300686
  have htrace : WordTrace (prefixWord ++ tailWord_2300686) baseStart_2300686 baseEnd_2300686 := by
    simpa [prefixWord, tailWord_2300686, baseEnd_2300686] using wordTrace_append hprefix tailTrace_2300686
  have hstable : (prefixWord ++ tailWord_2300686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300686).length < 2 ^ (prefixWord ++ tailWord_2300686).sum := by decide
  have hdescent : baseEnd_2300686 < baseStart_2300686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300690 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_2300690 : Nat := 118140960795 + 2300690 * 2 ^ 59
def prefixEnd_2300690 : Nat := 4983230072969 + 3 ^ 40 * 2300690 * 2
def baseEnd_2300690 : Nat := 262524401553935282998739

theorem tailTrace_2300690 : CollatzResearch.WordTrace tailWord_2300690 prefixEnd_2300690 262524401553935282998739 := by
  unfold tailWord_2300690
  simp only [CollatzResearch.WordTrace]
  refine ⟨20978264508750132853656881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55942038690000354276418349 20978264508750132853656881)
  ·
    refine ⟨15733698381562599640242661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20978264508750132853656881 15733698381562599640242661)
    ·
      refine ⟨2950068446542987432545499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15733698381562599640242661 2950068446542987432545499)
      ·
        refine ⟨4425102669814481148818249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2950068446542987432545499 4425102669814481148818249)
        ·
          refine ⟨3318827002360860861613687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4425102669814481148818249 3318827002360860861613687)
          ·
            refine ⟨4978240503541291292420531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3318827002360860861613687 4978240503541291292420531)
            ·
              refine ⟨7467360755311936938630797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978240503541291292420531 7467360755311936938630797)
              ·
                refine ⟨2800260283241976351986549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7467360755311936938630797 2800260283241976351986549)
                ·
                  refine ⟨262524401553935282998739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2800260283241976351986549 262524401553935282998739)
                  ·
                    rfl

theorem cell22_2300690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_2300690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300690 prefixEnd_2300690 := by exact prefixLift 2300690
  have htrace : WordTrace (prefixWord ++ tailWord_2300690) baseStart_2300690 baseEnd_2300690 := by
    simpa [prefixWord, tailWord_2300690, baseEnd_2300690] using wordTrace_append hprefix tailTrace_2300690
  have hstable : (prefixWord ++ tailWord_2300690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300690).length < 2 ^ (prefixWord ++ tailWord_2300690).sum := by decide
  have hdescent : baseEnd_2300690 < baseStart_2300690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300703 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 1, 4]
def baseStart_2300703 : Nat := 118140960795 + 2300703 * 2 ^ 59
def prefixEnd_2300703 : Nat := 4983230072969 + 3 ^ 40 * 2300703 * 2
def baseEnd_2300703 : Nat := 787577654827478148421177

theorem tailTrace_2300703 : CollatzResearch.WordTrace tailWord_2300703 prefixEnd_2300703 787577654827478148421177 := by
  unfold tailWord_2300703
  simp only [CollatzResearch.WordTrace]
  refine ⟨83913532183953434634850763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55942354789302289756567175 83913532183953434634850763)
  ·
    refine ⟨125870298275930151952276145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83913532183953434634850763 125870298275930151952276145)
    ·
      refine ⟨94402723706947613964207109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125870298275930151952276145 94402723706947613964207109)
      ·
        refine ⟨17700510695052677618288833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94402723706947613964207109 17700510695052677618288833)
        ·
          refine ⟨13275383021289508213716625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17700510695052677618288833 13275383021289508213716625)
          ·
            refine ⟨9956537265967131160287469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13275383021289508213716625 9956537265967131160287469)
            ·
              refine ⟨3733701474737674185107801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9956537265967131160287469 3733701474737674185107801)
              ·
                refine ⟨2800276106053255638830851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3733701474737674185107801 2800276106053255638830851)
                ·
                  refine ⟨4200414159079883458246277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800276106053255638830851 4200414159079883458246277)
                  ·
                    refine ⟨787577654827478148421177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4200414159079883458246277 787577654827478148421177)
                    ·
                      rfl

theorem cell22_2300703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_2300703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300703 prefixEnd_2300703 := by exact prefixLift 2300703
  have htrace : WordTrace (prefixWord ++ tailWord_2300703) baseStart_2300703 baseEnd_2300703 := by
    simpa [prefixWord, tailWord_2300703, baseEnd_2300703] using wordTrace_append hprefix tailTrace_2300703
  have hstable : (prefixWord ++ tailWord_2300703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300703).length < 2 ^ (prefixWord ++ tailWord_2300703).sum := by decide
  have hdescent : baseEnd_2300703 < baseStart_2300703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300716 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_2300716 : Nat := 118140960795 + 2300716 * 2 ^ 59
def prefixEnd_2300716 : Nat := 4983230072969 + 3 ^ 40 * 2300716 * 2
def baseEnd_2300716 : Nat := 787582104993150447846137

theorem tailTrace_2300716 : CollatzResearch.WordTrace tailWord_2300716 prefixEnd_2300716 787582104993150447846137 := by
  unfold tailWord_2300716
  simp only [CollatzResearch.WordTrace]
  refine ⟨41957003166453168927537001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55942670888604225236716001 41957003166453168927537001)
  ·
    refine ⟨31467752374839876695652751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41957003166453168927537001 31467752374839876695652751)
    ·
      refine ⟨47201628562259815043479127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31467752374839876695652751 47201628562259815043479127)
      ·
        refine ⟨70802442843389722565218691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47201628562259815043479127 70802442843389722565218691)
        ·
          refine ⟨106203664265084583847828037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70802442843389722565218691 106203664265084583847828037)
          ·
            refine ⟨19913187049703359471467757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106203664265084583847828037 19913187049703359471467757)
            ·
              refine ⟨7467445143638759801800409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19913187049703359471467757 7467445143638759801800409)
              ·
                refine ⟨5600583857729069851350307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7467445143638759801800409 5600583857729069851350307)
                ·
                  refine ⟨8400875786593604777025461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5600583857729069851350307 8400875786593604777025461)
                  ·
                    refine ⟨787582104993150447846137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8400875786593604777025461 787582104993150447846137)
                    ·
                      rfl

theorem cell22_2300716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_2300716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300716 prefixEnd_2300716 := by exact prefixLift 2300716
  have htrace : WordTrace (prefixWord ++ tailWord_2300716) baseStart_2300716 baseEnd_2300716 := by
    simpa [prefixWord, tailWord_2300716, baseEnd_2300716] using wordTrace_append hprefix tailTrace_2300716
  have hstable : (prefixWord ++ tailWord_2300716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300716).length < 2 ^ (prefixWord ++ tailWord_2300716).sum := by decide
  have hdescent : baseEnd_2300716 < baseStart_2300716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300729 : List Nat := [1, 2, 1, 18]
def baseStart_2300729 : Nat := 118140960795 + 2300729 * 2 ^ 59
def prefixEnd_2300729 : Nat := 4983230072969 + 3 ^ 40 * 2300729 * 2
def baseEnd_2300729 : Nat := 1080365644936656717793

theorem tailTrace_2300729 : CollatzResearch.WordTrace tailWord_2300729 prefixEnd_2300729 1080365644936656717793 := by
  unfold tailWord_2300729
  simp only [CollatzResearch.WordTrace]
  refine ⟨83914480481859241075297241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55942986987906160716864827 83914480481859241075297241)
  ·
    refine ⟨62935860361394430806472931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83914480481859241075297241 62935860361394430806472931)
    ·
      refine ⟨94403790542091646209709397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62935860361394430806472931 94403790542091646209709397)
      ·
        refine ⟨1080365644936656717793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 18 94403790542091646209709397 1080365644936656717793)
        ·
          rfl

theorem cell22_2300729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 18].length) (baseStart_2300729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300729 prefixEnd_2300729 := by exact prefixLift 2300729
  have htrace : WordTrace (prefixWord ++ tailWord_2300729) baseStart_2300729 baseEnd_2300729 := by
    simpa [prefixWord, tailWord_2300729, baseEnd_2300729] using wordTrace_append hprefix tailTrace_2300729
  have hstable : (prefixWord ++ tailWord_2300729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300729).length < 2 ^ (prefixWord ++ tailWord_2300729).sum := by decide
  have hdescent : baseEnd_2300729 < baseStart_2300729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300735 : List Nat := [1, 1, 2, 2, 5, 1, 4, 2, 4]
def baseStart_2300735 : Nat := 118140960795 + 2300735 * 2 ^ 59
def prefixEnd_2300735 : Nat := 4983230072969 + 3 ^ 40 * 2300735 * 2
def baseEnd_2300735 : Nat := 262529536360480243873693

theorem tailTrace_2300735 : CollatzResearch.WordTrace tailWord_2300735 prefixEnd_2300735 262529536360480243873693 := by
  unfold tailWord_2300735
  simp only [CollatzResearch.WordTrace]
  refine ⟨83914699319837504100015659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55943132879891669400010439 83914699319837504100015659)
  ·
    refine ⟨125872048979756256150023489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83914699319837504100015659 125872048979756256150023489)
    ·
      refine ⟨94404036734817192112517617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125872048979756256150023489 94404036734817192112517617)
      ·
        refine ⟨70803027551112894084388213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94404036734817192112517617 70803027551112894084388213)
        ·
          refine ⟨6637783832916833820411395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70803027551112894084388213 6637783832916833820411395)
          ·
            refine ⟨9956675749375250730617093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6637783832916833820411395 9956675749375250730617093)
            ·
              refine ⟨1866876703007859511990705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9956675749375250730617093 1866876703007859511990705)
              ·
                refine ⟨1400157527255894633993029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866876703007859511990705 1400157527255894633993029)
                ·
                  refine ⟨262529536360480243873693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400157527255894633993029 262529536360480243873693)
                  ·
                    rfl

theorem cell22_2300735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 4].length) (baseStart_2300735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300735 prefixEnd_2300735 := by exact prefixLift 2300735
  have htrace : WordTrace (prefixWord ++ tailWord_2300735) baseStart_2300735 baseEnd_2300735 := by
    simpa [prefixWord, tailWord_2300735, baseEnd_2300735] using wordTrace_append hprefix tailTrace_2300735
  have hstable : (prefixWord ++ tailWord_2300735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300735).length < 2 ^ (prefixWord ++ tailWord_2300735).sum := by decide
  have hdescent : baseEnd_2300735 < baseStart_2300735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300795 : List Nat := [1, 1, 1, 1, 1, 5, 4, 4, 1, 3]
def baseStart_2300795 : Nat := 118140960795 + 2300795 * 2 ^ 59
def prefixEnd_2300795 : Nat := 4983230072969 + 3 ^ 40 * 2300795 * 2
def baseEnd_2300795 : Nat := 787609148307620575120895

theorem tailTrace_2300795 : CollatzResearch.WordTrace tailWord_2300795 prefixEnd_2300795 787609148307620575120895 := by
  unfold tailWord_2300795
  simp only [CollatzResearch.WordTrace]
  refine ⟨83916887699620134347199839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55944591799746756231466559 83916887699620134347199839)
  ·
    refine ⟨125875331549430201520799759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83916887699620134347199839 125875331549430201520799759)
    ·
      refine ⟨188812997324145302281199639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125875331549430201520799759 188812997324145302281199639)
      ·
        refine ⟨283219495986217953421799459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188812997324145302281199639 283219495986217953421799459)
        ·
          refine ⟨424829243979326930132699189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283219495986217953421799459 424829243979326930132699189)
          ·
            refine ⟨39827741623061899699940549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 424829243979326930132699189 39827741623061899699940549)
            ·
              refine ⟨7467701554324106193738853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39827741623061899699940549 7467701554324106193738853)
              ·
                refine ⟨1400194041435769911326035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7467701554324106193738853 1400194041435769911326035)
                ·
                  refine ⟨2100291062153654866989053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400194041435769911326035 2100291062153654866989053)
                  ·
                    refine ⟨787609148307620575120895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2100291062153654866989053 787609148307620575120895)
                    ·
                      rfl

theorem cell22_2300795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 1, 3].length) (baseStart_2300795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300795 prefixEnd_2300795 := by exact prefixLift 2300795
  have htrace : WordTrace (prefixWord ++ tailWord_2300795) baseStart_2300795 baseEnd_2300795 := by
    simpa [prefixWord, tailWord_2300795, baseEnd_2300795] using wordTrace_append hprefix tailTrace_2300795
  have hstable : (prefixWord ++ tailWord_2300795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300795).length < 2 ^ (prefixWord ++ tailWord_2300795).sum := by decide
  have hdescent : baseEnd_2300795 < baseStart_2300795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300851 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 5, 5]
def baseStart_2300851 : Nat := 118140960795 + 2300851 * 2 ^ 59
def prefixEnd_2300851 : Nat := 4983230072969 + 3 ^ 40 * 2300851 * 2
def baseEnd_2300851 : Nat := 787628318252055095720723

theorem tailTrace_2300851 : CollatzResearch.WordTrace tailWord_2300851 prefixEnd_2300851 787628318252055095720723 := by
  unfold tailWord_2300851
  simp only [CollatzResearch.WordTrace]
  refine ⟨83918930187417255911238407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55945953458278170607492271 83918930187417255911238407)
  ·
    refine ⟨125878395281125883866857611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83918930187417255911238407 125878395281125883866857611)
    ·
      refine ⟨188817592921688825800286417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125878395281125883866857611 188817592921688825800286417)
      ·
        refine ⟨141613194691266619350214813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188817592921688825800286417 141613194691266619350214813)
        ·
          refine ⟨53104948009224982256330555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141613194691266619350214813 53104948009224982256330555)
          ·
            refine ⟨79657422013837473384495833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53104948009224982256330555 79657422013837473384495833)
            ·
              refine ⟨59743066510378105038371875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79657422013837473384495833 59743066510378105038371875)
              ·
                refine ⟨89614599765567157557557813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59743066510378105038371875 89614599765567157557557813)
                ·
                  refine ⟨8401368728021921021021045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89614599765567157557557813 8401368728021921021021045)
                  ·
                    refine ⟨787628318252055095720723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8401368728021921021021045 787628318252055095720723)
                    ·
                      rfl

theorem cell22_2300851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_2300851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300851 prefixEnd_2300851 := by exact prefixLift 2300851
  have htrace : WordTrace (prefixWord ++ tailWord_2300851) baseStart_2300851 baseEnd_2300851 := by
    simpa [prefixWord, tailWord_2300851, baseEnd_2300851] using wordTrace_append hprefix tailTrace_2300851
  have hstable : (prefixWord ++ tailWord_2300851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300851).length < 2 ^ (prefixWord ++ tailWord_2300851).sum := by decide
  have hdescent : baseEnd_2300851 < baseStart_2300851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300872 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 1, 4]
def baseStart_2300872 : Nat := 118140960795 + 2300872 * 2 ^ 59
def prefixEnd_2300872 : Nat := 4983230072969 + 3 ^ 40 * 2300872 * 2
def baseEnd_2300872 : Nat := 787635506981218040945659

theorem tailTrace_2300872 : CollatzResearch.WordTrace tailWord_2300872 prefixEnd_2300872 787635506981218040945659 := by
  unfold tailWord_2300872
  simp only [CollatzResearch.WordTrace]
  refine ⟨41959848060170588248876435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55946464080227450998501913 41959848060170588248876435)
  ·
    refine ⟨62939772090255882373314653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41959848060170588248876435 62939772090255882373314653)
    ·
      refine ⟨23602414533845955889992995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62939772090255882373314653 23602414533845955889992995)
      ·
        refine ⟨35403621800768933834989493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23602414533845955889992995 35403621800768933834989493)
        ·
          refine ⟨3319089543822087547030265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35403621800768933834989493 3319089543822087547030265)
          ·
            refine ⟨2489317157866565660272699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3319089543822087547030265 2489317157866565660272699)
            ·
              refine ⟨3733975736799848490409049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489317157866565660272699 3733975736799848490409049)
              ·
                refine ⟨2800481802599886367806787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3733975736799848490409049 2800481802599886367806787)
                ·
                  refine ⟨4200722703899829551710181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800481802599886367806787 4200722703899829551710181)
                  ·
                    refine ⟨787635506981218040945659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4200722703899829551710181 787635506981218040945659)
                    ·
                      rfl

theorem cell22_2300872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_2300872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300872 prefixEnd_2300872 := by exact prefixLift 2300872
  have htrace : WordTrace (prefixWord ++ tailWord_2300872) baseStart_2300872 baseEnd_2300872 := by
    simpa [prefixWord, tailWord_2300872, baseEnd_2300872] using wordTrace_append hprefix tailTrace_2300872
  have hstable : (prefixWord ++ tailWord_2300872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300872).length < 2 ^ (prefixWord ++ tailWord_2300872).sum := by decide
  have hdescent : baseEnd_2300872 < baseStart_2300872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300881 : List Nat := [1, 2, 2, 1, 2, 1, 3, 10]
def baseStart_2300881 : Nat := 118140960795 + 2300881 * 2 ^ 59
def prefixEnd_2300881 : Nat := 4983230072969 + 3 ^ 40 * 2300881 * 2
def baseEnd_2300881 : Nat := 87515398651682779718959

theorem tailTrace_2300881 : CollatzResearch.WordTrace tailWord_2300881 prefixEnd_2300881 87515398651682779718959 := by
  unfold tailWord_2300881
  simp only [CollatzResearch.WordTrace]
  refine ⟨83920024377308571034830497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55946682918205714023220331 83920024377308571034830497)
  ·
    refine ⟨62940018282981428276122873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83920024377308571034830497 62940018282981428276122873)
    ·
      refine ⟨47205013712236071207092155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62940018282981428276122873 47205013712236071207092155)
      ·
        refine ⟨70807520568354106810638233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47205013712236071207092155 70807520568354106810638233)
        ·
          refine ⟨53105640426265580107978675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70807520568354106810638233 53105640426265580107978675)
          ·
            refine ⟨79658460639398370161968013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53105640426265580107978675 79658460639398370161968013)
            ·
              refine ⟨29871922739774388810738005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79658460639398370161968013 29871922739774388810738005)
              ·
                refine ⟨87515398651682779718959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29871922739774388810738005 87515398651682779718959)
                ·
                  rfl

theorem cell22_2300881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 10].length) (baseStart_2300881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300881 prefixEnd_2300881 := by exact prefixLift 2300881
  have htrace : WordTrace (prefixWord ++ tailWord_2300881) baseStart_2300881 baseEnd_2300881 := by
    simpa [prefixWord, tailWord_2300881, baseEnd_2300881] using wordTrace_append hprefix tailTrace_2300881
  have hstable : (prefixWord ++ tailWord_2300881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300881).length < 2 ^ (prefixWord ++ tailWord_2300881).sum := by decide
  have hdescent : baseEnd_2300881 < baseStart_2300881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300885 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_2300885 : Nat := 118140960795 + 2300885 * 2 ^ 59
def prefixEnd_2300885 : Nat := 4983230072969 + 3 ^ 40 * 2300885 * 2
def baseEnd_2300885 : Nat := 787639957146890340370619

theorem tailTrace_2300885 : CollatzResearch.WordTrace tailWord_2300885 prefixEnd_2300885 787639957146890340370619 := by
  unfold tailWord_2300885
  simp only [CollatzResearch.WordTrace]
  refine ⟨83920170269294079717976109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55946780179529386478650739 83920170269294079717976109)
  ·
    refine ⟨31470063850985279894241041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83920170269294079717976109 31470063850985279894241041)
    ·
      refine ⟨23602547888238959920680781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31470063850985279894241041 23602547888238959920680781)
      ·
        refine ⟨8850955458089609970255293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23602547888238959920680781 8850955458089609970255293)
        ·
          refine ⟨3319108296783603738845735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8850955458089609970255293 3319108296783603738845735)
          ·
            refine ⟨4978662445175405608268603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3319108296783603738845735 4978662445175405608268603)
            ·
              refine ⟨7467993667763108412402905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978662445175405608268603 7467993667763108412402905)
              ·
                refine ⟨5600995250822331309302179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7467993667763108412402905 5600995250822331309302179)
                ·
                  refine ⟨8401492876233496963953269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5600995250822331309302179 8401492876233496963953269)
                  ·
                    refine ⟨787639957146890340370619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8401492876233496963953269 787639957146890340370619)
                    ·
                      rfl

theorem cell22_2300885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_2300885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300885 prefixEnd_2300885 := by exact prefixLift 2300885
  have htrace : WordTrace (prefixWord ++ tailWord_2300885) baseStart_2300885 baseEnd_2300885 := by
    simpa [prefixWord, tailWord_2300885, baseEnd_2300885] using wordTrace_append hprefix tailTrace_2300885
  have hstable : (prefixWord ++ tailWord_2300885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300885).length < 2 ^ (prefixWord ++ tailWord_2300885).sum := by decide
  have hdescent : baseEnd_2300885 < baseStart_2300885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300964 : List Nat := [2, 3, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_2300964 : Nat := 118140960795 + 2300964 * 2 ^ 59
def prefixEnd_2300964 : Nat := 4983230072969 + 3 ^ 40 * 2300964 * 2
def baseEnd_2300964 : Nat := 787667000461360467645377

theorem tailTrace_2300964 : CollatzResearch.WordTrace tailWord_2300964 prefixEnd_2300964 787667000461360467645377 := by
  unfold tailWord_2300964
  simp only [CollatzResearch.WordTrace]
  refine ⟨41961525818003938105050973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55948701090671917473401297 41961525818003938105050973)
  ·
    refine ⟨15735572181751476789394115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41961525818003938105050973 15735572181751476789394115)
    ·
      refine ⟨23603358272627215184091173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15735572181751476789394115 23603358272627215184091173)
      ·
        refine ⟨4425629676117602847017095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23603358272627215184091173 4425629676117602847017095)
        ·
          refine ⟨6638444514176404270525643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425629676117602847017095 6638444514176404270525643)
          ·
            refine ⟨9957666771264606405788465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6638444514176404270525643 9957666771264606405788465)
            ·
              refine ⟨7468250078448454804341349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9957666771264606405788465 7468250078448454804341349)
              ·
                refine ⟨1400296889709085275814003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7468250078448454804341349 1400296889709085275814003)
                ·
                  refine ⟨2100445334563627913721005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400296889709085275814003 2100445334563627913721005)
                  ·
                    refine ⟨787667000461360467645377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2100445334563627913721005 787667000461360467645377)
                    ·
                      rfl

theorem cell22_2300964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_2300964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300964 prefixEnd_2300964 := by exact prefixLift 2300964
  have htrace : WordTrace (prefixWord ++ tailWord_2300964) baseStart_2300964 baseEnd_2300964 := by
    simpa [prefixWord, tailWord_2300964, baseEnd_2300964] using wordTrace_append hprefix tailTrace_2300964
  have hstable : (prefixWord ++ tailWord_2300964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300964).length < 2 ^ (prefixWord ++ tailWord_2300964).sum := by decide
  have hdescent : baseEnd_2300964 < baseStart_2300964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2300998 : List Nat := [6, 1, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2300998 : Nat := 118140960795 + 2300998 * 2 ^ 59
def prefixEnd_2300998 : Nat := 4983230072969 + 3 ^ 40 * 2300998 * 2
def baseEnd_2300998 : Nat := 787678639356195712295273

theorem tailTrace_2300998 : CollatzResearch.WordTrace tailWord_2300998 prefixEnd_2300998 787678639356195712295273 := by
  unfold tailWord_2300998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622634116183896875526239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55949527811923133344559765 2622634116183896875526239)
  ·
    refine ⟨3933951174275845313289359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2622634116183896875526239 3933951174275845313289359)
    ·
      refine ⟨5900926761413767969934039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3933951174275845313289359 5900926761413767969934039)
      ·
        refine ⟨8851390142120651954901059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5900926761413767969934039 8851390142120651954901059)
        ·
          refine ⟨13277085213180977932351589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8851390142120651954901059 13277085213180977932351589)
          ·
            refine ⟨2489453477471433362315923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13277085213180977932351589 2489453477471433362315923)
            ·
              refine ⟨3734180216207150043473885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489453477471433362315923 3734180216207150043473885)
              ·
                refine ⟨1400317581077681266302707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3734180216207150043473885 1400317581077681266302707)
                ·
                  refine ⟨2100476371616521899454061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400317581077681266302707 2100476371616521899454061)
                  ·
                    refine ⟨787678639356195712295273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2100476371616521899454061 787678639356195712295273)
                    ·
                      rfl

theorem cell22_2300998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2300998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2300998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2300998 prefixEnd_2300998 := by exact prefixLift 2300998
  have htrace : WordTrace (prefixWord ++ tailWord_2300998) baseStart_2300998 baseEnd_2300998 := by
    simpa [prefixWord, tailWord_2300998, baseEnd_2300998] using wordTrace_append hprefix tailTrace_2300998
  have hstable : (prefixWord ++ tailWord_2300998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2300998).length < 2 ^ (prefixWord ++ tailWord_2300998).sum := by decide
  have hdescent : baseEnd_2300998 < baseStart_2300998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2300998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301018 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_2301018 : Nat := 118140960795 + 2301018 * 2 ^ 59
def prefixEnd_2301018 : Nat := 4983230072969 + 3 ^ 40 * 2301018 * 2
def baseEnd_2301018 : Nat := 787685485764922326795211

theorem tailTrace_2301018 : CollatzResearch.WordTrace tailWord_2301018 prefixEnd_2301018 787685485764922326795211 := by
  unfold tailWord_2301018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20981255294453060858141927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55950014118541495621711805 20981255294453060858141927)
  ·
    refine ⟨31471882941679591287212891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20981255294453060858141927 31471882941679591287212891)
    ·
      refine ⟨47207824412519386930819337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31471882941679591287212891 47207824412519386930819337)
      ·
        refine ⟨35405868309389540198114503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47207824412519386930819337 35405868309389540198114503)
        ·
          refine ⟨53108802464084310297171755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35405868309389540198114503 53108802464084310297171755)
          ·
            refine ⟨79663203696126465445757633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53108802464084310297171755 79663203696126465445757633)
            ·
              refine ⟨59747402772094849084318225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79663203696126465445757633 59747402772094849084318225)
              ·
                refine ⟨44810552079071136813238669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59747402772094849084318225 44810552079071136813238669)
                ·
                  refine ⟨16803957029651676304964501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44810552079071136813238669 16803957029651676304964501)
                  ·
                    refine ⟨787685485764922326795211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16803957029651676304964501 787685485764922326795211)
                    ·
                      rfl

theorem cell22_2301018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_2301018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301018 prefixEnd_2301018 := by exact prefixLift 2301018
  have htrace : WordTrace (prefixWord ++ tailWord_2301018) baseStart_2301018 baseEnd_2301018 := by
    simpa [prefixWord, tailWord_2301018, baseEnd_2301018] using wordTrace_append hprefix tailTrace_2301018
  have hstable : (prefixWord ++ tailWord_2301018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301018).length < 2 ^ (prefixWord ++ tailWord_2301018).sum := by decide
  have hdescent : baseEnd_2301018 < baseStart_2301018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301033 : List Nat := [1, 2, 1, 1, 1, 6, 1, 9]
def baseStart_2301033 : Nat := 118140960795 + 2301033 * 2 ^ 59
def prefixEnd_2301033 : Nat := 4983230072969 + 3 ^ 40 * 2301033 * 2
def baseEnd_2301033 : Nat := 87521180063496365296685

theorem tailTrace_2301033 : CollatzResearch.WordTrace tailWord_2301033 prefixEnd_2301033 87521180063496365296685 := by
  unfold tailWord_2301033
  simp only [CollatzResearch.WordTrace]
  refine ⟨83925568272757900994363753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55950378848505267329575835 83925568272757900994363753)
  ·
    refine ⟨62944176204568425745772815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83925568272757900994363753 62944176204568425745772815)
    ·
      refine ⟨94416264306852638618659223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62944176204568425745772815 94416264306852638618659223)
      ·
        refine ⟨141624396460278957927988835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94416264306852638618659223 141624396460278957927988835)
        ·
          refine ⟨212436594690418436891983253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141624396460278957927988835 212436594690418436891983253)
          ·
            refine ⟨9957965376113364229311715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 212436594690418436891983253 9957965376113364229311715)
            ·
              refine ⟨14936948064170046343967573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9957965376113364229311715 14936948064170046343967573)
              ·
                refine ⟨87521180063496365296685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14936948064170046343967573 87521180063496365296685)
                ·
                  rfl

theorem cell22_2301033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 9].length) (baseStart_2301033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301033 prefixEnd_2301033 := by exact prefixLift 2301033
  have htrace : WordTrace (prefixWord ++ tailWord_2301033) baseStart_2301033 baseEnd_2301033 := by
    simpa [prefixWord, tailWord_2301033, baseEnd_2301033] using wordTrace_append hprefix tailTrace_2301033
  have hstable : (prefixWord ++ tailWord_2301033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301033).length < 2 ^ (prefixWord ++ tailWord_2301033).sum := by decide
  have hdescent : baseEnd_2301033 < baseStart_2301033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301048 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_2301048 : Nat := 118140960795 + 2301048 * 2 ^ 59
def prefixEnd_2301048 : Nat := 4983230072969 + 3 ^ 40 * 2301048 * 2
def baseEnd_2301048 : Nat := 787695755378012248545119

theorem tailTrace_2301048 : CollatzResearch.WordTrace tailWord_2301048 prefixEnd_2301048 787695755378012248545119 := by
  unfold tailWord_2301048
  simp only [CollatzResearch.WordTrace]
  refine ⟨41963057683851779278079899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55950743578469039037439865 41963057683851779278079899)
  ·
    refine ⟨62944586525777668917119849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41963057683851779278079899 62944586525777668917119849)
    ·
      refine ⟨47208439894333251687839887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62944586525777668917119849 47208439894333251687839887)
      ·
        refine ⟨70812659841499877531759831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47208439894333251687839887 70812659841499877531759831)
        ·
          refine ⟨106218989762249816297639747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70812659841499877531759831 106218989762249816297639747)
          ·
            refine ⟨159328484643374724446459621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106218989762249816297639747 159328484643374724446459621)
            ·
              refine ⟨29874090870632760833711179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159328484643374724446459621 29874090870632760833711179)
              ·
                refine ⟨44811136305949141250566769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29874090870632760833711179 44811136305949141250566769)
                ·
                  refine ⟨33608352229461855937925077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44811136305949141250566769 33608352229461855937925077)
                  ·
                    refine ⟨787695755378012248545119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33608352229461855937925077 787695755378012248545119)
                    ·
                      rfl

theorem cell22_2301048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_2301048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301048 prefixEnd_2301048 := by exact prefixLift 2301048
  have htrace : WordTrace (prefixWord ++ tailWord_2301048) baseStart_2301048 baseEnd_2301048 := by
    simpa [prefixWord, tailWord_2301048, baseEnd_2301048] using wordTrace_append hprefix tailTrace_2301048
  have hstable : (prefixWord ++ tailWord_2301048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301048).length < 2 ^ (prefixWord ++ tailWord_2301048).sum := by decide
  have hdescent : baseEnd_2301048 < baseStart_2301048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301080 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_2301080 : Nat := 118140960795 + 2301080 * 2 ^ 59
def prefixEnd_2301080 : Nat := 4983230072969 + 3 ^ 40 * 2301080 * 2
def baseEnd_2301080 : Nat := 787706709631974831745021

theorem tailTrace_2301080 : CollatzResearch.WordTrace tailWord_2301080 prefixEnd_2301080 787706709631974831745021 := by
  unfold tailWord_2301080
  simp only [CollatzResearch.WordTrace]
  refine ⟨41963641251793814010662347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55951521669058418680883129 41963641251793814010662347)
  ·
    refine ⟨62945461877690721015993521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41963641251793814010662347 62945461877690721015993521)
    ·
      refine ⟨47209096408268040761995141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62945461877690721015993521 47209096408268040761995141)
      ·
        refine ⟨8851705576550257642874089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47209096408268040761995141 8851705576550257642874089)
        ·
          refine ⟨6638779182412693232155567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8851705576550257642874089 6638779182412693232155567)
          ·
            refine ⟨9958168773619039848233351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6638779182412693232155567 9958168773619039848233351)
            ·
              refine ⟨14937253160428559772350027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9958168773619039848233351 14937253160428559772350027)
              ·
                refine ⟨22405879740642839658525041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14937253160428559772350027 22405879740642839658525041)
                ·
                  refine ⟨16804409805482129743893781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22405879740642839658525041 16804409805482129743893781)
                  ·
                    refine ⟨787706709631974831745021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16804409805482129743893781 787706709631974831745021)
                    ·
                      rfl

theorem cell22_2301080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_2301080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301080 prefixEnd_2301080 := by exact prefixLift 2301080
  have htrace : WordTrace (prefixWord ++ tailWord_2301080) baseStart_2301080 baseEnd_2301080 := by
    simpa [prefixWord, tailWord_2301080, baseEnd_2301080] using wordTrace_append hprefix tailTrace_2301080
  have hstable : (prefixWord ++ tailWord_2301080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301080).length < 2 ^ (prefixWord ++ tailWord_2301080).sum := by decide
  have hdescent : baseEnd_2301080 < baseStart_2301080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301116 : List Nat := [2, 2, 2, 3, 2, 2, 2, 3, 1, 3]
def baseStart_2301116 : Nat := 118140960795 + 2301116 * 2 ^ 59
def prefixEnd_2301116 : Nat := 4983230072969 + 3 ^ 40 * 2301116 * 2
def baseEnd_2301116 : Nat := 787719033167682737844911

theorem tailTrace_2301116 : CollatzResearch.WordTrace tailWord_2301116 prefixEnd_2301116 787719033167682737844911 := by
  unfold tailWord_2301116
  simp only [CollatzResearch.WordTrace]
  refine ⟨41964297765728603084817601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55952397020971470779756801 41964297765728603084817601)
  ·
    refine ⟨31473223324296452313613201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41964297765728603084817601 31473223324296452313613201)
    ·
      refine ⟨23604917493222339235209901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31473223324296452313613201 23604917493222339235209901)
      ·
        refine ⟨8851844059958377213203713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23604917493222339235209901 8851844059958377213203713)
        ·
          refine ⟨6638883044968782909902785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8851844059958377213203713 6638883044968782909902785)
          ·
            refine ⟨4979162283726587182427089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6638883044968782909902785 4979162283726587182427089)
            ·
              refine ⟨3734371712794940386820317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4979162283726587182427089 3734371712794940386820317)
              ·
                refine ⟨1400389392298102645057619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3734371712794940386820317 1400389392298102645057619)
                ·
                  refine ⟨2100584088447153967586429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400389392298102645057619 2100584088447153967586429)
                  ·
                    refine ⟨787719033167682737844911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2100584088447153967586429 787719033167682737844911)
                    ·
                      rfl

theorem cell22_2301116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_2301116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301116 prefixEnd_2301116 := by exact prefixLift 2301116
  have htrace : WordTrace (prefixWord ++ tailWord_2301116) baseStart_2301116 baseEnd_2301116 := by
    simpa [prefixWord, tailWord_2301116, baseEnd_2301116] using wordTrace_append hprefix tailTrace_2301116
  have hstable : (prefixWord ++ tailWord_2301116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301116).length < 2 ^ (prefixWord ++ tailWord_2301116).sum := by decide
  have hdescent : baseEnd_2301116 < baseStart_2301116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301133 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2301133 : Nat := 118140960795 + 2301133 * 2 ^ 59
def prefixEnd_2301133 : Nat := 4983230072969 + 3 ^ 40 * 2301133 * 2
def baseEnd_2301133 : Nat := 787724852615100360169859

theorem tailTrace_2301133 : CollatzResearch.WordTrace tailWord_2301133 prefixEnd_2301133 787724852615100360169859 := by
  unfold tailWord_2301133
  simp only [CollatzResearch.WordTrace]
  refine ⟨83929215572395618073004053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55952810381597078715336035 83929215572395618073004053)
  ·
    refine ⟨3934181979956044597172065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83929215572395618073004053 3934181979956044597172065)
    ·
      refine ⟨2950636484967033447879049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3934181979956044597172065 2950636484967033447879049)
      ·
        refine ⟨2212977363725275085909287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2950636484967033447879049 2212977363725275085909287)
        ·
          refine ⟨3319466045587912628863931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212977363725275085909287 3319466045587912628863931)
          ·
            refine ⟨4979199068381868943295897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3319466045587912628863931 4979199068381868943295897)
            ·
              refine ⟨3734399301286401707471923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4979199068381868943295897 3734399301286401707471923)
              ·
                refine ⟨5601598951929602561207885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3734399301286401707471923 5601598951929602561207885)
                ·
                  refine ⟨2100599606973600960452957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5601598951929602561207885 2100599606973600960452957)
                  ·
                    refine ⟨787724852615100360169859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2100599606973600960452957 787724852615100360169859)
                    ·
                      rfl

theorem cell22_2301133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2301133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301133 prefixEnd_2301133 := by exact prefixLift 2301133
  have htrace : WordTrace (prefixWord ++ tailWord_2301133) baseStart_2301133 baseEnd_2301133 := by
    simpa [prefixWord, tailWord_2301133, baseEnd_2301133] using wordTrace_append hprefix tailTrace_2301133
  have hstable : (prefixWord ++ tailWord_2301133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301133).length < 2 ^ (prefixWord ++ tailWord_2301133).sum := by decide
  have hdescent : baseEnd_2301133 < baseStart_2301133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301185 : List Nat := [1, 2, 4, 1, 1, 3, 10]
def baseStart_2301185 : Nat := 118140960795 + 2301185 * 2 ^ 59
def prefixEnd_2301185 : Nat := 4983230072969 + 3 ^ 40 * 2301185 * 2
def baseEnd_2301185 : Nat := 29175653825103316958137

theorem tailTrace_2301185 : CollatzResearch.WordTrace tailWord_2301185 prefixEnd_2301185 29175653825103316958137 := by
  unfold tailWord_2301185
  simp only [CollatzResearch.WordTrace]
  refine ⟨83931112168207230953897009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55954074778804820635931339 83931112168207230953897009)
  ·
    refine ⟨62948334126155423215422757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83931112168207230953897009 62948334126155423215422757)
    ·
      refine ⟨11802812648654141852891767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62948334126155423215422757 11802812648654141852891767)
      ·
        refine ⟨17704218972981212779337651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11802812648654141852891767 17704218972981212779337651)
        ·
          refine ⟨26556328459471819169006477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17704218972981212779337651 26556328459471819169006477)
          ·
            refine ⟨9958623172301932188377429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26556328459471819169006477 9958623172301932188377429)
            ·
              refine ⟨29175653825103316958137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9958623172301932188377429 29175653825103316958137)
              ·
                rfl

theorem cell22_2301185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 10].length) (baseStart_2301185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301185 prefixEnd_2301185 := by exact prefixLift 2301185
  have htrace : WordTrace (prefixWord ++ tailWord_2301185) baseStart_2301185 baseEnd_2301185 := by
    simpa [prefixWord, tailWord_2301185, baseEnd_2301185] using wordTrace_append hprefix tailTrace_2301185
  have hstable : (prefixWord ++ tailWord_2301185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301185).length < 2 ^ (prefixWord ++ tailWord_2301185).sum := by decide
  have hdescent : baseEnd_2301185 < baseStart_2301185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301187 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 2, 4]
def baseStart_2301187 : Nat := 118140960795 + 2301187 * 2 ^ 59
def prefixEnd_2301187 : Nat := 4983230072969 + 3 ^ 40 * 2301187 * 2
def baseEnd_2301187 : Nat := 787743337918662219319693

theorem tailTrace_2301187 : CollatzResearch.WordTrace tailWord_2301187 prefixEnd_2301187 787743337918662219319693 := by
  unfold tailWord_2301187
  simp only [CollatzResearch.WordTrace]
  refine ⟨83931185114199985295469815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55954123409466656863646543 83931185114199985295469815)
  ·
    refine ⟨125896777671299977943204723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83931185114199985295469815 125896777671299977943204723)
    ·
      refine ⟨188845166506949966914807085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125896777671299977943204723 188845166506949966914807085)
      ·
        refine ⟨70816937440106237593052657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188845166506949966914807085 70816937440106237593052657)
        ·
          refine ⟨53112703080079678194789493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70816937440106237593052657 53112703080079678194789493)
          ·
            refine ⟨4979315913757469830761515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53112703080079678194789493 4979315913757469830761515)
            ·
              refine ⟨7468973870636204746142273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4979315913757469830761515 7468973870636204746142273)
              ·
                refine ⟨5601730402977153559606705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7468973870636204746142273 5601730402977153559606705)
                ·
                  refine ⟨4201297802232865169705029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5601730402977153559606705 4201297802232865169705029)
                  ·
                    refine ⟨787743337918662219319693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4201297802232865169705029 787743337918662219319693)
                    ·
                      rfl

theorem cell22_2301187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 4].length) (baseStart_2301187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301187 prefixEnd_2301187 := by exact prefixLift 2301187
  have htrace : WordTrace (prefixWord ++ tailWord_2301187) baseStart_2301187 baseEnd_2301187 := by
    simpa [prefixWord, tailWord_2301187, baseEnd_2301187] using wordTrace_append hprefix tailTrace_2301187
  have hstable : (prefixWord ++ tailWord_2301187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301187).length < 2 ^ (prefixWord ++ tailWord_2301187).sum := by decide
  have hdescent : baseEnd_2301187 < baseStart_2301187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301217 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 5, 3]
def baseStart_2301217 : Nat := 118140960795 + 2301217 * 2 ^ 59
def prefixEnd_2301217 : Nat := 4983230072969 + 3 ^ 40 * 2301217 * 2
def baseEnd_2301217 : Nat := 787753607531752141069601

theorem tailTrace_2301217 : CollatzResearch.WordTrace tailWord_2301217 prefixEnd_2301217 787753607531752141069601 := by
  unfold tailWord_2301217
  simp only [CollatzResearch.WordTrace]
  refine ⟨83932279304091300419061905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55954852869394200279374603 83932279304091300419061905)
  ·
    refine ⟨62949209478068475314296429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83932279304091300419061905 62949209478068475314296429)
    ·
      refine ⟨23605953554275678242861161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62949209478068475314296429 23605953554275678242861161)
      ·
        refine ⟨17704465165706758682145871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23605953554275678242861161 17704465165706758682145871)
        ·
          refine ⟨26556697748560138023218807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17704465165706758682145871 26556697748560138023218807)
          ·
            refine ⟨39835046622840207034828211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26556697748560138023218807 39835046622840207034828211)
            ·
              refine ⟨59752569934260310552242317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39835046622840207034828211 59752569934260310552242317)
              ·
                refine ⟨22407213725347616457090869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59752569934260310552242317 22407213725347616457090869)
                ·
                  refine ⟨2100676286751339042852269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22407213725347616457090869 2100676286751339042852269)
                  ·
                    refine ⟨787753607531752141069601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2100676286751339042852269 787753607531752141069601)
                    ·
                      rfl

theorem cell22_2301217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_2301217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301217 prefixEnd_2301217 := by exact prefixLift 2301217
  have htrace : WordTrace (prefixWord ++ tailWord_2301217) baseStart_2301217 baseEnd_2301217 := by
    simpa [prefixWord, tailWord_2301217, baseEnd_2301217] using wordTrace_append hprefix tailTrace_2301217
  have hstable : (prefixWord ++ tailWord_2301217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301217).length < 2 ^ (prefixWord ++ tailWord_2301217).sum := by decide
  have hdescent : baseEnd_2301217 < baseStart_2301217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301247 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 5]
def baseStart_2301247 : Nat := 118140960795 + 2301247 * 2 ^ 59
def prefixEnd_2301247 : Nat := 4983230072969 + 3 ^ 40 * 2301247 * 2
def baseEnd_2301247 : Nat := 262587959048280687606503

theorem tailTrace_2301247 : CollatzResearch.WordTrace tailWord_2301247 prefixEnd_2301247 262587959048280687606503 := by
  unfold tailWord_2301247
  simp only [CollatzResearch.WordTrace]
  refine ⟨83933373493982615542653995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55955582329321743695102663 83933373493982615542653995)
  ·
    refine ⟨125900060240973923313980993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83933373493982615542653995 125900060240973923313980993)
    ·
      refine ⟨94425045180730442485485745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125900060240973923313980993 94425045180730442485485745)
      ·
        refine ⟨70818783885547831864114309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94425045180730442485485745 70818783885547831864114309)
        ·
          refine ⟨13278521978540218474521433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70818783885547831864114309 13278521978540218474521433)
          ·
            refine ⟨9958891483905163855891075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13278521978540218474521433 9958891483905163855891075)
            ·
              refine ⟨14938337225857745783836613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9958891483905163855891075 14938337225857745783836613)
              ·
                refine ⟨2800938229848327334469365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14938337225857745783836613 2800938229848327334469365)
                ·
                  refine ⟨262587959048280687606503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2800938229848327334469365 262587959048280687606503)
                  ·
                    rfl

theorem cell22_2301247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 5].length) (baseStart_2301247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301247 prefixEnd_2301247 := by exact prefixLift 2301247
  have htrace : WordTrace (prefixWord ++ tailWord_2301247) baseStart_2301247 baseEnd_2301247 := by
    simpa [prefixWord, tailWord_2301247, baseEnd_2301247] using wordTrace_append hprefix tailTrace_2301247
  have hstable : (prefixWord ++ tailWord_2301247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301247).length < 2 ^ (prefixWord ++ tailWord_2301247).sum := by decide
  have hdescent : baseEnd_2301247 < baseStart_2301247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301262 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2301262 : Nat := 118140960795 + 2301262 * 2 ^ 59
def prefixEnd_2301262 : Nat := 4983230072969 + 3 ^ 40 * 2301262 * 2
def baseEnd_2301262 : Nat := 787769011951387023694463

theorem tailTrace_2301262 : CollatzResearch.WordTrace tailWord_2301262 prefixEnd_2301262 787769011951387023694463 := by
  unfold tailWord_2301262
  simp only [CollatzResearch.WordTrace]
  refine ⟨10491740073616034138056255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55955947059285515402966693 10491740073616034138056255)
  ·
    refine ⟨15737610110424051207084383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10491740073616034138056255 15737610110424051207084383)
    ·
      refine ⟨23606415165636076810626575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15737610110424051207084383 23606415165636076810626575)
      ·
        refine ⟨35409622748454115215939863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23606415165636076810626575 35409622748454115215939863)
        ·
          refine ⟨53114434122681172823909795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35409622748454115215939863 53114434122681172823909795)
          ·
            refine ⟨79671651184021759235864693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53114434122681172823909795 79671651184021759235864693)
            ·
              refine ⟨7469217298502039928362315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79671651184021759235864693 7469217298502039928362315)
              ·
                refine ⟨11203825947753059892543473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7469217298502039928362315 11203825947753059892543473)
                ·
                  refine ⟨8402869460814794919407605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11203825947753059892543473 8402869460814794919407605)
                  ·
                    refine ⟨787769011951387023694463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8402869460814794919407605 787769011951387023694463)
                    ·
                      rfl

theorem cell22_2301262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2301262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301262 prefixEnd_2301262 := by exact prefixLift 2301262
  have htrace : WordTrace (prefixWord ++ tailWord_2301262) baseStart_2301262 baseEnd_2301262 := by
    simpa [prefixWord, tailWord_2301262, baseEnd_2301262] using wordTrace_append hprefix tailTrace_2301262
  have hstable : (prefixWord ++ tailWord_2301262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301262).length < 2 ^ (prefixWord ++ tailWord_2301262).sum := by decide
  have hdescent : baseEnd_2301262 < baseStart_2301262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301270 : List Nat := [5, 2, 3, 1, 1, 1, 3, 6]
def baseStart_2301270 : Nat := 118140960795 + 2301270 * 2 ^ 59
def prefixEnd_2301270 : Nat := 4983230072969 + 3 ^ 40 * 2301270 * 2
def baseEnd_2301270 : Nat := 87530194501653074388271

theorem tailTrace_2301270 : CollatzResearch.WordTrace tailWord_2301270 prefixEnd_2301270 87530194501653074388271 := by
  unfold tailWord_2301270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5245888273306205654421329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55956141581932860313827509 5245888273306205654421329)
  ·
    refine ⟨3934416204979654240815997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5245888273306205654421329 3934416204979654240815997)
    ·
      refine ⟨1475406076867370340305999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3934416204979654240815997 1475406076867370340305999)
      ·
        refine ⟨2213109115301055510458999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475406076867370340305999 2213109115301055510458999)
        ·
          refine ⟨3319663672951583265688499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2213109115301055510458999 3319663672951583265688499)
          ·
            refine ⟨4979495509427374898532749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3319663672951583265688499 4979495509427374898532749)
            ·
              refine ⟨1867310816035265586949781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4979495509427374898532749 1867310816035265586949781)
              ·
                refine ⟨87530194501653074388271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1867310816035265586949781 87530194501653074388271)
                ·
                  rfl

theorem cell22_2301270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_2301270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301270 prefixEnd_2301270 := by exact prefixLift 2301270
  have htrace : WordTrace (prefixWord ++ tailWord_2301270) baseStart_2301270 baseEnd_2301270 := by
    simpa [prefixWord, tailWord_2301270, baseEnd_2301270] using wordTrace_append hprefix tailTrace_2301270
  have hstable : (prefixWord ++ tailWord_2301270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301270).length < 2 ^ (prefixWord ++ tailWord_2301270).sum := by decide
  have hdescent : baseEnd_2301270 < baseStart_2301270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301309 : List Nat := [1, 4, 1, 1, 2, 2, 1, 6, 4]
def baseStart_2301309 : Nat := 118140960795 + 2301309 * 2 ^ 59
def prefixEnd_2301309 : Nat := 4983230072969 + 3 ^ 40 * 2301309 * 2
def baseEnd_2301309 : Nat := 262595033670631522589773

theorem tailTrace_2301309 : CollatzResearch.WordTrace tailWord_2301309 prefixEnd_2301309 262595033670631522589773 := by
  unfold tailWord_2301309
  simp only [CollatzResearch.WordTrace]
  refine ⟨83935634819758000131410981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55957089879838666754273987 83935634819758000131410981)
  ·
    refine ⟨15737931528704625024639559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83935634819758000131410981 15737931528704625024639559)
    ·
      refine ⟨23606897293056937536959339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15737931528704625024639559 23606897293056937536959339)
      ·
        refine ⟨35410345939585406305439009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23606897293056937536959339 35410345939585406305439009)
        ·
          refine ⟨26557759454689054729079257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35410345939585406305439009 26557759454689054729079257)
          ·
            refine ⟨19918319591016791046809443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26557759454689054729079257 19918319591016791046809443)
            ·
              refine ⟨29877479386525186570214165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19918319591016791046809443 29877479386525186570214165)
              ·
                refine ⟨1400506846243368120478789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29877479386525186570214165 1400506846243368120478789)
                ·
                  refine ⟨262595033670631522589773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400506846243368120478789 262595033670631522589773)
                  ·
                    rfl

theorem cell22_2301309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_2301309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301309 prefixEnd_2301309 := by exact prefixLift 2301309
  have htrace : WordTrace (prefixWord ++ tailWord_2301309) baseStart_2301309 baseEnd_2301309 := by
    simpa [prefixWord, tailWord_2301309, baseEnd_2301309] using wordTrace_append hprefix tailTrace_2301309
  have hstable : (prefixWord ++ tailWord_2301309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301309).length < 2 ^ (prefixWord ++ tailWord_2301309).sum := by decide
  have hdescent : baseEnd_2301309 < baseStart_2301309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301337 : List Nat := [1, 2, 1, 2, 1, 6, 1, 8]
def baseStart_2301337 : Nat := 118140960795 + 2301337 * 2 ^ 59
def prefixEnd_2301337 : Nat := 4983230072969 + 3 ^ 40 * 2301337 * 2
def baseEnd_2301337 : Nat := 87532742887123536452137

theorem tailTrace_2301337 : CollatzResearch.WordTrace tailWord_2301337 prefixEnd_2301337 87532742887123536452137 := by
  unfold tailWord_2301337
  simp only [CollatzResearch.WordTrace]
  refine ⟨83936656063656560913430265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55957770709104373942286843 83936656063656560913430265)
  ·
    refine ⟨62952492047742420685072699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83936656063656560913430265 62952492047742420685072699)
    ·
      refine ⟨94428738071613631027609049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62952492047742420685072699 94428738071613631027609049)
      ·
        refine ⟨70821553553710223270706787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94428738071613631027609049 70821553553710223270706787)
        ·
          refine ⟨106232330330565334906060181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70821553553710223270706787 106232330330565334906060181)
          ·
            refine ⟨4979640484245250073721571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106232330330565334906060181 4979640484245250073721571)
            ·
              refine ⟨7469460726367875110582357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4979640484245250073721571 7469460726367875110582357)
              ·
                refine ⟨87532742887123536452137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7469460726367875110582357 87532742887123536452137)
                ·
                  rfl

theorem cell22_2301337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 8].length) (baseStart_2301337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301337 prefixEnd_2301337 := by exact prefixLift 2301337
  have htrace : WordTrace (prefixWord ++ tailWord_2301337) baseStart_2301337 baseEnd_2301337 := by
    simpa [prefixWord, tailWord_2301337, baseEnd_2301337] using wordTrace_append hprefix tailTrace_2301337
  have hstable : (prefixWord ++ tailWord_2301337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301337).length < 2 ^ (prefixWord ++ tailWord_2301337).sum := by decide
  have hdescent : baseEnd_2301337 < baseStart_2301337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301367 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 2, 6]
def baseStart_2301367 : Nat := 118140960795 + 2301367 * 2 ^ 59
def prefixEnd_2301367 : Nat := 4983230072969 + 3 ^ 40 * 2301367 * 2
def baseEnd_2301367 : Nat := 787804955597201749819141

theorem tailTrace_2301367 : CollatzResearch.WordTrace tailWord_2301367 prefixEnd_2301367 787804955597201749819141 := by
  unfold tailWord_2301367
  simp only [CollatzResearch.WordTrace]
  refine ⟨83937750253547876037022355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55958500169031917358014903 83937750253547876037022355)
  ·
    refine ⟨125906625380321814055533533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83937750253547876037022355 125906625380321814055533533)
    ·
      refine ⟨47214984517620680270825075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125906625380321814055533533 47214984517620680270825075)
      ·
        refine ⟨70822476776431020406237613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47214984517620680270825075 70822476776431020406237613)
        ·
          refine ⟨26558428791161632652339105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70822476776431020406237613 26558428791161632652339105)
          ·
            refine ⟨19918821593371224489254329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26558428791161632652339105 19918821593371224489254329)
            ·
              refine ⟨14939116195028418366940747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19918821593371224489254329 14939116195028418366940747)
              ·
                refine ⟨22408674292542627550411121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14939116195028418366940747 22408674292542627550411121)
                ·
                  refine ⟨16806505719406970662808341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22408674292542627550411121 16806505719406970662808341)
                  ·
                    refine ⟨787804955597201749819141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16806505719406970662808341 787804955597201749819141)
                    ·
                      rfl

theorem cell22_2301367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_2301367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301367 prefixEnd_2301367 := by exact prefixLift 2301367
  have htrace : WordTrace (prefixWord ++ tailWord_2301367) baseStart_2301367 baseEnd_2301367 := by
    simpa [prefixWord, tailWord_2301367, baseEnd_2301367] using wordTrace_append hprefix tailTrace_2301367
  have hstable : (prefixWord ++ tailWord_2301367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301367).length < 2 ^ (prefixWord ++ tailWord_2301367).sum := by decide
  have hdescent : baseEnd_2301367 < baseStart_2301367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301459 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 1, 5]
def baseStart_2301459 : Nat := 118140960795 + 2301459 * 2 ^ 59
def prefixEnd_2301459 : Nat := 4983230072969 + 3 ^ 40 * 2301459 * 2
def baseEnd_2301459 : Nat := 787836449077344176518859

theorem tailTrace_2301459 : CollatzResearch.WordTrace tailWord_2301459 prefixEnd_2301459 787836449077344176518859 := by
  unfold tailWord_2301459
  simp only [CollatzResearch.WordTrace]
  refine ⟨83941105769214575749371431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55960737179476383832914287 83941105769214575749371431)
  ·
    refine ⟨125911658653821863624057147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83941105769214575749371431 125911658653821863624057147)
    ·
      refine ⟨188867487980732795436085721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125911658653821863624057147 188867487980732795436085721)
      ·
        refine ⟨141650615985549596577064291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188867487980732795436085721 141650615985549596577064291)
        ·
          refine ⟨212475923978324394865596437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141650615985549596577064291 212475923978324394865596437)
          ·
            refine ⟨9959808936483956009324833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 212475923978324394865596437 9959808936483956009324833)
            ·
              refine ⟨7469856702362967006993625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9959808936483956009324833 7469856702362967006993625)
              ·
                refine ⟨5602392526772225255245219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7469856702362967006993625 5602392526772225255245219)
                ·
                  refine ⟨8403588790158337882867829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5602392526772225255245219 8403588790158337882867829)
                  ·
                    refine ⟨787836449077344176518859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8403588790158337882867829 787836449077344176518859)
                    ·
                      rfl

theorem cell22_2301459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 5].length) (baseStart_2301459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301459 prefixEnd_2301459 := by exact prefixLift 2301459
  have htrace : WordTrace (prefixWord ++ tailWord_2301459) baseStart_2301459 baseEnd_2301459 := by
    simpa [prefixWord, tailWord_2301459, baseEnd_2301459] using wordTrace_append hprefix tailTrace_2301459
  have hstable : (prefixWord ++ tailWord_2301459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301459).length < 2 ^ (prefixWord ++ tailWord_2301459).sum := by decide
  have hdescent : baseEnd_2301459 < baseStart_2301459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301461 : List Nat := [1, 3, 2, 1, 3, 2, 1, 5, 4]
def baseStart_2301461 : Nat := 118140960795 + 2301461 * 2 ^ 59
def prefixEnd_2301461 : Nat := 4983230072969 + 3 ^ 40 * 2301461 * 2
def baseEnd_2301461 : Nat := 262612377906072279322951

theorem tailTrace_2301461 : CollatzResearch.WordTrace tailWord_2301461 prefixEnd_2301461 262612377906072279322951 := by
  unfold tailWord_2301461
  simp only [CollatzResearch.WordTrace]
  refine ⟨83941178715207330090944237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55960785810138220060629491 83941178715207330090944237)
  ·
    refine ⟨31477942018202748784104089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83941178715207330090944237 31477942018202748784104089)
    ·
      refine ⟨23608456513652061588078067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31477942018202748784104089 23608456513652061588078067)
      ·
        refine ⟨35412684770478092382117101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23608456513652061588078067 35412684770478092382117101)
        ·
          refine ⟨13279756788929284643293913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35412684770478092382117101 13279756788929284643293913)
          ·
            refine ⟨9959817591696963482470435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13279756788929284643293913 9959817591696963482470435)
            ·
              refine ⟨14939726387545445223705653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9959817591696963482470435 14939726387545445223705653)
              ·
                refine ⟨1400599348832385489722405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14939726387545445223705653 1400599348832385489722405)
                ·
                  refine ⟨262612377906072279322951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400599348832385489722405 262612377906072279322951)
                  ·
                    rfl

theorem cell22_2301461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_2301461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301461 prefixEnd_2301461 := by exact prefixLift 2301461
  have htrace : WordTrace (prefixWord ++ tailWord_2301461) baseStart_2301461 baseEnd_2301461 := by
    simpa [prefixWord, tailWord_2301461, baseEnd_2301461] using wordTrace_append hprefix tailTrace_2301461
  have hstable : (prefixWord ++ tailWord_2301461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301461).length < 2 ^ (prefixWord ++ tailWord_2301461).sum := by decide
  have hdescent : baseEnd_2301461 < baseStart_2301461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301598 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2301598 : Nat := 118140960795 + 2301598 * 2 ^ 59
def prefixEnd_2301598 : Nat := 4983230072969 + 3 ^ 40 * 2301598 * 2
def baseEnd_2301598 : Nat := 787884031617994147293433

theorem tailTrace_2301598 : CollatzResearch.WordTrace tailWord_2301598 prefixEnd_2301598 787884031617994147293433 := by
  unfold tailWord_2301598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10493271939463875311085181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55964117010474001659120965 10493271939463875311085181)
  ·
    refine ⟨3934976977298953241656943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10493271939463875311085181 3934976977298953241656943)
    ·
      refine ⟨5902465465948429862485415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3934976977298953241656943 5902465465948429862485415)
      ·
        refine ⟨8853698198922644793728123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5902465465948429862485415 8853698198922644793728123)
        ·
          refine ⟨13280547298383967190592185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8853698198922644793728123 13280547298383967190592185)
          ·
            refine ⟨9960410473787975392944139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13280547298383967190592185 9960410473787975392944139)
            ·
              refine ⟨14940615710681963089416209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9960410473787975392944139 14940615710681963089416209)
              ·
                refine ⟨11205461783011472317062157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14940615710681963089416209 11205461783011472317062157)
                ·
                  refine ⟨4202048168629302118898309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11205461783011472317062157 4202048168629302118898309)
                  ·
                    refine ⟨787884031617994147293433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4202048168629302118898309 787884031617994147293433)
                    ·
                      rfl

theorem cell22_2301598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2301598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301598 prefixEnd_2301598 := by exact prefixLift 2301598
  have htrace : WordTrace (prefixWord ++ tailWord_2301598) baseStart_2301598 baseEnd_2301598 := by
    simpa [prefixWord, tailWord_2301598, baseEnd_2301598] using wordTrace_append hprefix tailTrace_2301598
  have hstable : (prefixWord ++ tailWord_2301598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301598).length < 2 ^ (prefixWord ++ tailWord_2301598).sum := by decide
  have hdescent : baseEnd_2301598 < baseStart_2301598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301624 : List Nat := [2, 1, 2, 1, 2, 1, 1, 12]
def baseStart_2301624 : Nat := 118140960795 + 2301624 * 2 ^ 59
def prefixEnd_2301624 : Nat := 4983230072969 + 3 ^ 40 * 2301624 * 2
def baseEnd_2301624 : Nat := 87543659105482082904817

theorem tailTrace_2301624 : CollatzResearch.WordTrace tailWord_2301624 prefixEnd_2301624 87543659105482082904817 := by
  unfold tailWord_2301624
  simp only [CollatzResearch.WordTrace]
  refine ⟨41973561906808404464563963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55964749209077872619418617 41973561906808404464563963)
  ·
    refine ⟨62960342860212606696845945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41973561906808404464563963 62960342860212606696845945)
    ·
      refine ⟨47220257145159455022634459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62960342860212606696845945 47220257145159455022634459)
      ·
        refine ⟨70830385717739182533951689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47220257145159455022634459 70830385717739182533951689)
        ·
          refine ⟨53122789288304386900463767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70830385717739182533951689 53122789288304386900463767)
          ·
            refine ⟨79684183932456580350695651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53122789288304386900463767 79684183932456580350695651)
            ·
              refine ⟨119526275898684870526043477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79684183932456580350695651 119526275898684870526043477)
              ·
                refine ⟨87543659105482082904817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 119526275898684870526043477 87543659105482082904817)
                ·
                  rfl

theorem cell22_2301624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 12].length) (baseStart_2301624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301624 prefixEnd_2301624 := by exact prefixLift 2301624
  have htrace : WordTrace (prefixWord ++ tailWord_2301624) baseStart_2301624 baseEnd_2301624 := by
    simpa [prefixWord, tailWord_2301624, baseEnd_2301624] using wordTrace_append hprefix tailTrace_2301624
  have hstable : (prefixWord ++ tailWord_2301624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301624).length < 2 ^ (prefixWord ++ tailWord_2301624).sum := by decide
  have hdescent : baseEnd_2301624 < baseStart_2301624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301626 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_2301626 : Nat := 118140960795 + 2301626 * 2 ^ 59
def prefixEnd_2301626 : Nat := 4983230072969 + 3 ^ 40 * 2301626 * 2
def baseEnd_2301626 : Nat := 787893616590211407593347

theorem tailTrace_2301626 : CollatzResearch.WordTrace tailWord_2301626 prefixEnd_2301626 787893616590211407593347 := by
  unfold tailWord_2301626
  simp only [CollatzResearch.WordTrace]
  refine ⟨20986799189902390817675183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55964797839739708847133821 20986799189902390817675183)
  ·
    refine ⟨31480198784853586226512775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20986799189902390817675183 31480198784853586226512775)
    ·
      refine ⟨47220298177280379339769163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31480198784853586226512775 47220298177280379339769163)
      ·
        refine ⟨70830447265920569009653745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47220298177280379339769163 70830447265920569009653745)
        ·
          refine ⟨53122835449440426757240309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70830447265920569009653745 53122835449440426757240309)
          ·
            refine ⟨4980265823385040008491279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53122835449440426757240309 4980265823385040008491279)
            ·
              refine ⟨7470398735077560012736919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4980265823385040008491279 7470398735077560012736919)
              ·
                refine ⟨11205598102616340019105379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7470398735077560012736919 11205598102616340019105379)
                ·
                  refine ⟨16808397153924510028658069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11205598102616340019105379 16808397153924510028658069)
                  ·
                    refine ⟨787893616590211407593347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16808397153924510028658069 787893616590211407593347)
                    ·
                      rfl

theorem cell22_2301626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_2301626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301626 prefixEnd_2301626 := by exact prefixLift 2301626
  have htrace : WordTrace (prefixWord ++ tailWord_2301626) baseStart_2301626 baseEnd_2301626 := by
    simpa [prefixWord, tailWord_2301626, baseEnd_2301626] using wordTrace_append hprefix tailTrace_2301626
  have hstable : (prefixWord ++ tailWord_2301626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301626).length < 2 ^ (prefixWord ++ tailWord_2301626).sum := by decide
  have hdescent : baseEnd_2301626 < baseStart_2301626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301630 : List Nat := [4, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_2301630 : Nat := 118140960795 + 2301630 * 2 ^ 59
def prefixEnd_2301630 : Nat := 4983230072969 + 3 ^ 40 * 2301630 * 2
def baseEnd_2301630 : Nat := 262631661957318910164445

theorem tailTrace_2301630 : CollatzResearch.WordTrace tailWord_2301630 prefixEnd_2301630 262631661957318910164445 := by
  unfold tailWord_2301630
  simp only [CollatzResearch.WordTrace]
  refine ⟨10493417831449383994230793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55964895101063381302564229 10493417831449383994230793)
  ·
    refine ⟨7870063373587037995673095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10493417831449383994230793 7870063373587037995673095)
    ·
      refine ⟨11805095060380556993509643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7870063373587037995673095 11805095060380556993509643)
      ·
        refine ⟨17707642590570835490264465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11805095060380556993509643 17707642590570835490264465)
        ·
          refine ⟨13280731942928126617698349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17707642590570835490264465 13280731942928126617698349)
          ·
            refine ⟨4980274478598047481636881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13280731942928126617698349 4980274478598047481636881)
            ·
              refine ⟨3735205858948535611227661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4980274478598047481636881 3735205858948535611227661)
              ·
                refine ⟨1400702197105700854210373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3735205858948535611227661 1400702197105700854210373)
                ·
                  refine ⟨262631661957318910164445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400702197105700854210373 262631661957318910164445)
                  ·
                    rfl

theorem cell22_2301630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_2301630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301630 prefixEnd_2301630 := by exact prefixLift 2301630
  have htrace : WordTrace (prefixWord ++ tailWord_2301630) baseStart_2301630 baseEnd_2301630 := by
    simpa [prefixWord, tailWord_2301630, baseEnd_2301630] using wordTrace_append hprefix tailTrace_2301630
  have hstable : (prefixWord ++ tailWord_2301630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301630).length < 2 ^ (prefixWord ++ tailWord_2301630).sum := by decide
  have hdescent : baseEnd_2301630 < baseStart_2301630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301709 : List Nat := [1, 7, 2, 1, 1, 1, 2, 7]
def baseStart_2301709 : Nat := 118140960795 + 2301709 * 2 ^ 59
def prefixEnd_2301709 : Nat := 4983230072969 + 3 ^ 40 * 2301709 * 2
def baseEnd_2301709 : Nat := 87546892131825206418677

theorem tailTrace_2301709 : CollatzResearch.WordTrace tailWord_2301709 prefixEnd_2301709 87546892131825206418677 := by
  unfold tailWord_2301709
  simp only [CollatzResearch.WordTrace]
  refine ⟨83950224018308868445972181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55966816012205912297314787 83950224018308868445972181)
  ·
    refine ⟨1967583375429114104202473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 83950224018308868445972181 1967583375429114104202473)
    ·
      refine ⟨1475687531571835578151855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1967583375429114104202473 1475687531571835578151855)
      ·
        refine ⟨2213531297357753367227783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475687531571835578151855 2213531297357753367227783)
        ·
          refine ⟨3320296946036630050841675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2213531297357753367227783 3320296946036630050841675)
          ·
            refine ⟨4980445419054945076262513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3320296946036630050841675 4980445419054945076262513)
            ·
              refine ⟨3735334064291208807196885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4980445419054945076262513 3735334064291208807196885)
              ·
                refine ⟨87546892131825206418677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3735334064291208807196885 87546892131825206418677)
                ·
                  rfl

theorem cell22_2301709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 7].length) (baseStart_2301709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301709 prefixEnd_2301709 := by exact prefixLift 2301709
  have htrace : WordTrace (prefixWord ++ tailWord_2301709) baseStart_2301709 baseEnd_2301709 := by
    simpa [prefixWord, tailWord_2301709, baseEnd_2301709] using wordTrace_append hprefix tailTrace_2301709
  have hstable : (prefixWord ++ tailWord_2301709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301709).length < 2 ^ (prefixWord ++ tailWord_2301709).sum := by decide
  have hdescent : baseEnd_2301709 < baseStart_2301709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301731 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 6]
def baseStart_2301731 : Nat := 118140960795 + 2301731 * 2 ^ 59
def prefixEnd_2301731 : Nat := 4983230072969 + 3 ^ 40 * 2301731 * 2
def baseEnd_2301731 : Nat := 262643186745342044572675

theorem tailTrace_2301731 : CollatzResearch.WordTrace tailWord_2301731 prefixEnd_2301731 262643186745342044572675 := by
  unfold tailWord_2301731
  simp only [CollatzResearch.WordTrace]
  refine ⟨83951026424229166203273047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55967350949486110802182031 83951026424229166203273047)
  ·
    refine ⟨125926539636343749304909571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83951026424229166203273047 125926539636343749304909571)
    ·
      refine ⟨188889809454515623957364357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125926539636343749304909571 188889809454515623957364357)
      ·
        refine ⟨35416839272721679492005817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188889809454515623957364357 35416839272721679492005817)
        ·
          refine ⟨26562629454541259619004363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35416839272721679492005817 26562629454541259619004363)
          ·
            refine ⟨39843944181811889428506545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26562629454541259619004363 39843944181811889428506545)
            ·
              refine ⟨29882958136358917071379909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39843944181811889428506545 29882958136358917071379909)
              ·
                refine ⟨5603054650567296950883733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29882958136358917071379909 5603054650567296950883733)
                ·
                  refine ⟨262643186745342044572675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5603054650567296950883733 262643186745342044572675)
                  ·
                    rfl

theorem cell22_2301731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 6].length) (baseStart_2301731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301731 prefixEnd_2301731 := by exact prefixLift 2301731
  have htrace : WordTrace (prefixWord ++ tailWord_2301731) baseStart_2301731 baseEnd_2301731 := by
    simpa [prefixWord, tailWord_2301731, baseEnd_2301731] using wordTrace_append hprefix tailTrace_2301731
  have hstable : (prefixWord ++ tailWord_2301731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301731).length < 2 ^ (prefixWord ++ tailWord_2301731).sum := by decide
  have hdescent : baseEnd_2301731 < baseStart_2301731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301733 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_2301733 : Nat := 118140960795 + 2301733 * 2 ^ 59
def prefixEnd_2301733 : Nat := 4983230072969 + 3 ^ 40 * 2301733 * 2
def baseEnd_2301733 : Nat := 787930244876898795168019

theorem tailTrace_2301733 : CollatzResearch.WordTrace tailWord_2301733 prefixEnd_2301733 787930244876898795168019 := by
  unfold tailWord_2301733
  simp only [CollatzResearch.WordTrace]
  refine ⟨83951099370221920544845853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55967399580147947029897235 83951099370221920544845853)
  ·
    refine ⟨31481662263833220204317195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83951099370221920544845853 31481662263833220204317195)
    ·
      refine ⟨47222493395749830306475793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31481662263833220204317195 47222493395749830306475793)
      ·
        refine ⟨35416870046812372729856845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47222493395749830306475793 35416870046812372729856845)
        ·
          refine ⟨13281326267554639773696317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35416870046812372729856845 13281326267554639773696317)
          ·
            refine ⟨4980497350332989915136119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13281326267554639773696317 4980497350332989915136119)
            ·
              refine ⟨7470746025499484872704179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4980497350332989915136119 7470746025499484872704179)
              ·
                refine ⟨11206119038249227309056269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7470746025499484872704179 11206119038249227309056269)
                ·
                  refine ⟨4202294639343460240896101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11206119038249227309056269 4202294639343460240896101)
                  ·
                    refine ⟨787930244876898795168019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4202294639343460240896101 787930244876898795168019)
                    ·
                      rfl

theorem cell22_2301733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_2301733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301733 prefixEnd_2301733 := by exact prefixLift 2301733
  have htrace : WordTrace (prefixWord ++ tailWord_2301733) baseStart_2301733 baseEnd_2301733 := by
    simpa [prefixWord, tailWord_2301733, baseEnd_2301733] using wordTrace_append hprefix tailTrace_2301733
  have hstable : (prefixWord ++ tailWord_2301733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301733).length < 2 ^ (prefixWord ++ tailWord_2301733).sum := by decide
  have hdescent : baseEnd_2301733 < baseStart_2301733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301780 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2301780 : Nat := 118140960795 + 2301780 * 2 ^ 59
def prefixEnd_2301780 : Nat := 4983230072969 + 3 ^ 40 * 2301780 * 2
def baseEnd_2301780 : Nat := 787946333937406339242875

theorem tailTrace_2301780 : CollatzResearch.WordTrace tailWord_2301780 prefixEnd_2301780 787946333937406339242875 := by
  unfold tailWord_2301780
  simp only [CollatzResearch.WordTrace]
  refine ⟨41976406800525823785903397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55968542400701098381204529 41976406800525823785903397)
  ·
    refine ⟨7870576275098591959856887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41976406800525823785903397 7870576275098591959856887)
    ·
      refine ⟨11805864412647887939785331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7870576275098591959856887 11805864412647887939785331)
      ·
        refine ⟨17708796618971831909677997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11805864412647887939785331 17708796618971831909677997)
        ·
          refine ⟨6640798732114436966129249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17708796618971831909677997 6640798732114436966129249)
          ·
            refine ⟨4980599049085827724596937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6640798732114436966129249 4980599049085827724596937)
            ·
              refine ⟨3735449286814370793447703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4980599049085827724596937 3735449286814370793447703)
              ·
                refine ⟨5603173930221556190171555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3735449286814370793447703 5603173930221556190171555)
                ·
                  refine ⟨8404760895332334285257333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5603173930221556190171555 8404760895332334285257333)
                  ·
                    refine ⟨787946333937406339242875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8404760895332334285257333 787946333937406339242875)
                    ·
                      rfl

theorem cell22_2301780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2301780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301780 prefixEnd_2301780 := by exact prefixLift 2301780
  have htrace : WordTrace (prefixWord ++ tailWord_2301780) baseStart_2301780 baseEnd_2301780 := by
    simpa [prefixWord, tailWord_2301780, baseEnd_2301780] using wordTrace_append hprefix tailTrace_2301780
  have hstable : (prefixWord ++ tailWord_2301780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301780).length < 2 ^ (prefixWord ++ tailWord_2301780).sum := by decide
  have hdescent : baseEnd_2301780 < baseStart_2301780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301793 : List Nat := [1, 2, 3, 1, 1, 1, 7, 6]
def baseStart_2301793 : Nat := 118140960795 + 2301793 * 2 ^ 59
def prefixEnd_2301793 : Nat := 4983230072969 + 3 ^ 40 * 2301793 * 2
def baseEnd_2301793 : Nat := 87550087122564293185315

theorem tailTrace_2301793 : CollatzResearch.WordTrace tailWord_2301793 prefixEnd_2301793 87550087122564293185315 := by
  unfold tailWord_2301793
  simp only [CollatzResearch.WordTrace]
  refine ⟨83953287750004550792030033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55968858500003033861353355 83953287750004550792030033)
  ·
    refine ⟨62964965812503413094022525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83953287750004550792030033 62964965812503413094022525)
    ·
      refine ⟨23611862179688779910258447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62964965812503413094022525 23611862179688779910258447)
      ·
        refine ⟨35417793269533169865387671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23611862179688779910258447 35417793269533169865387671)
        ·
          refine ⟨53126689904299754798081507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35417793269533169865387671 53126689904299754798081507)
          ·
            refine ⟨79690034856449632197122261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53126689904299754798081507 79690034856449632197122261)
            ·
              refine ⟨1867735191948038254620053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 79690034856449632197122261 1867735191948038254620053)
              ·
                refine ⟨87550087122564293185315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1867735191948038254620053 87550087122564293185315)
                ·
                  rfl

theorem cell22_2301793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 6].length) (baseStart_2301793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301793 prefixEnd_2301793 := by exact prefixLift 2301793
  have htrace : WordTrace (prefixWord ++ tailWord_2301793) baseStart_2301793 baseEnd_2301793 := by
    simpa [prefixWord, tailWord_2301793, baseEnd_2301793] using wordTrace_append hprefix tailTrace_2301793
  have hstable : (prefixWord ++ tailWord_2301793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301793).length < 2 ^ (prefixWord ++ tailWord_2301793).sum := by decide
  have hdescent : baseEnd_2301793 < baseStart_2301793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2301808 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 7, 3]
def baseStart_2301808 : Nat := 118140960795 + 2301808 * 2 ^ 59
def prefixEnd_2301808 : Nat := 4983230072969 + 3 ^ 40 * 2301808 * 2
def baseEnd_2301808 : Nat := 787955918909623599542789

theorem tailTrace_2301808 : CollatzResearch.WordTrace tailWord_2301808 prefixEnd_2301808 787955918909623599542789 := by
  unfold tailWord_2301808
  simp only [CollatzResearch.WordTrace]
  refine ⟨41976917422475104176913039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55969223229966805569217385 41976917422475104176913039)
  ·
    refine ⟨62965376133712656265369559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41976917422475104176913039 62965376133712656265369559)
    ·
      refine ⟨94448064200568984398054339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62965376133712656265369559 94448064200568984398054339)
      ·
        refine ⟨141672096300853476597081509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94448064200568984398054339 141672096300853476597081509)
        ·
          refine ⟨26563518056410026861952783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141672096300853476597081509 26563518056410026861952783)
          ·
            refine ⟨39845277084615040292929175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26563518056410026861952783 39845277084615040292929175)
            ·
              refine ⟨59767915626922560439393763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39845277084615040292929175 59767915626922560439393763)
              ·
                refine ⟨89651873440383840659090645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59767915626922560439393763 89651873440383840659090645)
                ·
                  refine ⟨2101215783758996265447437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 89651873440383840659090645 2101215783758996265447437)
                  ·
                    refine ⟨787955918909623599542789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2101215783758996265447437 787955918909623599542789)
                    ·
                      rfl

theorem cell22_2301808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7, 3].length) (baseStart_2301808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2301808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2301808 prefixEnd_2301808 := by exact prefixLift 2301808
  have htrace : WordTrace (prefixWord ++ tailWord_2301808) baseStart_2301808 baseEnd_2301808 := by
    simpa [prefixWord, tailWord_2301808, baseEnd_2301808] using wordTrace_append hprefix tailTrace_2301808
  have hstable : (prefixWord ++ tailWord_2301808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2301808).length < 2 ^ (prefixWord ++ tailWord_2301808).sum := by decide
  have hdescent : baseEnd_2301808 < baseStart_2301808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2301808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
