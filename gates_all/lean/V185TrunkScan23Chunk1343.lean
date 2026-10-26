import V185TrunkScan23Chunk1342

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7953832 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_7953832 : Nat := 118140960795 + 7953832 * 2 ^ 59
def prefixEnd_7953832 : Nat := 4983230072969 + 3 ^ 40 * 7953832 * 2
def baseEnd_7953832 : Nat := 4084138861112029829420999

theorem tailTrace_7953832 : CollatzResearch.WordTrace tailWord_7953832 prefixEnd_7953832 4084138861112029829420999 := by
  unfold tailWord_7953832
  simp only [CollatzResearch.WordTrace]
  refine ⟨145050042860316272601227875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193400057147088363468303833 145050042860316272601227875)
  ·
    refine ⟨217575064290474408901841813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145050042860316272601227875 217575064290474408901841813)
    ·
      refine ⟨10198831138615987917273835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217575064290474408901841813 10198831138615987917273835)
      ·
        refine ⟨15298246707923981875910753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10198831138615987917273835 15298246707923981875910753)
        ·
          refine ⟨11473685030942986406933065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15298246707923981875910753 11473685030942986406933065)
          ·
            refine ⟨8605263773207239805199799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11473685030942986406933065 8605263773207239805199799)
            ·
              refine ⟨12907895659810859707799699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8605263773207239805199799 12907895659810859707799699)
              ·
                refine ⟨19361843489716289561699549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12907895659810859707799699 19361843489716289561699549)
                ·
                  refine ⟨7260691308643608585637331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19361843489716289561699549 7260691308643608585637331)
                  ·
                    refine ⟨10891036962965412878455997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7260691308643608585637331 10891036962965412878455997)
                    ·
                      refine ⟨4084138861112029829420999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10891036962965412878455997 4084138861112029829420999)
                      ·
                        rfl

theorem cell23_7953832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_7953832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953832 prefixEnd_7953832 := by exact prefixLift 7953832
  have htrace : WordTrace (prefixWord ++ tailWord_7953832) baseStart_7953832 baseEnd_7953832 := by
    simpa [prefixWord, tailWord_7953832, baseEnd_7953832] using wordTrace_append hprefix tailTrace_7953832
  have hstable : (prefixWord ++ tailWord_7953832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953832).length < 2 ^ (prefixWord ++ tailWord_7953832).sum := by decide
  have hdescent : baseEnd_7953832 < baseStart_7953832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953841 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 3, 2, 3]
def baseStart_7953841 : Nat := 118140960795 + 7953841 * 2 ^ 59
def prefixEnd_7953841 : Nat := 4983230072969 + 3 ^ 40 * 7953841 * 2
def baseEnd_7953841 : Nat := 4084143482437920294208457

theorem tailTrace_7953841 : CollatzResearch.WordTrace tailWord_7953841 prefixEnd_7953841 4084143482437920294208457 := by
  unfold tailWord_7953841
  simp only [CollatzResearch.WordTrace]
  refine ⟨290100413977599939739533377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193400275985066626493022251 290100413977599939739533377)
  ·
    refine ⟨217575310483199954804650033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290100413977599939739533377 217575310483199954804650033)
    ·
      refine ⟨163181482862399966103487525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217575310483199954804650033 163181482862399966103487525)
      ·
        refine ⟨30596528036699993644403911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163181482862399966103487525 30596528036699993644403911)
        ·
          refine ⟨45894792055049990466605867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30596528036699993644403911 45894792055049990466605867)
          ·
            refine ⟨68842188082574985699908801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45894792055049990466605867 68842188082574985699908801)
            ·
              refine ⟨51631641061931239274931601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68842188082574985699908801 51631641061931239274931601)
              ·
                refine ⟨38723730796448429456198701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51631641061931239274931601 38723730796448429456198701)
                ·
                  refine ⟨14521399048668161046074513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38723730796448429456198701 14521399048668161046074513)
                  ·
                    refine ⟨10891049286501120784555885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14521399048668161046074513 10891049286501120784555885)
                    ·
                      refine ⟨4084143482437920294208457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10891049286501120784555885 4084143482437920294208457)
                      ·
                        rfl

theorem cell23_7953841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_7953841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953841 prefixEnd_7953841 := by exact prefixLift 7953841
  have htrace : WordTrace (prefixWord ++ tailWord_7953841) baseStart_7953841 baseEnd_7953841 := by
    simpa [prefixWord, tailWord_7953841, baseEnd_7953841] using wordTrace_append hprefix tailTrace_7953841
  have hstable : (prefixWord ++ tailWord_7953841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953841).length < 2 ^ (prefixWord ++ tailWord_7953841).sum := by decide
  have hdescent : baseEnd_7953841 < baseStart_7953841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953848 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 2, 4]
def baseStart_7953848 : Nat := 118140960795 + 7953848 * 2 ^ 59
def prefixEnd_7953848 : Nat := 4983230072969 + 3 ^ 40 * 7953848 * 2
def baseEnd_7953848 : Nat := 1361382358934167255606975

theorem tailTrace_7953848 : CollatzResearch.WordTrace tailWord_7953848 prefixEnd_7953848 1361382358934167255606975 := by
  unfold tailWord_7953848
  simp only [CollatzResearch.WordTrace]
  refine ⟨145050334644287289967519099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193400446192383053290025465 145050334644287289967519099)
  ·
    refine ⟨217575501966430934951278649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145050334644287289967519099 217575501966430934951278649)
    ·
      refine ⟨163181626474823201213458987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217575501966430934951278649 163181626474823201213458987)
      ·
        refine ⟨244772439712234801820188481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163181626474823201213458987 244772439712234801820188481)
        ·
          refine ⟨183579329784176101365141361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244772439712234801820188481 183579329784176101365141361)
          ·
            refine ⟨137684497338132076023856021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183579329784176101365141361 137684497338132076023856021)
            ·
              refine ⟨6453960812724941063618251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137684497338132076023856021 6453960812724941063618251)
              ·
                refine ⟨9680941219087411595427377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6453960812724941063618251 9680941219087411595427377)
                ·
                  refine ⟨7260705914315558696570533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9680941219087411595427377 7260705914315558696570533)
                  ·
                    refine ⟨1361382358934167255606975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7260705914315558696570533 1361382358934167255606975)
                    ·
                      rfl

theorem cell23_7953848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_7953848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953848 prefixEnd_7953848 := by exact prefixLift 7953848
  have htrace : WordTrace (prefixWord ++ tailWord_7953848) baseStart_7953848 baseEnd_7953848 := by
    simpa [prefixWord, tailWord_7953848, baseEnd_7953848] using wordTrace_append hprefix tailTrace_7953848
  have hstable : (prefixWord ++ tailWord_7953848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953848).length < 2 ^ (prefixWord ++ tailWord_7953848).sum := by decide
  have hdescent : baseEnd_7953848 < baseStart_7953848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953871 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 6, 1, 3]
def baseStart_7953871 : Nat := 118140960795 + 7953871 * 2 ^ 59
def prefixEnd_7953871 : Nat := 4983230072969 + 3 ^ 40 * 7953871 * 2
def baseEnd_7953871 : Nat := 4084158886857555176833319

theorem tailTrace_7953871 : CollatzResearch.WordTrace tailWord_7953871 prefixEnd_7953871 4084158886857555176833319 := by
  unfold tailWord_7953871
  simp only [CollatzResearch.WordTrace]
  refine ⟨290101508167491254863125467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193401005444994169908750311 290101508167491254863125467)
  ·
    refine ⟨435152262251236882294688201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290101508167491254863125467 435152262251236882294688201)
    ·
      refine ⟨326364196688427661721016151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435152262251236882294688201 326364196688427661721016151)
      ·
        refine ⟨489546295032641492581524227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326364196688427661721016151 489546295032641492581524227)
        ·
          refine ⟨734319442548962238872286341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489546295032641492581524227 734319442548962238872286341)
          ·
            refine ⟨137684895477930419788553689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 734319442548962238872286341 137684895477930419788553689)
            ·
              refine ⟨103263671608447814841415267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137684895477930419788553689 103263671608447814841415267)
              ·
                refine ⟨154895507412671722262122901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103263671608447814841415267 154895507412671722262122901)
                ·
                  refine ⟨7260726909968986981037011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154895507412671722262122901 7260726909968986981037011)
                  ·
                    refine ⟨10891090364953480471555517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7260726909968986981037011 10891090364953480471555517)
                    ·
                      refine ⟨4084158886857555176833319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10891090364953480471555517 4084158886857555176833319)
                      ·
                        rfl

theorem cell23_7953871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 1, 3].length) (baseStart_7953871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953871 prefixEnd_7953871 := by exact prefixLift 7953871
  have htrace : WordTrace (prefixWord ++ tailWord_7953871) baseStart_7953871 baseEnd_7953871 := by
    simpa [prefixWord, tailWord_7953871, baseEnd_7953871] using wordTrace_append hprefix tailTrace_7953871
  have hstable : (prefixWord ++ tailWord_7953871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953871).length < 2 ^ (prefixWord ++ tailWord_7953871).sum := by decide
  have hdescent : baseEnd_7953871 < baseStart_7953871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953889 : List Nat := [1, 2, 3, 1, 2, 5, 2, 2, 1, 2, 2]
def baseStart_7953889 : Nat := 118140960795 + 7953889 * 2 ^ 59
def prefixEnd_7953889 : Nat := 4983230072969 + 3 ^ 40 * 7953889 * 2
def baseEnd_7953889 : Nat := 4084168129509336106408237

theorem tailTrace_7953889 : CollatzResearch.WordTrace tailWord_7953889 prefixEnd_7953889 4084168129509336106408237 := by
  unfold tailWord_7953889
  simp only [CollatzResearch.WordTrace]
  refine ⟨290102164681426043937280721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193401443120950695958187147 290102164681426043937280721)
  ·
    refine ⟨217576623511069532952960541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290102164681426043937280721 217576623511069532952960541)
    ·
      refine ⟨81591233816651074857360203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217576623511069532952960541 81591233816651074857360203)
      ·
        refine ⟨122386850724976612286040305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81591233816651074857360203 122386850724976612286040305)
        ·
          refine ⟨91790138043732459214530229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122386850724976612286040305 91790138043732459214530229)
          ·
            refine ⟨8605325441599918051362209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91790138043732459214530229 8605325441599918051362209)
            ·
              refine ⟨6453994081199938538521657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8605325441599918051362209 6453994081199938538521657)
              ·
                refine ⟨4840495560899953903891243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6453994081199938538521657 4840495560899953903891243)
                ·
                  refine ⟨7260743341349930855836865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840495560899953903891243 7260743341349930855836865)
                  ·
                    refine ⟨5445557506012448141877649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7260743341349930855836865 5445557506012448141877649)
                    ·
                      refine ⟨4084168129509336106408237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445557506012448141877649 4084168129509336106408237)
                      ·
                        rfl

theorem cell23_7953889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_7953889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953889 prefixEnd_7953889 := by exact prefixLift 7953889
  have htrace : WordTrace (prefixWord ++ tailWord_7953889) baseStart_7953889 baseEnd_7953889 := by
    simpa [prefixWord, tailWord_7953889, baseEnd_7953889] using wordTrace_append hprefix tailTrace_7953889
  have hstable : (prefixWord ++ tailWord_7953889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953889).length < 2 ^ (prefixWord ++ tailWord_7953889).sum := by decide
  have hdescent : baseEnd_7953889 < baseStart_7953889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953904 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 1, 8]
def baseStart_7953904 : Nat := 118140960795 + 7953904 * 2 ^ 59
def prefixEnd_7953904 : Nat := 4983230072969 + 3 ^ 40 * 7953904 * 2
def baseEnd_7953904 : Nat := 1361391943906384515906889

theorem tailTrace_7953904 : CollatzResearch.WordTrace tailWord_7953904 prefixEnd_7953904 1361391943906384515906889 := by
  unfold tailWord_7953904
  simp only [CollatzResearch.WordTrace]
  refine ⟨145051355888185850749538383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193401807850914467666051177 145051355888185850749538383)
  ·
    refine ⟨217577033832278776124307575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145051355888185850749538383 217577033832278776124307575)
    ·
      refine ⟨326365550748418164186461363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217577033832278776124307575 326365550748418164186461363)
      ·
        refine ⟨489548326122627246279692045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326365550748418164186461363 489548326122627246279692045)
        ·
          refine ⟨183580622295985217354884517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489548326122627246279692045 183580622295985217354884517)
          ·
            refine ⟨34421366680497228254040847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183580622295985217354884517 34421366680497228254040847)
            ·
              refine ⟨51632050020745842381061271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34421366680497228254040847 51632050020745842381061271)
              ·
                refine ⟨77448075031118763571591907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51632050020745842381061271 77448075031118763571591907)
                ·
                  refine ⟨116172112546678145357387861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77448075031118763571591907 116172112546678145357387861)
                  ·
                    refine ⟨1361391943906384515906889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116172112546678145357387861 1361391943906384515906889)
                    ·
                      rfl

theorem cell23_7953904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_7953904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953904 prefixEnd_7953904 := by exact prefixLift 7953904
  have htrace : WordTrace (prefixWord ++ tailWord_7953904) baseStart_7953904 baseEnd_7953904 := by
    simpa [prefixWord, tailWord_7953904, baseEnd_7953904] using wordTrace_append hprefix tailTrace_7953904
  have hstable : (prefixWord ++ tailWord_7953904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953904).length < 2 ^ (prefixWord ++ tailWord_7953904).sum := by decide
  have hdescent : baseEnd_7953904 < baseStart_7953904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953928 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 1, 4, 2]
def baseStart_7953928 : Nat := 118140960795 + 7953928 * 2 ^ 59
def prefixEnd_7953928 : Nat := 4983230072969 + 3 ^ 40 * 7953928 * 2
def baseEnd_7953928 : Nat := 4084188155254861453820557

theorem tailTrace_7953928 : CollatzResearch.WordTrace tailWord_7953928 prefixEnd_7953928 4084188155254861453820557 := by
  unfold tailWord_7953928
  simp only [CollatzResearch.WordTrace]
  refine ⟨145051793564142376798975219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193402391418856502398633625 145051793564142376798975219)
  ·
    refine ⟨217577690346213565198462829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145051793564142376798975219 217577690346213565198462829)
    ·
      refine ⟨81591633879830086949423561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217577690346213565198462829 81591633879830086949423561)
      ·
        refine ⟨61193725409872565212067671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81591633879830086949423561 61193725409872565212067671)
        ·
          refine ⟨91790588114808847818101507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61193725409872565212067671 91790588114808847818101507)
          ·
            refine ⟨137685882172213271727152261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91790588114808847818101507 137685882172213271727152261)
            ·
              refine ⟨25816102907289988448841049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137685882172213271727152261 25816102907289988448841049)
              ·
                refine ⟨19362077180467491336630787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25816102907289988448841049 19362077180467491336630787)
                ·
                  refine ⟨29043115770701237004946181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19362077180467491336630787 29043115770701237004946181)
                  ·
                    refine ⟨5445584207006481938427409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29043115770701237004946181 5445584207006481938427409)
                    ·
                      refine ⟨4084188155254861453820557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445584207006481938427409 4084188155254861453820557)
                      ·
                        rfl

theorem cell23_7953928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_7953928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953928 prefixEnd_7953928 := by exact prefixLift 7953928
  have htrace : WordTrace (prefixWord ++ tailWord_7953928) baseStart_7953928 baseEnd_7953928 := by
    simpa [prefixWord, tailWord_7953928, baseEnd_7953928] using wordTrace_append hprefix tailTrace_7953928
  have hstable : (prefixWord ++ tailWord_7953928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953928).length < 2 ^ (prefixWord ++ tailWord_7953928).sum := by decide
  have hdescent : baseEnd_7953928 < baseStart_7953928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953941 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_7953941 : Nat := 118140960795 + 7953941 * 2 ^ 59
def prefixEnd_7953941 : Nat := 4983230072969 + 3 ^ 40 * 7953941 * 2
def baseEnd_7953941 : Nat := 4084194830503369902957997

theorem tailTrace_7953941 : CollatzResearch.WordTrace tailWord_7953941 prefixEnd_7953941 4084194830503369902957997 := by
  unfold tailWord_7953941
  simp only [CollatzResearch.WordTrace]
  refine ⟨290104061277237656818173677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193402707518158437878782451 290104061277237656818173677)
  ·
    refine ⟨108789022978964121306815129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290104061277237656818173677 108789022978964121306815129)
    ·
      refine ⟨81591767234223090980111347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108789022978964121306815129 81591767234223090980111347)
      ·
        refine ⟨122387650851334636470167021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81591767234223090980111347 122387650851334636470167021)
        ·
          refine ⟨45895369069250488676312633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122387650851334636470167021 45895369069250488676312633)
          ·
            refine ⟨34421526801937866507234475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45895369069250488676312633 34421526801937866507234475)
            ·
              refine ⟨51632290202906799760851713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34421526801937866507234475 51632290202906799760851713)
              ·
                refine ⟨38724217652180099820638785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51632290202906799760851713 38724217652180099820638785)
                ·
                  refine ⟨29043163239135074865479089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38724217652180099820638785 29043163239135074865479089)
                  ·
                    refine ⟨21782372429351306149109317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29043163239135074865479089 21782372429351306149109317)
                    ·
                      refine ⟨4084194830503369902957997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21782372429351306149109317 4084194830503369902957997)
                      ·
                        rfl

theorem cell23_7953941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_7953941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953941 prefixEnd_7953941 := by exact prefixLift 7953941
  have htrace : WordTrace (prefixWord ++ tailWord_7953941) baseStart_7953941 baseEnd_7953941 := by
    simpa [prefixWord, tailWord_7953941, baseEnd_7953941] using wordTrace_append hprefix tailTrace_7953941
  have hstable : (prefixWord ++ tailWord_7953941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953941).length < 2 ^ (prefixWord ++ tailWord_7953941).sum := by decide
  have hdescent : baseEnd_7953941 < baseStart_7953941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954013 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7954013 : Nat := 118140960795 + 7954013 * 2 ^ 59
def prefixEnd_7954013 : Nat := 4983230072969 + 3 ^ 40 * 7954013 * 2
def baseEnd_7954013 : Nat := 4084231801110493621257667

theorem tailTrace_7954013 : CollatzResearch.WordTrace tailWord_7954013 prefixEnd_7954013 4084231801110493621257667 := by
  unfold tailWord_7954013
  simp only [CollatzResearch.WordTrace]
  refine ⟨290106687332976813114794693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193404458221984542076529795 290106687332976813114794693)
  ·
    refine ⟨54395003874933152459024005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290106687332976813114794693 54395003874933152459024005)
    ·
      refine ⟨10199063226549966086067001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54395003874933152459024005 10199063226549966086067001)
      ·
        refine ⟨7649297419912474564550251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10199063226549966086067001 7649297419912474564550251)
        ·
          refine ⟨11473946129868711846825377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7649297419912474564550251 11473946129868711846825377)
          ·
            refine ⟨8605459597401533885119033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11473946129868711846825377 8605459597401533885119033)
            ·
              refine ⟨6454094698051150413839275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8605459597401533885119033 6454094698051150413839275)
              ·
                refine ⟨9681142047076725620758913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454094698051150413839275 9681142047076725620758913)
                ·
                  refine ⟨7260856535307544215569185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9681142047076725620758913 7260856535307544215569185)
                  ·
                    refine ⟨5445642401480658161676889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7260856535307544215569185 5445642401480658161676889)
                    ·
                      refine ⟨4084231801110493621257667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445642401480658161676889 4084231801110493621257667)
                      ·
                        rfl

theorem cell23_7954013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7954013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954013 prefixEnd_7954013 := by exact prefixLift 7954013
  have htrace : WordTrace (prefixWord ++ tailWord_7954013) baseStart_7954013 baseEnd_7954013 := by
    simpa [prefixWord, tailWord_7954013, baseEnd_7954013] using wordTrace_append hprefix tailTrace_7954013
  have hstable : (prefixWord ++ tailWord_7954013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954013).length < 2 ^ (prefixWord ++ tailWord_7954013).sum := by decide
  have hdescent : baseEnd_7954013 < baseStart_7954013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954058 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 6]
def baseStart_7954058 : Nat := 118140960795 + 7954058 * 2 ^ 59
def prefixEnd_7954058 : Nat := 4983230072969 + 3 ^ 40 * 7954058 * 2
def baseEnd_7954058 : Nat := 453806100859993993910551

theorem tailTrace_7954058 : CollatzResearch.WordTrace tailWord_7954058 prefixEnd_7954058 453806100859993993910551 := by
  unfold tailWord_7954058
  simp only [CollatzResearch.WordTrace]
  refine ⟨72527082154453446450045707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193405552411875857200121885 72527082154453446450045707)
  ·
    refine ⟨108790623231680169675068561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72527082154453446450045707 108790623231680169675068561)
    ·
      refine ⟨81592967423760127256301421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108790623231680169675068561 81592967423760127256301421)
      ·
        refine ⟨30597362783910047721113033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81592967423760127256301421 30597362783910047721113033)
        ·
          refine ⟨22948022087932535790834775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30597362783910047721113033 22948022087932535790834775)
          ·
            refine ⟨34422033131898803686252163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22948022087932535790834775 34422033131898803686252163)
            ·
              refine ⟨51633049697848205529378245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34422033131898803686252163 51633049697848205529378245)
              ·
                refine ⟨9681196818346538536758421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51633049697848205529378245 9681196818346538536758421)
                ·
                  refine ⟨453806100859993993910551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9681196818346538536758421 453806100859993993910551)
                  ·
                    rfl

theorem cell23_7954058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_7954058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954058 prefixEnd_7954058 := by exact prefixLift 7954058
  have htrace : WordTrace (prefixWord ++ tailWord_7954058) baseStart_7954058 baseEnd_7954058 := by
    simpa [prefixWord, tailWord_7954058, baseEnd_7954058] using wordTrace_append hprefix tailTrace_7954058
  have hstable : (prefixWord ++ tailWord_7954058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954058).length < 2 ^ (prefixWord ++ tailWord_7954058).sum := by decide
  have hdescent : baseEnd_7954058 < baseStart_7954058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954062 : List Nat := [4, 1, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_7954062 : Nat := 118140960795 + 7954062 * 2 ^ 59
def prefixEnd_7954062 : Nat := 4983230072969 + 3 ^ 40 * 7954062 * 2
def baseEnd_7954062 : Nat := 1361418987220854643181647

theorem tailTrace_7954062 : CollatzResearch.WordTrace tailWord_7954062 prefixEnd_7954062 1361418987220854643181647 := by
  unfold tailWord_7954062
  simp only [CollatzResearch.WordTrace]
  refine ⟨36263559313724911810416055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193405649673199529655552293 36263559313724911810416055)
  ·
    refine ⟨54395338970587367715624083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36263559313724911810416055 54395338970587367715624083)
    ·
      refine ⟨81593008455881051573436125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54395338970587367715624083 81593008455881051573436125)
      ·
        refine ⟨30597378170955394340038547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81593008455881051573436125 30597378170955394340038547)
        ·
          refine ⟨45896067256433091510057821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30597378170955394340038547 45896067256433091510057821)
          ·
            refine ⟨17211025221162409316271683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45896067256433091510057821 17211025221162409316271683)
            ·
              refine ⟨25816537831743613974407525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17211025221162409316271683 25816537831743613974407525)
              ·
                refine ⟨4840600843451927620201411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25816537831743613974407525 4840600843451927620201411)
                ·
                  refine ⟨7260901265177891430302117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840600843451927620201411 7260901265177891430302117)
                  ·
                    refine ⟨1361418987220854643181647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7260901265177891430302117 1361418987220854643181647)
                    ·
                      rfl

theorem cell23_7954062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_7954062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954062 prefixEnd_7954062 := by exact prefixLift 7954062
  have htrace : WordTrace (prefixWord ++ tailWord_7954062) baseStart_7954062 baseEnd_7954062 := by
    simpa [prefixWord, tailWord_7954062, baseEnd_7954062] using wordTrace_append hprefix tailTrace_7954062
  have hstable : (prefixWord ++ tailWord_7954062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954062).length < 2 ^ (prefixWord ++ tailWord_7954062).sum := by decide
  have hdescent : baseEnd_7954062 < baseStart_7954062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954105 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 1, 5]
def baseStart_7954105 : Nat := 118140960795 + 7954105 * 2 ^ 59
def prefixEnd_7954105 : Nat := 4983230072969 + 3 ^ 40 * 7954105 * 2
def baseEnd_7954105 : Nat := 1361426347110235753769081

theorem tailTrace_7954105 : CollatzResearch.WordTrace tailWord_7954105 prefixEnd_7954105 1361426347110235753769081 := by
  unfold tailWord_7954105
  simp only [CollatzResearch.WordTrace]
  refine ⟨290110042848643512827143769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193406695232429008551429179 290110042848643512827143769)
  ·
    refine ⟨217582532136482634620357827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290110042848643512827143769 217582532136482634620357827)
    ·
      refine ⟨326373798204723951930536741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217582532136482634620357827 326373798204723951930536741)
      ·
        refine ⟨61195087163385740986975639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326373798204723951930536741 61195087163385740986975639)
        ·
          refine ⟨91792630745078611480463459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61195087163385740986975639 91792630745078611480463459)
          ·
            refine ⟨137688946117617917220695189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91792630745078611480463459 137688946117617917220695189)
            ·
              refine ⟨6454169349263339869720087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137688946117617917220695189 6454169349263339869720087)
              ·
                refine ⟨9681254023895009804580131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454169349263339869720087 9681254023895009804580131)
                ·
                  refine ⟨14521881035842514706870197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9681254023895009804580131 14521881035842514706870197)
                  ·
                    refine ⟨1361426347110235753769081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14521881035842514706870197 1361426347110235753769081)
                    ·
                      rfl

theorem cell23_7954105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 5].length) (baseStart_7954105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954105 prefixEnd_7954105 := by exact prefixLift 7954105
  have htrace : WordTrace (prefixWord ++ tailWord_7954105) baseStart_7954105 baseEnd_7954105 := by
    simpa [prefixWord, tailWord_7954105, baseEnd_7954105] using wordTrace_append hprefix tailTrace_7954105
  have hstable : (prefixWord ++ tailWord_7954105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954105).length < 2 ^ (prefixWord ++ tailWord_7954105).sum := by decide
  have hdescent : baseEnd_7954105 < baseStart_7954105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954121 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_7954121 : Nat := 118140960795 + 7954121 * 2 ^ 59
def prefixEnd_7954121 : Nat := 4983230072969 + 3 ^ 40 * 7954121 * 2
def baseEnd_7954121 : Nat := 4084287257021179198707169

theorem tailTrace_7954121 : CollatzResearch.WordTrace tailWord_7954121 prefixEnd_7954121 4084287257021179198707169 := by
  unfold tailWord_7954121
  simp only [CollatzResearch.WordTrace]
  refine ⟨290110626416585547559726217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193407084277723698373150811 290110626416585547559726217)
  ·
    refine ⟨217582969812439160669794663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290110626416585547559726217 217582969812439160669794663)
    ·
      refine ⟨326374454718658741004691995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217582969812439160669794663 326374454718658741004691995)
      ·
        refine ⟨489561682077988111507037993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326374454718658741004691995 489561682077988111507037993)
        ·
          refine ⟨367171261558491083630278495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489561682077988111507037993 367171261558491083630278495)
          ·
            refine ⟨550756892337736625445417743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367171261558491083630278495 550756892337736625445417743)
            ·
              refine ⟨826135338506604938168126615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550756892337736625445417743 826135338506604938168126615)
              ·
                refine ⟨1239203007759907407252189923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826135338506604938168126615 1239203007759907407252189923)
                ·
                  refine ⟨1858804511639861110878284885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239203007759907407252189923 1858804511639861110878284885)
                  ·
                    refine ⟨21782865370779622393104901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1858804511639861110878284885 21782865370779622393104901)
                    ·
                      refine ⟨4084287257021179198707169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21782865370779622393104901 4084287257021179198707169)
                      ·
                        rfl

theorem cell23_7954121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_7954121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954121 prefixEnd_7954121 := by exact prefixLift 7954121
  have htrace : WordTrace (prefixWord ++ tailWord_7954121) baseStart_7954121 baseEnd_7954121 := by
    simpa [prefixWord, tailWord_7954121, baseEnd_7954121] using wordTrace_append hprefix tailTrace_7954121
  have hstable : (prefixWord ++ tailWord_7954121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954121).length < 2 ^ (prefixWord ++ tailWord_7954121).sum := by decide
  have hdescent : baseEnd_7954121 < baseStart_7954121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954128 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 3]
def baseStart_7954128 : Nat := 118140960795 + 7954128 * 2 ^ 59
def prefixEnd_7954128 : Nat := 4983230072969 + 3 ^ 40 * 7954128 * 2
def baseEnd_7954128 : Nat := 4084290851385760671319637

theorem tailTrace_7954128 : CollatzResearch.WordTrace tailWord_7954128 prefixEnd_7954128 4084290851385760671319637 := by
  unfold tailWord_7954128
  simp only [CollatzResearch.WordTrace]
  refine ⟨145055440863780093877615519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193407254485040125170154025 145055440863780093877615519)
  ·
    refine ⟨217583161295670140816423279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145055440863780093877615519 217583161295670140816423279)
    ·
      refine ⟨326374741943505211224634919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217583161295670140816423279 326374741943505211224634919)
      ·
        refine ⟨489562112915257816836952379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326374741943505211224634919 489562112915257816836952379)
        ·
          refine ⟨734343169372886725255428569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489562112915257816836952379 734343169372886725255428569)
          ·
            refine ⟨550757377029665043941571427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734343169372886725255428569 550757377029665043941571427)
            ·
              refine ⟨826136065544497565912357141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550757377029665043941571427 826136065544497565912357141)
              ·
                refine ⟨38725128072398323402141741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 826136065544497565912357141 38725128072398323402141741)
                ·
                  refine ⟨14521923027149371275803153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38725128072398323402141741 14521923027149371275803153)
                  ·
                    refine ⟨10891442270362028456852365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14521923027149371275803153 10891442270362028456852365)
                    ·
                      refine ⟨4084290851385760671319637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10891442270362028456852365 4084290851385760671319637)
                      ·
                        rfl

theorem cell23_7954128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 3].length) (baseStart_7954128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954128 prefixEnd_7954128 := by exact prefixLift 7954128
  have htrace : WordTrace (prefixWord ++ tailWord_7954128) baseStart_7954128 baseEnd_7954128 := by
    simpa [prefixWord, tailWord_7954128, baseEnd_7954128] using wordTrace_append hprefix tailTrace_7954128
  have hstable : (prefixWord ++ tailWord_7954128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954128).length < 2 ^ (prefixWord ++ tailWord_7954128).sum := by decide
  have hdescent : baseEnd_7954128 < baseStart_7954128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954138 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_7954138 : Nat := 118140960795 + 7954138 * 2 ^ 59
def prefixEnd_7954138 : Nat := 4983230072969 + 3 ^ 40 * 7954138 * 2
def baseEnd_7954138 : Nat := 4084295986192305632194591

theorem tailTrace_7954138 : CollatzResearch.WordTrace tailWord_7954138 prefixEnd_7954138 4084295986192305632194591 := by
  unfold tailWord_7954138
  simp only [CollatzResearch.WordTrace]
  refine ⟨72527811614380989865773767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193407497638349306308730045 72527811614380989865773767)
  ·
    refine ⟨108791717421571484798660651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72527811614380989865773767 108791717421571484798660651)
    ·
      refine ⟨163187576132357227197990977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108791717421571484798660651 163187576132357227197990977)
      ·
        refine ⟨122390682099267920398493233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163187576132357227197990977 122390682099267920398493233)
        ·
          refine ⟨91793011574450940298869925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122390682099267920398493233 91793011574450940298869925)
          ·
            refine ⟨17211189670209551306038111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91793011574450940298869925 17211189670209551306038111)
            ·
              refine ⟨25816784505314326959057167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17211189670209551306038111 25816784505314326959057167)
              ·
                refine ⟨38725176757971490438585751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25816784505314326959057167 38725176757971490438585751)
                ·
                  refine ⟨58087765136957235657878627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38725176757971490438585751 58087765136957235657878627)
                  ·
                    refine ⟨87131647705435853486817941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58087765136957235657878627 87131647705435853486817941)
                    ·
                      refine ⟨4084295986192305632194591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87131647705435853486817941 4084295986192305632194591)
                      ·
                        rfl

theorem cell23_7954138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_7954138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954138 prefixEnd_7954138 := by exact prefixLift 7954138
  have htrace : WordTrace (prefixWord ++ tailWord_7954138) baseStart_7954138 baseEnd_7954138 := by
    simpa [prefixWord, tailWord_7954138, baseEnd_7954138] using wordTrace_append hprefix tailTrace_7954138
  have hstable : (prefixWord ++ tailWord_7954138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954138).length < 2 ^ (prefixWord ++ tailWord_7954138).sum := by decide
  have hdescent : baseEnd_7954138 < baseStart_7954138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954175 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 4, 1, 3]
def baseStart_7954175 : Nat := 118140960795 + 7954175 * 2 ^ 59
def prefixEnd_7954175 : Nat := 4983230072969 + 3 ^ 40 * 7954175 * 2
def baseEnd_7954175 : Nat := 4084314984976521987431921

theorem tailTrace_7954175 : CollatzResearch.WordTrace tailWord_7954175 prefixEnd_7954175 4084314984976521987431921 := by
  unfold tailWord_7954175
  simp only [CollatzResearch.WordTrace]
  refine ⟨290112595958389914782191979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193408397305593276521461319 290112595958389914782191979)
  ·
    refine ⟨435168893937584872173287969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290112595958389914782191979 435168893937584872173287969)
    ·
      refine ⟨326376670453188654129965977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435168893937584872173287969 326376670453188654129965977)
      ·
        refine ⟨244782502839891490597474483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326376670453188654129965977 244782502839891490597474483)
        ·
          refine ⟨367173754259837235896211725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244782502839891490597474483 367173754259837235896211725)
          ·
            refine ⟨137690157847438963461079397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367173754259837235896211725 137690157847438963461079397)
            ·
              refine ⟨25816904596394805648952387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137690157847438963461079397 25816904596394805648952387)
              ·
                refine ⟨38725356894592208473428581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25816904596394805648952387 38725356894592208473428581)
                ·
                  refine ⟨7261004417736039088767859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38725356894592208473428581 7261004417736039088767859)
                  ·
                    refine ⟨10891506626604058633151789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7261004417736039088767859 10891506626604058633151789)
                    ·
                      refine ⟨4084314984976521987431921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10891506626604058633151789 4084314984976521987431921)
                      ·
                        rfl

theorem cell23_7954175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_7954175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954175 prefixEnd_7954175 := by exact prefixLift 7954175
  have htrace : WordTrace (prefixWord ++ tailWord_7954175) baseStart_7954175 baseEnd_7954175 := by
    simpa [prefixWord, tailWord_7954175, baseEnd_7954175] using wordTrace_append hprefix tailTrace_7954175
  have hstable : (prefixWord ++ tailWord_7954175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954175).length < 2 ^ (prefixWord ++ tailWord_7954175).sum := by decide
  have hdescent : baseEnd_7954175 < baseStart_7954175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954185 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 3, 3, 2]
def baseStart_7954185 : Nat := 118140960795 + 7954185 * 2 ^ 59
def prefixEnd_7954185 : Nat := 4983230072969 + 3 ^ 40 * 7954185 * 2
def baseEnd_7954185 : Nat := 4084320119783066948306875

theorem tailTrace_7954185 : CollatzResearch.WordTrace tailWord_7954185 prefixEnd_7954185 4084320119783066948306875 := by
  unfold tailWord_7954185
  simp only [CollatzResearch.WordTrace]
  refine ⟨290112960688353686490056009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193408640458902457660037339 290112960688353686490056009)
  ·
    refine ⟨217584720516265264867542007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290112960688353686490056009 217584720516265264867542007)
    ·
      refine ⟨326377080774397897301313011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217584720516265264867542007 326377080774397897301313011)
      ·
        refine ⟨489565621161596845951969517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326377080774397897301313011 489565621161596845951969517)
        ·
          refine ⟨183587107935598817231988569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489565621161596845951969517 183587107935598817231988569)
          ·
            refine ⟨137690330951699112923991427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183587107935598817231988569 137690330951699112923991427)
            ·
              refine ⟨206535496427548669385987141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137690330951699112923991427 206535496427548669385987141)
              ·
                refine ⟨38725405580165375509872589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206535496427548669385987141 38725405580165375509872589)
                ·
                  refine ⟨14522027092562015816202221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38725405580165375509872589 14522027092562015816202221)
                  ·
                    refine ⟨5445760159710755931075833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14522027092562015816202221 5445760159710755931075833)
                    ·
                      refine ⟨4084320119783066948306875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445760159710755931075833 4084320119783066948306875)
                      ·
                        rfl

theorem cell23_7954185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 3, 2].length) (baseStart_7954185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954185 prefixEnd_7954185 := by exact prefixLift 7954185
  have htrace : WordTrace (prefixWord ++ tailWord_7954185) baseStart_7954185 baseEnd_7954185 := by
    simpa [prefixWord, tailWord_7954185, baseEnd_7954185] using wordTrace_append hprefix tailTrace_7954185
  have hstable : (prefixWord ++ tailWord_7954185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954185).length < 2 ^ (prefixWord ++ tailWord_7954185).sum := by decide
  have hdescent : baseEnd_7954185 < baseStart_7954185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954196 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7954196 : Nat := 118140960795 + 7954196 * 2 ^ 59
def prefixEnd_7954196 : Nat := 4983230072969 + 3 ^ 40 * 7954196 * 2
def baseEnd_7954196 : Nat := 4084325768070266405269325

theorem tailTrace_7954196 : CollatzResearch.WordTrace tailWord_7954196 prefixEnd_7954196 4084325768070266405269325 := by
  unfold tailWord_7954196
  simp only [CollatzResearch.WordTrace]
  refine ⟨145056680945656917684353221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193408907927542556912470961 145056680945656917684353221)
  ·
    refine ⟨27198127677310672065816229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145056680945656917684353221 27198127677310672065816229)
    ·
      refine ⟨5099648939495751012340543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27198127677310672065816229 5099648939495751012340543)
      ·
        refine ⟨7649473409243626518510815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5099648939495751012340543 7649473409243626518510815)
        ·
          refine ⟨11474210113865439777766223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7649473409243626518510815 11474210113865439777766223)
          ·
            refine ⟨17211315170798159666649335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11474210113865439777766223 17211315170798159666649335)
            ·
              refine ⟨25816972756197239499974003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17211315170798159666649335 25816972756197239499974003)
              ·
                refine ⟨38725459134295859249961005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25816972756197239499974003 38725459134295859249961005)
                ·
                  refine ⟨14522047175360947218735377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38725459134295859249961005 14522047175360947218735377)
                  ·
                    refine ⟨10891535381520710414051533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14522047175360947218735377 10891535381520710414051533)
                    ·
                      refine ⟨4084325768070266405269325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10891535381520710414051533 4084325768070266405269325)
                      ·
                        rfl

theorem cell23_7954196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7954196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954196 prefixEnd_7954196 := by exact prefixLift 7954196
  have htrace : WordTrace (prefixWord ++ tailWord_7954196) baseStart_7954196 baseEnd_7954196 := by
    simpa [prefixWord, tailWord_7954196, baseEnd_7954196] using wordTrace_append hprefix tailTrace_7954196
  have hstable : (prefixWord ++ tailWord_7954196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954196).length < 2 ^ (prefixWord ++ tailWord_7954196).sum := by decide
  have hdescent : baseEnd_7954196 < baseStart_7954196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954202 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2]
def baseStart_7954202 : Nat := 118140960795 + 7954202 * 2 ^ 59
def prefixEnd_7954202 : Nat := 4983230072969 + 3 ^ 40 * 7954202 * 2
def baseEnd_7954202 : Nat := 4084328848954193381794297

theorem tailTrace_7954202 : CollatzResearch.WordTrace tailWord_7954202 prefixEnd_7954202 4084328848954193381794297 := by
  unfold tailWord_7954202
  simp only [CollatzResearch.WordTrace]
  refine ⟨72528395182323024598356215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193409053819528065595616573 72528395182323024598356215)
  ·
    refine ⟨108792592773484536897534323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72528395182323024598356215 108792592773484536897534323)
    ·
      refine ⟨163188889160226805346301485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108792592773484536897534323 163188889160226805346301485)
      ·
        refine ⟨61195833435085052004863057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163188889160226805346301485 61195833435085052004863057)
        ·
          refine ⟨45896875076313789003647293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61195833435085052004863057 45896875076313789003647293)
          ·
            refine ⟨17211328153617670876367735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45896875076313789003647293 17211328153617670876367735)
            ·
              refine ⟨25816992230426506314551603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17211328153617670876367735 25816992230426506314551603)
              ·
                refine ⟨38725488345639759471827405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25816992230426506314551603 38725488345639759471827405)
                ·
                  refine ⟨14522058129614909801935277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38725488345639759471827405 14522058129614909801935277)
                  ·
                    refine ⟨5445771798605591175725729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14522058129614909801935277 5445771798605591175725729)
                    ·
                      refine ⟨4084328848954193381794297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445771798605591175725729 4084328848954193381794297)
                      ·
                        rfl

theorem cell23_7954202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_7954202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954202 prefixEnd_7954202 := by exact prefixLift 7954202
  have htrace : WordTrace (prefixWord ++ tailWord_7954202) baseStart_7954202 baseEnd_7954202 := by
    simpa [prefixWord, tailWord_7954202, baseEnd_7954202] using wordTrace_append hprefix tailTrace_7954202
  have hstable : (prefixWord ++ tailWord_7954202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954202).length < 2 ^ (prefixWord ++ tailWord_7954202).sum := by decide
  have hdescent : baseEnd_7954202 < baseStart_7954202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954272 : List Nat := [2, 1, 1, 3, 3, 3, 2, 3, 5]
def baseStart_7954272 : Nat := 118140960795 + 7954272 * 2 ^ 59
def prefixEnd_7954272 : Nat := 4983230072969 + 3 ^ 40 * 7954272 * 2
def baseEnd_7954272 : Nat := 453818310288889789768775

theorem tailTrace_7954272 : CollatzResearch.WordTrace tailWord_7954272 prefixEnd_7954272 453818310288889789768775 := by
  unfold tailWord_7954272
  simp only [CollatzResearch.WordTrace]
  refine ⟨145058066919519250174236535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193410755892692333565648713 145058066919519250174236535)
  ·
    refine ⟨217587100379278875261354803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145058066919519250174236535 217587100379278875261354803)
    ·
      refine ⟨326380650568918312892032205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217587100379278875261354803 326380650568918312892032205)
      ·
        refine ⟨122392743963344367334512077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326380650568918312892032205 122392743963344367334512077)
        ·
          refine ⟨45897278986254137750442029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122392743963344367334512077 45897278986254137750442029)
          ·
            refine ⟨17211479619845301656415761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45897278986254137750442029 17211479619845301656415761)
            ·
              refine ⟨12908609714883976242311821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17211479619845301656415761 12908609714883976242311821)
              ·
                refine ⟨4840728643081491090866933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12908609714883976242311821 4840728643081491090866933)
                ·
                  refine ⟨453818310288889789768775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4840728643081491090866933 453818310288889789768775)
                  ·
                    rfl

theorem cell23_7954272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 5].length) (baseStart_7954272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954272 prefixEnd_7954272 := by exact prefixLift 7954272
  have htrace : WordTrace (prefixWord ++ tailWord_7954272) baseStart_7954272 baseEnd_7954272 := by
    simpa [prefixWord, tailWord_7954272, baseEnd_7954272] using wordTrace_append hprefix tailTrace_7954272
  have hstable : (prefixWord ++ tailWord_7954272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954272).length < 2 ^ (prefixWord ++ tailWord_7954272).sum := by decide
  have hdescent : baseEnd_7954272 < baseStart_7954272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954285 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_7954285 : Nat := 118140960795 + 7954285 * 2 ^ 59
def prefixEnd_7954285 : Nat := 4983230072969 + 3 ^ 40 * 7954285 * 2
def baseEnd_7954285 : Nat := 1361457155949505519018805

theorem tailTrace_7954285 : CollatzResearch.WordTrace tailWord_7954285 prefixEnd_7954285 1361457155949505519018805 := by
  unfold tailWord_7954285
  simp only [CollatzResearch.WordTrace]
  refine ⟨290116607987991403568696309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193411071991994269045797539 290116607987991403568696309)
  ·
    refine ⟨27198431998874194084565279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 290116607987991403568696309 27198431998874194084565279)
    ·
      refine ⟨40797647998311291126847919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27198431998874194084565279 40797647998311291126847919)
      ·
        refine ⟨61196471997466936690271879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40797647998311291126847919 61196471997466936690271879)
        ·
          refine ⟨91794707996200405035407819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61196471997466936690271879 91794707996200405035407819)
          ·
            refine ⟨137692061994300607553111729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91794707996200405035407819 137692061994300607553111729)
            ·
              refine ⟨103269046495725455664833797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137692061994300607553111729 103269046495725455664833797)
              ·
                refine ⟨19362946217948522937156337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103269046495725455664833797 19362946217948522937156337)
                ·
                  refine ⟨14522209663461392202867253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19362946217948522937156337 14522209663461392202867253)
                  ·
                    refine ⟨1361457155949505519018805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14522209663461392202867253 1361457155949505519018805)
                    ·
                      rfl

theorem cell23_7954285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_7954285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954285 prefixEnd_7954285 := by exact prefixLift 7954285
  have htrace : WordTrace (prefixWord ++ tailWord_7954285) baseStart_7954285 baseEnd_7954285 := by
    simpa [prefixWord, tailWord_7954285, baseEnd_7954285] using wordTrace_append hprefix tailTrace_7954285
  have hstable : (prefixWord ++ tailWord_7954285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954285).length < 2 ^ (prefixWord ++ tailWord_7954285).sum := by decide
  have hdescent : baseEnd_7954285 < baseStart_7954285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954302 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7954302 : Nat := 118140960795 + 7954302 * 2 ^ 59
def prefixEnd_7954302 : Nat := 4983230072969 + 3 ^ 40 * 7954302 * 2
def baseEnd_7954302 : Nat := 1361460065673214330181279

theorem tailTrace_7954302 : CollatzResearch.WordTrace tailWord_7954302 prefixEnd_7954302 1361460065673214330181279 := by
  unfold tailWord_7954302
  simp only [CollatzResearch.WordTrace]
  refine ⟨36264653503616226934008145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193411485352619876981376773 36264653503616226934008145)
  ·
    refine ⟨27198490127712170200506109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36264653503616226934008145 27198490127712170200506109)
    ·
      refine ⟨10199433797892063825189791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27198490127712170200506109 10199433797892063825189791)
      ·
        refine ⟨15299150696838095737784687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10199433797892063825189791 15299150696838095737784687)
        ·
          refine ⟨22948726045257143606677031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15299150696838095737784687 22948726045257143606677031)
          ·
            refine ⟨34423089067885715410015547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22948726045257143606677031 34423089067885715410015547)
            ·
              refine ⟨51634633601828573115023321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34423089067885715410015547 51634633601828573115023321)
              ·
                refine ⟨38725975201371429836267491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51634633601828573115023321 38725975201371429836267491)
                ·
                  refine ⟨58088962802057144754401237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38725975201371429836267491 58088962802057144754401237)
                  ·
                    refine ⟨1361460065673214330181279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58088962802057144754401237 1361460065673214330181279)
                    ·
                      rfl

theorem cell23_7954302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7954302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954302 prefixEnd_7954302 := by exact prefixLift 7954302
  have htrace : WordTrace (prefixWord ++ tailWord_7954302) baseStart_7954302 baseEnd_7954302 := by
    simpa [prefixWord, tailWord_7954302, baseEnd_7954302] using wordTrace_append hprefix tailTrace_7954302
  have hstable : (prefixWord ++ tailWord_7954302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954302).length < 2 ^ (prefixWord ++ tailWord_7954302).sum := by decide
  have hdescent : baseEnd_7954302 < baseStart_7954302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954322 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7954322 : Nat := 118140960795 + 7954322 * 2 ^ 59
def prefixEnd_7954322 : Nat := 4983230072969 + 3 ^ 40 * 7954322 * 2
def baseEnd_7954322 : Nat := 4084390466632732912293745

theorem tailTrace_7954322 : CollatzResearch.WordTrace tailWord_7954322 prefixEnd_7954322 4084390466632732912293745 := by
  unfold tailWord_7954322
  simp only [CollatzResearch.WordTrace]
  refine ⟨72529489372214339721948305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193411971659238239258528813 72529489372214339721948305)
  ·
    refine ⟨54397117029160754791461229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72529489372214339721948305 54397117029160754791461229)
    ·
      refine ⟨20398918885935283046797961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54397117029160754791461229 20398918885935283046797961)
      ·
        refine ⟨15299189164451462285098471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20398918885935283046797961 15299189164451462285098471)
        ·
          refine ⟨22948783746677193427647707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15299189164451462285098471 22948783746677193427647707)
          ·
            refine ⟨34423175620015790141471561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22948783746677193427647707 34423175620015790141471561)
            ·
              refine ⟨25817381715011842606103671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34423175620015790141471561 25817381715011842606103671)
              ·
                refine ⟨38726072572517763909155507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25817381715011842606103671 38726072572517763909155507)
                ·
                  refine ⟨58089108858776645863733261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38726072572517763909155507 58089108858776645863733261)
                  ·
                    refine ⟨21783415822041242198899973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58089108858776645863733261 21783415822041242198899973)
                    ·
                      refine ⟨4084390466632732912293745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21783415822041242198899973 4084390466632732912293745)
                      ·
                        rfl

theorem cell23_7954322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7954322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954322 prefixEnd_7954322 := by exact prefixLift 7954322
  have htrace : WordTrace (prefixWord ++ tailWord_7954322) baseStart_7954322 baseEnd_7954322 := by
    simpa [prefixWord, tailWord_7954322, baseEnd_7954322] using wordTrace_append hprefix tailTrace_7954322
  have hstable : (prefixWord ++ tailWord_7954322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954322).length < 2 ^ (prefixWord ++ tailWord_7954322).sum := by decide
  have hdescent : baseEnd_7954322 < baseStart_7954322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954325 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_7954325 : Nat := 118140960795 + 7954325 * 2 ^ 59
def prefixEnd_7954325 : Nat := 4983230072969 + 3 ^ 40 * 7954325 * 2
def baseEnd_7954325 : Nat := 4084392007074696400556231

theorem tailTrace_7954325 : CollatzResearch.WordTrace tailWord_7954325 prefixEnd_7954325 4084392007074696400556231 := by
  unfold tailWord_7954325
  simp only [CollatzResearch.WordTrace]
  refine ⟨290118066907846490400152429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193412044605230993600101619 290118066907846490400152429)
  ·
    refine ⟨108794275090442433900057161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290118066907846490400152429 108794275090442433900057161)
    ·
      refine ⟨81595706317831825425042871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108794275090442433900057161 81595706317831825425042871)
      ·
        refine ⟨122393559476747738137564307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81595706317831825425042871 122393559476747738137564307)
        ·
          refine ⟨183590339215121607206346461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122393559476747738137564307 183590339215121607206346461)
          ·
            refine ⟨68846377205670602702379923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183590339215121607206346461 68846377205670602702379923)
            ·
              refine ⟨103269565808505904053569885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68846377205670602702379923 103269565808505904053569885)
              ·
                refine ⟨38726087178189714020088707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103269565808505904053569885 38726087178189714020088707)
                ·
                  refine ⟨58089130767284571030133061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38726087178189714020088707 58089130767284571030133061)
                  ·
                    refine ⟨10891712018865857068149949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58089130767284571030133061 10891712018865857068149949)
                    ·
                      refine ⟨4084392007074696400556231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10891712018865857068149949 4084392007074696400556231)
                      ·
                        rfl

theorem cell23_7954325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_7954325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954325 prefixEnd_7954325 := by exact prefixLift 7954325
  have htrace : WordTrace (prefixWord ++ tailWord_7954325) baseStart_7954325 baseEnd_7954325 := by
    simpa [prefixWord, tailWord_7954325, baseEnd_7954325] using wordTrace_append hprefix tailTrace_7954325
  have hstable : (prefixWord ++ tailWord_7954325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954325).length < 2 ^ (prefixWord ++ tailWord_7954325).sum := by decide
  have hdescent : baseEnd_7954325 < baseStart_7954325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954399 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 2, 3, 2]
def baseStart_7954399 : Nat := 118140960795 + 7954399 * 2 ^ 59
def prefixEnd_7954399 : Nat := 4983230072969 + 3 ^ 40 * 7954399 * 2
def baseEnd_7954399 : Nat := 4084430004643129111030891

theorem tailTrace_7954399 : CollatzResearch.WordTrace tailWord_7954399 prefixEnd_7954399 4084430004643129111030891 := by
  unfold tailWord_7954399
  simp only [CollatzResearch.WordTrace]
  refine ⟨290120765909578401038346251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193413843939718934025564167 290120765909578401038346251)
  ·
    refine ⟨435181148864367601557519377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290120765909578401038346251 435181148864367601557519377)
    ·
      refine ⟨326385861648275701168139533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435181148864367601557519377 326385861648275701168139533)
      ·
        refine ⟨122394698118103387938052325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326385861648275701168139533 122394698118103387938052325)
        ·
          refine ⟨22949005897144385238384811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122394698118103387938052325 22949005897144385238384811)
          ·
            refine ⟨34423508845716577857577217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22949005897144385238384811 34423508845716577857577217)
            ·
              refine ⟨25817631634287433393182913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34423508845716577857577217 25817631634287433393182913)
              ·
                refine ⟨19363223725715575044887185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25817631634287433393182913 19363223725715575044887185)
                ·
                  refine ⟨14522417794286681283665389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19363223725715575044887185 14522417794286681283665389)
                  ·
                    refine ⟨5445906672857505481374521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14522417794286681283665389 5445906672857505481374521)
                    ·
                      refine ⟨4084430004643129111030891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445906672857505481374521 4084430004643129111030891)
                      ·
                        rfl

theorem cell23_7954399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_7954399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954399 prefixEnd_7954399 := by exact prefixLift 7954399
  have htrace : WordTrace (prefixWord ++ tailWord_7954399) baseStart_7954399 baseEnd_7954399 := by
    simpa [prefixWord, tailWord_7954399, baseEnd_7954399] using wordTrace_append hprefix tailTrace_7954399
  have hstable : (prefixWord ++ tailWord_7954399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954399).length < 2 ^ (prefixWord ++ tailWord_7954399).sum := by decide
  have hdescent : baseEnd_7954399 < baseStart_7954399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954415 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_7954415 : Nat := 118140960795 + 7954415 * 2 ^ 59
def prefixEnd_7954415 : Nat := 4983230072969 + 3 ^ 40 * 7954415 * 2
def baseEnd_7954415 : Nat := 4084438220333601048430817

theorem tailTrace_7954415 : CollatzResearch.WordTrace tailWord_7954415 prefixEnd_7954415 4084438220333601048430817 := by
  unfold tailWord_7954415
  simp only [CollatzResearch.WordTrace]
  refine ⟨290121349477520435770928699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193414232985013623847285799 290121349477520435770928699)
  ·
    refine ⟨435182024216280653656393049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290121349477520435770928699 435182024216280653656393049)
    ·
      refine ⟨326386518162210490242294787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435182024216280653656393049 326386518162210490242294787)
      ·
        refine ⟨489579777243315735363442181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326386518162210490242294787 489579777243315735363442181)
        ·
          refine ⟨91796208233121700380645409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489579777243315735363442181 91796208233121700380645409)
          ·
            refine ⟨68847156174841275285484057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91796208233121700380645409 68847156174841275285484057)
            ·
              refine ⟨51635367131130956464113043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68847156174841275285484057 51635367131130956464113043)
              ·
                refine ⟨77453050696696434696169565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51635367131130956464113043 77453050696696434696169565)
                ·
                  refine ⟨29044894011261163011063587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77453050696696434696169565 29044894011261163011063587)
                  ·
                    refine ⟨43567341016891744516595381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29044894011261163011063587 43567341016891744516595381)
                    ·
                      refine ⟨4084438220333601048430817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43567341016891744516595381 4084438220333601048430817)
                      ·
                        rfl

theorem cell23_7954415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_7954415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954415 prefixEnd_7954415 := by exact prefixLift 7954415
  have htrace : WordTrace (prefixWord ++ tailWord_7954415) baseStart_7954415 baseEnd_7954415 := by
    simpa [prefixWord, tailWord_7954415, baseEnd_7954415] using wordTrace_append hprefix tailTrace_7954415
  have hstable : (prefixWord ++ tailWord_7954415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954415).length < 2 ^ (prefixWord ++ tailWord_7954415).sum := by decide
  have hdescent : baseEnd_7954415 < baseStart_7954415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954429 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 5, 2, 2]
def baseStart_7954429 : Nat := 118140960795 + 7954429 * 2 ^ 59
def prefixEnd_7954429 : Nat := 4983230072969 + 3 ^ 40 * 7954429 * 2
def baseEnd_7954429 : Nat := 4084445409062763993655753

theorem tailTrace_7954429 : CollatzResearch.WordTrace tailWord_7954429 prefixEnd_7954429 4084445409062763993655753 := by
  unfold tailWord_7954429
  simp only [CollatzResearch.WordTrace]
  refine ⟨290121860099469716161938341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193414573399646477441292227 290121860099469716161938341)
  ·
    refine ⟨54397848768650571780363439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290121860099469716161938341 54397848768650571780363439)
    ·
      refine ⟨81596773152975857670545159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54397848768650571780363439 81596773152975857670545159)
      ·
        refine ⟨122395159729463786505817739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81596773152975857670545159 122395159729463786505817739)
        ·
          refine ⟨183592739594195679758726609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122395159729463786505817739 183592739594195679758726609)
          ·
            refine ⟨137694554695646759819044957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183592739594195679758726609 137694554695646759819044957)
            ·
              refine ⟨51635458010867534932141859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137694554695646759819044957 51635458010867534932141859)
              ·
                refine ⟨77453187016301302398212789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51635458010867534932141859 77453187016301302398212789)
                ·
                  refine ⟨7261236282778247099832449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77453187016301302398212789 7261236282778247099832449)
                  ·
                    refine ⟨5445927212083685324874337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7261236282778247099832449 5445927212083685324874337)
                    ·
                      refine ⟨4084445409062763993655753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445927212083685324874337 4084445409062763993655753)
                      ·
                        rfl

theorem cell23_7954429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_7954429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954429 prefixEnd_7954429 := by exact prefixLift 7954429
  have htrace : WordTrace (prefixWord ++ tailWord_7954429) baseStart_7954429 baseEnd_7954429 := by
    simpa [prefixWord, tailWord_7954429, baseEnd_7954429] using wordTrace_append hprefix tailTrace_7954429
  have hstable : (prefixWord ++ tailWord_7954429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954429).length < 2 ^ (prefixWord ++ tailWord_7954429).sum := by decide
  have hdescent : baseEnd_7954429 < baseStart_7954429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954495 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 1, 8]
def baseStart_7954495 : Nat := 118140960795 + 7954495 * 2 ^ 59
def prefixEnd_7954495 : Nat := 4983230072969 + 3 ^ 40 * 7954495 * 2
def baseEnd_7954495 : Nat := 1361493099595320245143483

theorem tailTrace_7954495 : CollatzResearch.WordTrace tailWord_7954495 prefixEnd_7954495 1361493099595320245143483 := by
  unfold tailWord_7954495
  simp only [CollatzResearch.WordTrace]
  refine ⟨290124267317230609433840939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193416178211487072955893959 290124267317230609433840939)
  ·
    refine ⟨435186400975845914150761409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290124267317230609433840939 435186400975845914150761409)
    ·
      refine ⟨326389800731884435613071057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435186400975845914150761409 326389800731884435613071057)
      ·
        refine ⟨244792350548913326709803293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326389800731884435613071057 244792350548913326709803293)
        ·
          refine ⟨91797131455842497516176235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244792350548913326709803293 91797131455842497516176235)
          ·
            refine ⟨137695697183763746274264353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91797131455842497516176235 137695697183763746274264353)
            ·
              refine ⟨103271772887822809705698265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137695697183763746274264353 103271772887822809705698265)
              ·
                refine ⟨77453829665867107279273699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103271772887822809705698265 77453829665867107279273699)
                ·
                  refine ⟨116180744498800660918910549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77453829665867107279273699 116180744498800660918910549)
                  ·
                    refine ⟨1361493099595320245143483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116180744498800660918910549 1361493099595320245143483)
                    ·
                      rfl

theorem cell23_7954495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_7954495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954495 prefixEnd_7954495 := by exact prefixLift 7954495
  have htrace : WordTrace (prefixWord ++ tailWord_7954495) baseStart_7954495 baseEnd_7954495 := by
    simpa [prefixWord, tailWord_7954495, baseEnd_7954495] using wordTrace_append hprefix tailTrace_7954495
  have hstable : (prefixWord ++ tailWord_7954495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954495).length < 2 ^ (prefixWord ++ tailWord_7954495).sum := by decide
  have hdescent : baseEnd_7954495 < baseStart_7954495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954522 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3]
def baseStart_7954522 : Nat := 118140960795 + 7954522 * 2 ^ 59
def prefixEnd_7954522 : Nat := 4983230072969 + 3 ^ 40 * 7954522 * 2
def baseEnd_7954522 : Nat := 4084493162763632129792825

theorem tailTrace_7954522 : CollatzResearch.WordTrace tailWord_7954522 prefixEnd_7954522 4084493162763632129792825 := by
  unfold tailWord_7954522
  simp only [CollatzResearch.WordTrace]
  refine ⟨72531313022033198261268455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193416834725421862030049213 72531313022033198261268455)
  ·
    refine ⟨108796969533049797391902683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72531313022033198261268455 108796969533049797391902683)
    ·
      refine ⟨163195454299574696087854025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108796969533049797391902683 163195454299574696087854025)
      ·
        refine ⟨122396590724681022065890519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163195454299574696087854025 122396590724681022065890519)
        ·
          refine ⟨183594886087021533098835779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122396590724681022065890519 183594886087021533098835779)
          ·
            refine ⟨275392329130532299648253669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183594886087021533098835779 275392329130532299648253669)
            ·
              refine ⟨51636061711974806184047563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275392329130532299648253669 51636061711974806184047563)
              ·
                refine ⟨77454092567962209276071345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51636061711974806184047563 77454092567962209276071345)
                ·
                  refine ⟨58090569425971656957053509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77454092567962209276071345 58090569425971656957053509)
                  ·
                    refine ⟨10891981767369685679447533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58090569425971656957053509 10891981767369685679447533)
                    ·
                      refine ⟨4084493162763632129792825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10891981767369685679447533 4084493162763632129792825)
                      ·
                        rfl

theorem cell23_7954522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_7954522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954522 prefixEnd_7954522 := by exact prefixLift 7954522
  have htrace : WordTrace (prefixWord ++ tailWord_7954522) baseStart_7954522 baseEnd_7954522 := by
    simpa [prefixWord, tailWord_7954522, baseEnd_7954522] using wordTrace_append hprefix tailTrace_7954522
  have hstable : (prefixWord ++ tailWord_7954522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954522).length < 2 ^ (prefixWord ++ tailWord_7954522).sum := by decide
  have hdescent : baseEnd_7954522 < baseStart_7954522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954532 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_7954532 : Nat := 118140960795 + 7954532 * 2 ^ 59
def prefixEnd_7954532 : Nat := 4983230072969 + 3 ^ 40 * 7954532 * 2
def baseEnd_7954532 : Nat := 4084498297570177090667779

theorem tailTrace_7954532 : CollatzResearch.WordTrace tailWord_7954532 prefixEnd_7954532 4084498297570177090667779 := by
  unfold tailWord_7954532
  simp only [CollatzResearch.WordTrace]
  refine ⟨145062808409048282376468925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193417077878731043168625233 145062808409048282376468925)
  ·
    refine ⟨54398553153393105891175847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145062808409048282376468925 54398553153393105891175847)
    ·
      refine ⟨81597829730089658836763771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54398553153393105891175847 81597829730089658836763771)
      ·
        refine ⟨122396744595134488255145657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81597829730089658836763771 122396744595134488255145657)
        ·
          refine ⟨91797558446350866191359243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122396744595134488255145657 91797558446350866191359243)
          ·
            refine ⟨137696337669526299287038865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91797558446350866191359243 137696337669526299287038865)
            ·
              refine ⟨103272253252144724465279149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137696337669526299287038865 103272253252144724465279149)
              ·
                refine ⟨38727094969554271674479681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103272253252144724465279149 38727094969554271674479681)
                ·
                  refine ⟨29045321227165703755859761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38727094969554271674479681 29045321227165703755859761)
                  ·
                    refine ⟨21783990920374277816894821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29045321227165703755859761 21783990920374277816894821)
                    ·
                      refine ⟨4084498297570177090667779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21783990920374277816894821 4084498297570177090667779)
                      ·
                        rfl

theorem cell23_7954532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_7954532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954532 prefixEnd_7954532 := by exact prefixLift 7954532
  have htrace : WordTrace (prefixWord ++ tailWord_7954532) baseStart_7954532 baseEnd_7954532 := by
    simpa [prefixWord, tailWord_7954532, baseEnd_7954532] using wordTrace_append hprefix tailTrace_7954532
  have hstable : (prefixWord ++ tailWord_7954532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954532).length < 2 ^ (prefixWord ++ tailWord_7954532).sum := by decide
  have hdescent : baseEnd_7954532 < baseStart_7954532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954542 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_7954542 : Nat := 118140960795 + 7954542 * 2 ^ 59
def prefixEnd_7954542 : Nat := 4983230072969 + 3 ^ 40 * 7954542 * 2
def baseEnd_7954542 : Nat := 453833714708524672393637

theorem tailTrace_7954542 : CollatzResearch.WordTrace tailWord_7954542 prefixEnd_7954542 453833714708524672393637 := by
  unfold tailWord_7954542
  simp only [CollatzResearch.WordTrace]
  refine ⟨36265747693507542057600235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193417321032040224307201253 36265747693507542057600235)
  ·
    refine ⟨54398621540261313086400353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36265747693507542057600235 54398621540261313086400353)
    ·
      refine ⟨40798966155195984814800265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54398621540261313086400353 40798966155195984814800265)
      ·
        refine ⟨30599224616396988611100199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40798966155195984814800265 30599224616396988611100199)
        ·
          refine ⟨45898836924595482916650299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30599224616396988611100199 45898836924595482916650299)
          ·
            refine ⟨68848255386893224374975449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45898836924595482916650299 68848255386893224374975449)
            ·
              refine ⟨51636191540169918281231587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68848255386893224374975449 51636191540169918281231587)
              ·
                refine ⟨77454287310254877421847381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51636191540169918281231587 77454287310254877421847381)
                ·
                  refine ⟨453833714708524672393637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77454287310254877421847381 453833714708524672393637)
                  ·
                    rfl

theorem cell23_7954542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_7954542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954542 prefixEnd_7954542 := by exact prefixLift 7954542
  have htrace : WordTrace (prefixWord ++ tailWord_7954542) baseStart_7954542 baseEnd_7954542 := by
    simpa [prefixWord, tailWord_7954542, baseEnd_7954542] using wordTrace_append hprefix tailTrace_7954542
  have hstable : (prefixWord ++ tailWord_7954542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954542).length < 2 ^ (prefixWord ++ tailWord_7954542).sum := by decide
  have hdescent : baseEnd_7954542 < baseStart_7954542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954552 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 4, 3, 3]
def baseStart_7954552 : Nat := 118140960795 + 7954552 * 2 ^ 59
def prefixEnd_7954552 : Nat := 4983230072969 + 3 ^ 40 * 7954552 * 2
def baseEnd_7954552 : Nat := 4084508567183267012417687

theorem tailTrace_7954552 : CollatzResearch.WordTrace tailWord_7954552 prefixEnd_7954552 4084508567183267012417687 := by
  unfold tailWord_7954552
  simp only [CollatzResearch.WordTrace]
  refine ⟨145063173139012054084332955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193417564185349405445777273 145063173139012054084332955)
  ·
    refine ⟨217594759708518081126499433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145063173139012054084332955 217594759708518081126499433)
    ·
      refine ⟨163196069781388560844874575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217594759708518081126499433 163196069781388560844874575)
      ·
        refine ⟨244794104672082841267311863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163196069781388560844874575 244794104672082841267311863)
        ·
          refine ⟨367191157008124261900967795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244794104672082841267311863 367191157008124261900967795)
          ·
            refine ⟨550786735512186392851451693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367191157008124261900967795 550786735512186392851451693)
            ·
              refine ⟨206545025817069897319294385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550786735512186392851451693 206545025817069897319294385)
              ·
                refine ⟨154908769362802422989470789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206545025817069897319294385 154908769362802422989470789)
                ·
                  refine ⟨29045394255525454310525773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154908769362802422989470789 29045394255525454310525773)
                  ·
                    refine ⟨10892022845822045366447165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29045394255525454310525773 10892022845822045366447165)
                    ·
                      refine ⟨4084508567183267012417687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10892022845822045366447165 4084508567183267012417687)
                      ·
                        rfl

theorem cell23_7954552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_7954552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954552 prefixEnd_7954552 := by exact prefixLift 7954552
  have htrace : WordTrace (prefixWord ++ tailWord_7954552) baseStart_7954552 baseEnd_7954552 := by
    simpa [prefixWord, tailWord_7954552, baseEnd_7954552] using wordTrace_append hprefix tailTrace_7954552
  have hstable : (prefixWord ++ tailWord_7954552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954552).length < 2 ^ (prefixWord ++ tailWord_7954552).sum := by decide
  have hdescent : baseEnd_7954552 < baseStart_7954552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954586 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3]
def baseStart_7954586 : Nat := 118140960795 + 7954586 * 2 ^ 59
def prefixEnd_7954586 : Nat := 4983230072969 + 3 ^ 40 * 7954586 * 2
def baseEnd_7954586 : Nat := 4084526025525519879392531

theorem tailTrace_7954586 : CollatzResearch.WordTrace tailWord_7954586 prefixEnd_7954586 4084526025525519879392531 := by
  unfold tailWord_7954586
  simp only [CollatzResearch.WordTrace]
  refine ⟨72531896589975232993850903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193418390906600621316935741 72531896589975232993850903)
  ·
    refine ⟨108797844884962849490776355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72531896589975232993850903 108797844884962849490776355)
    ·
      refine ⟨163196767327444274236164533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108797844884962849490776355 163196767327444274236164533)
      ·
        refine ⟨15299696936947900709640425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163196767327444274236164533 15299696936947900709640425)
        ·
          refine ⟨11474772702710925532230319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15299696936947900709640425 11474772702710925532230319)
          ·
            refine ⟨17212159054066388298345479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11474772702710925532230319 17212159054066388298345479)
            ·
              refine ⟨25818238581099582447518219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17212159054066388298345479 25818238581099582447518219)
              ·
                refine ⟨38727357871649373671277329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25818238581099582447518219 38727357871649373671277329)
                ·
                  refine ⟨29045518403737030253457997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38727357871649373671277329 29045518403737030253457997)
                  ·
                    refine ⟨10892069401401386345046749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29045518403737030253457997 10892069401401386345046749)
                    ·
                      refine ⟨4084526025525519879392531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10892069401401386345046749 4084526025525519879392531)
                      ·
                        rfl

theorem cell23_7954586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_7954586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954586 prefixEnd_7954586 := by exact prefixLift 7954586
  have htrace : WordTrace (prefixWord ++ tailWord_7954586) baseStart_7954586 baseEnd_7954586 := by
    simpa [prefixWord, tailWord_7954586, baseEnd_7954586] using wordTrace_append hprefix tailTrace_7954586
  have hstable : (prefixWord ++ tailWord_7954586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954586).length < 2 ^ (prefixWord ++ tailWord_7954586).sum := by decide
  have hdescent : baseEnd_7954586 < baseStart_7954586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954629 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 3]
def baseStart_7954629 : Nat := 118140960795 + 7954629 * 2 ^ 59
def prefixEnd_7954629 : Nat := 4983230072969 + 3 ^ 40 * 7954629 * 2
def baseEnd_7954629 : Nat := 4084548105193663211154833

theorem tailTrace_7954629 : CollatzResearch.WordTrace tailWord_7954629 prefixEnd_7954629 4084548105193663211154833 := by
  unfold tailWord_7954629
  simp only [CollatzResearch.WordTrace]
  refine ⟨290129154698745150319218941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193419436465830100212812627 290129154698745150319218941)
  ·
    refine ⟨108798433012029431369707103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290129154698745150319218941 108798433012029431369707103)
    ·
      refine ⟨163197649518044147054560655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108798433012029431369707103 163197649518044147054560655)
      ·
        refine ⟨244796474277066220581840983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163197649518044147054560655 244796474277066220581840983)
        ·
          refine ⟨367194711415599330872761475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244796474277066220581840983 367194711415599330872761475)
          ·
            refine ⟨550792067123398996309142213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367194711415599330872761475 550792067123398996309142213)
            ·
              refine ⟨103273512585637311807964165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 550792067123398996309142213 103273512585637311807964165)
              ·
                refine ⟨19363783609806995963993281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103273512585637311807964165 19363783609806995963993281)
                ·
                  refine ⟨14522837707355246972994961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19363783609806995963993281 14522837707355246972994961)
                  ·
                    refine ⟨10892128280516435229746221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14522837707355246972994961 10892128280516435229746221)
                    ·
                      refine ⟨4084548105193663211154833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10892128280516435229746221 4084548105193663211154833)
                      ·
                        rfl

theorem cell23_7954629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_7954629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954629 prefixEnd_7954629 := by exact prefixLift 7954629
  have htrace : WordTrace (prefixWord ++ tailWord_7954629) baseStart_7954629 baseEnd_7954629 := by
    simpa [prefixWord, tailWord_7954629, baseEnd_7954629] using wordTrace_append hprefix tailTrace_7954629
  have hstable : (prefixWord ++ tailWord_7954629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954629).length < 2 ^ (prefixWord ++ tailWord_7954629).sum := by decide
  have hdescent : baseEnd_7954629 < baseStart_7954629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954699 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 4]
def baseStart_7954699 : Nat := 118140960795 + 7954699 * 2 ^ 59
def prefixEnd_7954699 : Nat := 4983230072969 + 3 ^ 40 * 7954699 * 2
def baseEnd_7954699 : Nat := 4084584048839477937279511

theorem tailTrace_7954699 : CollatzResearch.WordTrace tailWord_7954699 prefixEnd_7954699 4084584048839477937279511 := by
  unfold tailWord_7954699
  simp only [CollatzResearch.WordTrace]
  refine ⟨290131707808491552274267151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193421138538994368182844767 290131707808491552274267151)
  ·
    refine ⟨435197561712737328411400727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290131707808491552274267151 435197561712737328411400727)
    ·
      refine ⟨652796342569105992617101091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435197561712737328411400727 652796342569105992617101091)
      ·
        refine ⟨979194513853658988925651637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652796342569105992617101091 979194513853658988925651637)
        ·
          refine ⟨91799485673780530211779841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 979194513853658988925651637 91799485673780530211779841)
          ·
            refine ⟨68849614255335397658834881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91799485673780530211779841 68849614255335397658834881)
            ·
              refine ⟨51637210691501548244126161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68849614255335397658834881 51637210691501548244126161)
              ·
                refine ⟨38727908018626161183094621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51637210691501548244126161 38727908018626161183094621)
                ·
                  refine ⟨14522965506984810443660483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38727908018626161183094621 14522965506984810443660483)
                  ·
                    refine ⟨21784448260477215665490725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14522965506984810443660483 21784448260477215665490725)
                    ·
                      refine ⟨4084584048839477937279511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21784448260477215665490725 4084584048839477937279511)
                      ·
                        rfl

theorem cell23_7954699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 4].length) (baseStart_7954699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954699 prefixEnd_7954699 := by exact prefixLift 7954699
  have htrace : WordTrace (prefixWord ++ tailWord_7954699) baseStart_7954699 baseEnd_7954699 := by
    simpa [prefixWord, tailWord_7954699, baseEnd_7954699] using wordTrace_append hprefix tailTrace_7954699
  have hstable : (prefixWord ++ tailWord_7954699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954699).length < 2 ^ (prefixWord ++ tailWord_7954699).sum := by decide
  have hdescent : baseEnd_7954699 < baseStart_7954699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954730 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 1, 5]
def baseStart_7954730 : Nat := 118140960795 + 7954730 * 2 ^ 59
def prefixEnd_7954730 : Nat := 4983230072969 + 3 ^ 40 * 7954730 * 2
def baseEnd_7954730 : Nat := 1361533322246589105330623

theorem tailTrace_7954730 : CollatzResearch.WordTrace tailWord_7954730 prefixEnd_7954730 1361533322246589105330623 := by
  unfold tailWord_7954730
  simp only [CollatzResearch.WordTrace]
  refine ⟨72533209617844811142161411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193421892314252829712430429 72533209617844811142161411)
  ·
    refine ⟨108799814426767216713242117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72533209617844811142161411 108799814426767216713242117)
    ·
      refine ⟨20399965205018853133732897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108799814426767216713242117 20399965205018853133732897)
      ·
        refine ⟨15299973903764139850299673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20399965205018853133732897 15299973903764139850299673)
        ·
          refine ⟨11474980427823104887724755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15299973903764139850299673 11474980427823104887724755)
          ·
            refine ⟨17212470641734657331587133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11474980427823104887724755 17212470641734657331587133)
            ·
              refine ⟨6454676490650496499345175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17212470641734657331587133 6454676490650496499345175)
              ·
                refine ⟨9682014735975744749017763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454676490650496499345175 9682014735975744749017763)
                ·
                  refine ⟨14523022103963617123526645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9682014735975744749017763 14523022103963617123526645)
                  ·
                    refine ⟨1361533322246589105330623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14523022103963617123526645 1361533322246589105330623)
                    ·
                      rfl

theorem cell23_7954730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_7954730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954730 prefixEnd_7954730 := by exact prefixLift 7954730
  have htrace : WordTrace (prefixWord ++ tailWord_7954730) baseStart_7954730 baseEnd_7954730 := by
    simpa [prefixWord, tailWord_7954730, baseEnd_7954730] using wordTrace_append hprefix tailTrace_7954730
  have hstable : (prefixWord ++ tailWord_7954730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954730).length < 2 ^ (prefixWord ++ tailWord_7954730).sum := by decide
  have hdescent : baseEnd_7954730 < baseStart_7954730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954793 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 1, 3, 2]
def baseStart_7954793 : Nat := 118140960795 + 7954793 * 2 ^ 59
def prefixEnd_7954793 : Nat := 4983230072969 + 3 ^ 40 * 7954793 * 2
def baseEnd_7954793 : Nat := 4084632316021000569504079

theorem tailTrace_7954793 : CollatzResearch.WordTrace tailWord_7954793 prefixEnd_7954793 4084632316021000569504079 := by
  unfold tailWord_7954793
  simp only [CollatzResearch.WordTrace]
  refine ⟨290135136270151006328189033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193423424180100670885459355 290135136270151006328189033)
  ·
    refine ⟨217601352202613254746141775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290135136270151006328189033 217601352202613254746141775)
    ·
      refine ⟨326402028303919882119212663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217601352202613254746141775 326402028303919882119212663)
      ·
        refine ⟨489603042455879823178818995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326402028303919882119212663 489603042455879823178818995)
        ·
          refine ⟨734404563683819734768228493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489603042455879823178818995 734404563683819734768228493)
          ·
            refine ⟨275401711381432400538085685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 734404563683819734768228493 275401711381432400538085685)
            ·
              refine ⟨25818910442009287550445533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275401711381432400538085685 25818910442009287550445533)
              ·
                refine ⟨9682091415753482831417075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25818910442009287550445533 9682091415753482831417075)
                ·
                  refine ⟨14523137123630224247125613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9682091415753482831417075 14523137123630224247125613)
                  ·
                    refine ⟨5446176421361334092672105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14523137123630224247125613 5446176421361334092672105)
                    ·
                      refine ⟨4084632316021000569504079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446176421361334092672105 4084632316021000569504079)
                      ·
                        rfl

theorem cell23_7954793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 3, 2].length) (baseStart_7954793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954793 prefixEnd_7954793 := by exact prefixLift 7954793
  have htrace : WordTrace (prefixWord ++ tailWord_7954793) baseStart_7954793 baseEnd_7954793 := by
    simpa [prefixWord, tailWord_7954793, baseEnd_7954793] using wordTrace_append hprefix tailTrace_7954793
  have hstable : (prefixWord ++ tailWord_7954793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954793).length < 2 ^ (prefixWord ++ tailWord_7954793).sum := by decide
  have hdescent : baseEnd_7954793 < baseStart_7954793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954800 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 2, 1, 3]
def baseStart_7954800 : Nat := 118140960795 + 7954800 * 2 ^ 59
def prefixEnd_7954800 : Nat := 4983230072969 + 3 ^ 40 * 7954800 * 2
def baseEnd_7954800 : Nat := 4084635910385582042116547

theorem tailTrace_7954800 : CollatzResearch.WordTrace tailWord_7954800 prefixEnd_7954800 4084635910385582042116547 := by
  unfold tailWord_7954800
  simp only [CollatzResearch.WordTrace]
  refine ⟨145067695790562823261846927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193423594387417097682462569 145067695790562823261846927)
  ·
    refine ⟨217601543685844234892770391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145067695790562823261846927 217601543685844234892770391)
    ·
      refine ⟨326402315528766352339155587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217601543685844234892770391 326402315528766352339155587)
      ·
        refine ⟨489603473293149528508733381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326402315528766352339155587 489603473293149528508733381)
        ·
          refine ⟨91800651242465536595387509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489603473293149528508733381 91800651242465536595387509)
          ·
            refine ⟨8606311053981144055817579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91800651242465536595387509 8606311053981144055817579)
            ·
              refine ⟨12909466580971716083726369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8606311053981144055817579 12909466580971716083726369)
              ·
                refine ⟨9682099935728787062794777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12909466580971716083726369 9682099935728787062794777)
                ·
                  refine ⟨7261574951796590297096083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9682099935728787062794777 7261574951796590297096083)
                  ·
                    refine ⟨10892362427694885445644125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7261574951796590297096083 10892362427694885445644125)
                    ·
                      refine ⟨4084635910385582042116547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10892362427694885445644125 4084635910385582042116547)
                      ·
                        rfl

theorem cell23_7954800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2, 1, 3].length) (baseStart_7954800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954800 prefixEnd_7954800 := by exact prefixLift 7954800
  have htrace : WordTrace (prefixWord ++ tailWord_7954800) baseStart_7954800 baseEnd_7954800 := by
    simpa [prefixWord, tailWord_7954800, baseEnd_7954800] using wordTrace_append hprefix tailTrace_7954800
  have hstable : (prefixWord ++ tailWord_7954800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954800).length < 2 ^ (prefixWord ++ tailWord_7954800).sum := by decide
  have hdescent : baseEnd_7954800 < baseStart_7954800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954809 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_7954809 : Nat := 118140960795 + 7954809 * 2 ^ 59
def prefixEnd_7954809 : Nat := 4983230072969 + 3 ^ 40 * 7954809 * 2
def baseEnd_7954809 : Nat := 4084640531711472506904005

theorem tailTrace_7954809 : CollatzResearch.WordTrace tailWord_7954809 prefixEnd_7954809 4084640531711472506904005 := by
  unfold tailWord_7954809
  simp only [CollatzResearch.WordTrace]
  refine ⟨290135719838093041060771481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193423813225395360707180987 290135719838093041060771481)
  ·
    refine ⟨217601789878569780795578611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290135719838093041060771481 217601789878569780795578611)
    ·
      refine ⟨326402684817854671193367917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217601789878569780795578611 326402684817854671193367917)
      ·
        refine ⟨122401006806695501697512969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326402684817854671193367917 122401006806695501697512969)
        ·
          refine ⟨91800755105021626273134727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122401006806695501697512969 91800755105021626273134727)
          ·
            refine ⟨137701132657532439409702091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91800755105021626273134727 137701132657532439409702091)
            ·
              refine ⟨206551698986298659114553137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137701132657532439409702091 206551698986298659114553137)
              ·
                refine ⟨154913774239723994335914853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206551698986298659114553137 154913774239723994335914853)
                ·
                  refine ⟨29046332669948248937984035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154913774239723994335914853 29046332669948248937984035)
                  ·
                    refine ⟨43569499004922373406976053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29046332669948248937984035 43569499004922373406976053)
                    ·
                      refine ⟨4084640531711472506904005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43569499004922373406976053 4084640531711472506904005)
                      ·
                        rfl

theorem cell23_7954809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_7954809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954809 prefixEnd_7954809 := by exact prefixLift 7954809
  have htrace : WordTrace (prefixWord ++ tailWord_7954809) baseStart_7954809 baseEnd_7954809 := by
    simpa [prefixWord, tailWord_7954809, baseEnd_7954809] using wordTrace_append hprefix tailTrace_7954809
  have hstable : (prefixWord ++ tailWord_7954809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954809).length < 2 ^ (prefixWord ++ tailWord_7954809).sum := by decide
  have hdescent : baseEnd_7954809 < baseStart_7954809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954817 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_7954817 : Nat := 118140960795 + 7954817 * 2 ^ 59
def prefixEnd_7954817 : Nat := 4983230072969 + 3 ^ 40 * 7954817 * 2
def baseEnd_7954817 : Nat := 4084644639556708475603969

theorem tailTrace_7954817 : CollatzResearch.WordTrace tailWord_7954817 prefixEnd_7954817 4084644639556708475603969 := by
  unfold tailWord_7954817
  simp only [CollatzResearch.WordTrace]
  refine ⟨290136011622064058427062705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193424007748042705618041803 290136011622064058427062705)
  ·
    refine ⟨217602008716548043820297029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290136011622064058427062705 217602008716548043820297029)
    ·
      refine ⟨40800376634352758216305693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217602008716548043820297029 40800376634352758216305693)
      ·
        refine ⟨15300141237882284331114635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40800376634352758216305693 15300141237882284331114635)
        ·
          refine ⟨22950211856823426496671953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15300141237882284331114635 22950211856823426496671953)
          ·
            refine ⟨17212658892617569872503965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22950211856823426496671953 17212658892617569872503965)
            ·
              refine ⟨6454747084731588702188987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17212658892617569872503965 6454747084731588702188987)
              ·
                refine ⟨9682120627097383053283481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454747084731588702188987 9682120627097383053283481)
                ·
                  refine ⟨7261590470323037289962611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9682120627097383053283481 7261590470323037289962611)
                  ·
                    refine ⟨10892385705484555934943917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7261590470323037289962611 10892385705484555934943917)
                    ·
                      refine ⟨4084644639556708475603969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10892385705484555934943917 4084644639556708475603969)
                      ·
                        rfl

theorem cell23_7954817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_7954817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954817 prefixEnd_7954817 := by exact prefixLift 7954817
  have htrace : WordTrace (prefixWord ++ tailWord_7954817) baseStart_7954817 baseEnd_7954817 := by
    simpa [prefixWord, tailWord_7954817, baseEnd_7954817] using wordTrace_append hprefix tailTrace_7954817
  have hstable : (prefixWord ++ tailWord_7954817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954817).length < 2 ^ (prefixWord ++ tailWord_7954817).sum := by decide
  have hdescent : baseEnd_7954817 < baseStart_7954817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954840 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 4, 2, 2]
def baseStart_7954840 : Nat := 118140960795 + 7954840 * 2 ^ 59
def prefixEnd_7954840 : Nat := 4983230072969 + 3 ^ 40 * 7954840 * 2
def baseEnd_7954840 : Nat := 4084656449611761885616363

theorem tailTrace_7954840 : CollatzResearch.WordTrace tailWord_7954840 prefixEnd_7954840 4084656449611761885616363 := by
  unfold tailWord_7954840
  simp only [CollatzResearch.WordTrace]
  refine ⟨145068425250490366677574987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193424567000653822236766649 145068425250490366677574987)
  ·
    refine ⟨217602637875735550016362481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145068425250490366677574987 217602637875735550016362481)
    ·
      refine ⟨163201978406801662512271861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217602637875735550016362481 163201978406801662512271861)
      ·
        refine ⟨15300185475637655860525487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163201978406801662512271861 15300185475637655860525487)
        ·
          refine ⟨22950278213456483790788231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15300185475637655860525487 22950278213456483790788231)
          ·
            refine ⟨34425417320184725686182347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22950278213456483790788231 34425417320184725686182347)
            ·
              refine ⟨51638125980277088529273521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34425417320184725686182347 51638125980277088529273521)
              ·
                refine ⟨38728594485207816396955141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51638125980277088529273521 38728594485207816396955141)
                ·
                  refine ⟨7261611465976465574429089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38728594485207816396955141 7261611465976465574429089)
                  ·
                    refine ⟨5446208599482349180821817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7261611465976465574429089 5446208599482349180821817)
                    ·
                      refine ⟨4084656449611761885616363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446208599482349180821817 4084656449611761885616363)
                      ·
                        rfl

theorem cell23_7954840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_7954840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954840 prefixEnd_7954840 := by exact prefixLift 7954840
  have htrace : WordTrace (prefixWord ++ tailWord_7954840) baseStart_7954840 baseEnd_7954840 := by
    simpa [prefixWord, tailWord_7954840, baseEnd_7954840] using wordTrace_append hprefix tailTrace_7954840
  have hstable : (prefixWord ++ tailWord_7954840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954840).length < 2 ^ (prefixWord ++ tailWord_7954840).sum := by decide
  have hdescent : baseEnd_7954840 < baseStart_7954840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954868 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_7954868 : Nat := 118140960795 + 7954868 * 2 ^ 59
def prefixEnd_7954868 : Nat := 4983230072969 + 3 ^ 40 * 7954868 * 2
def baseEnd_7954868 : Nat := 4084670827070087776066235

theorem tailTrace_7954868 : CollatzResearch.WordTrace tailWord_7954868 prefixEnd_7954868 4084670827070087776066235 := by
  unfold tailWord_7954868
  simp only [CollatzResearch.WordTrace]
  refine ⟨145068935872439647068584629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193425247829919529424779505 145068935872439647068584629)
  ·
    refine ⟨13600212738041216912679809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145068935872439647068584629 13600212738041216912679809)
    ·
      refine ⟨10200159553530912684509857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13600212738041216912679809 10200159553530912684509857)
      ·
        refine ⟨7650119665148184513382393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10200159553530912684509857 7650119665148184513382393)
        ·
          refine ⟨5737589748861138385036795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7650119665148184513382393 5737589748861138385036795)
          ·
            refine ⟨8606384623291707577555193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737589748861138385036795 8606384623291707577555193)
            ·
              refine ⟨6454788467468780683166395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8606384623291707577555193 6454788467468780683166395)
              ·
                refine ⟨9682182701203171024749593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454788467468780683166395 9682182701203171024749593)
                ·
                  refine ⟨7261637025902378268562195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9682182701203171024749593 7261637025902378268562195)
                  ·
                    refine ⟨10892455538853567402843293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7261637025902378268562195 10892455538853567402843293)
                    ·
                      refine ⟨4084670827070087776066235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10892455538853567402843293 4084670827070087776066235)
                      ·
                        rfl

theorem cell23_7954868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_7954868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954868 prefixEnd_7954868 := by exact prefixLift 7954868
  have htrace : WordTrace (prefixWord ++ tailWord_7954868) baseStart_7954868 baseEnd_7954868 := by
    simpa [prefixWord, tailWord_7954868, baseEnd_7954868] using wordTrace_append hprefix tailTrace_7954868
  have hstable : (prefixWord ++ tailWord_7954868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954868).length < 2 ^ (prefixWord ++ tailWord_7954868).sum := by decide
  have hdescent : baseEnd_7954868 < baseStart_7954868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954889 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 2, 8]
def baseStart_7954889 : Nat := 118140960795 + 7954889 * 2 ^ 59
def prefixEnd_7954889 : Nat := 4983230072969 + 3 ^ 40 * 7954889 * 2
def baseEnd_7954889 : Nat := 1361560536721277397967879

theorem tailTrace_7954889 : CollatzResearch.WordTrace tailWord_7954889 prefixEnd_7954889 1361560536721277397967879 := by
  unfold tailWord_7954889
  simp only [CollatzResearch.WordTrace]
  refine ⟨290138637677803214723683721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193425758451868809815789147 290138637677803214723683721)
  ·
    refine ⟨217603978258352411042762791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290138637677803214723683721 217603978258352411042762791)
    ·
      refine ⟨326405967387528616564144187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217603978258352411042762791 326405967387528616564144187)
      ·
        refine ⟨489608951081292924846216281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326405967387528616564144187 489608951081292924846216281)
        ·
          refine ⟨367206713310969693634662211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489608951081292924846216281 367206713310969693634662211)
          ·
            refine ⟨550810069966454540451993317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367206713310969693634662211 550810069966454540451993317)
            ·
              refine ⟨103276888118710226334748747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 550810069966454540451993317 103276888118710226334748747)
              ·
                refine ⟨154915332178065339502123121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103276888118710226334748747 154915332178065339502123121)
                ·
                  refine ⟨116186499133549004626592341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154915332178065339502123121 116186499133549004626592341)
                  ·
                    refine ⟨1361560536721277397967879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116186499133549004626592341 1361560536721277397967879)
                    ·
                      rfl

theorem cell23_7954889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_7954889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954889 prefixEnd_7954889 := by exact prefixLift 7954889
  have htrace : WordTrace (prefixWord ++ tailWord_7954889) baseStart_7954889 baseEnd_7954889 := by
    simpa [prefixWord, tailWord_7954889, baseEnd_7954889] using wordTrace_append hprefix tailTrace_7954889
  have hstable : (prefixWord ++ tailWord_7954889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954889).length < 2 ^ (prefixWord ++ tailWord_7954889).sum := by decide
  have hdescent : baseEnd_7954889 < baseStart_7954889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954913 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 2, 4, 2]
def baseStart_7954913 : Nat := 118140960795 + 7954913 * 2 ^ 59
def prefixEnd_7954913 : Nat := 4983230072969 + 3 ^ 40 * 7954913 * 2
def baseEnd_7954913 : Nat := 4084693933699540100003527

theorem tailTrace_7954913 : CollatzResearch.WordTrace tailWord_7954913 prefixEnd_7954913 4084693933699540100003527 := by
  unfold tailWord_7954913
  simp only [CollatzResearch.WordTrace]
  refine ⟨290139513029716266822557393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193426342019810844548371595 290139513029716266822557393)
  ·
    refine ⟨217604634772287200116918045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290139513029716266822557393 217604634772287200116918045)
    ·
      refine ⟨81601738039607700043844267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217604634772287200116918045 81601738039607700043844267)
      ·
        refine ⟨122402607059411550065766401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81601738039607700043844267 122402607059411550065766401)
        ·
          refine ⟨91801955294558662549324801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122402607059411550065766401 91801955294558662549324801)
          ·
            refine ⟨68851466470918996911993601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91801955294558662549324801 68851466470918996911993601)
            ·
              refine ⟨51638599853189247683995201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68851466470918996911993601 51638599853189247683995201)
              ·
                refine ⟨38728949889891935762996401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51638599853189247683995201 38728949889891935762996401)
                ·
                  refine ⟨29046712417418951822247301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38728949889891935762996401 29046712417418951822247301)
                  ·
                    refine ⟨5446258578266053466671369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29046712417418951822247301 5446258578266053466671369)
                    ·
                      refine ⟨4084693933699540100003527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446258578266053466671369 4084693933699540100003527)
                      ·
                        rfl

theorem cell23_7954913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_7954913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954913 prefixEnd_7954913 := by exact prefixLift 7954913
  have htrace : WordTrace (prefixWord ++ tailWord_7954913) baseStart_7954913 baseEnd_7954913 := by
    simpa [prefixWord, tailWord_7954913, baseEnd_7954913] using wordTrace_append hprefix tailTrace_7954913
  have hstable : (prefixWord ++ tailWord_7954913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954913).length < 2 ^ (prefixWord ++ tailWord_7954913).sum := by decide
  have hdescent : baseEnd_7954913 < baseStart_7954913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954916 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_7954916 : Nat := 118140960795 + 7954916 * 2 ^ 59
def prefixEnd_7954916 : Nat := 4983230072969 + 3 ^ 40 * 7954916 * 2
def baseEnd_7954916 : Nat := 4084695474141503588266013

theorem tailTrace_7954916 : CollatzResearch.WordTrace tailWord_7954916 prefixEnd_7954916 4084695474141503588266013 := by
  unfold tailWord_7954916
  simp only [CollatzResearch.WordTrace]
  refine ⟨145069811224352699167458301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193426414965803598889944401 145069811224352699167458301)
  ·
    refine ⟨54401179209132262187796863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145069811224352699167458301 54401179209132262187796863)
    ·
      refine ⟨81601768813698393281695295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54401179209132262187796863 81601768813698393281695295)
      ·
        refine ⟨122402653220547589922542943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81601768813698393281695295 122402653220547589922542943)
        ·
          refine ⟨183603979830821384883814415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122402653220547589922542943 183603979830821384883814415)
          ·
            refine ⟨275405969746232077325721623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183603979830821384883814415 275405969746232077325721623)
            ·
              refine ⟨413108954619348115988582435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275405969746232077325721623 413108954619348115988582435)
              ·
                refine ⟨619663431929022173982873653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413108954619348115988582435 619663431929022173982873653)
                ·
                  refine ⟨58093446743345828810894405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 619663431929022173982873653 58093446743345828810894405)
                  ·
                    refine ⟨10892521264377342902042701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58093446743345828810894405 10892521264377342902042701)
                    ·
                      refine ⟨4084695474141503588266013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10892521264377342902042701 4084695474141503588266013)
                      ·
                        rfl

theorem cell23_7954916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_7954916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954916 prefixEnd_7954916 := by exact prefixLift 7954916
  have htrace : WordTrace (prefixWord ++ tailWord_7954916) baseStart_7954916 baseEnd_7954916 := by
    simpa [prefixWord, tailWord_7954916, baseEnd_7954916] using wordTrace_append hprefix tailTrace_7954916
  have hstable : (prefixWord ++ tailWord_7954916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954916).length < 2 ^ (prefixWord ++ tailWord_7954916).sum := by decide
  have hdescent : baseEnd_7954916 < baseStart_7954916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954936 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 6]
def baseStart_7954936 : Nat := 118140960795 + 7954936 * 2 ^ 59
def prefixEnd_7954936 : Nat := 4983230072969 + 3 ^ 40 * 7954936 * 2
def baseEnd_7954936 : Nat := 453856193750510390001769

theorem tailTrace_7954936 : CollatzResearch.WordTrace tailWord_7954936 prefixEnd_7954936 453856193750510390001769 := by
  unfold tailWord_7954936
  simp only [CollatzResearch.WordTrace]
  refine ⟨145070175954316470875322331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193426901272421961167096441 145070175954316470875322331)
  ·
    refine ⟨217605263931474706312983497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145070175954316470875322331 217605263931474706312983497)
    ·
      refine ⟨163203947948606029734737623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217605263931474706312983497 163203947948606029734737623)
      ·
        refine ⟨244805921922909044602106435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163203947948606029734737623 244805921922909044602106435)
        ·
          refine ⟨367208882884363566903159653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244805921922909044602106435 367208882884363566903159653)
          ·
            refine ⟨68851665540818168794342435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367208882884363566903159653 68851665540818168794342435)
            ·
              refine ⟨103277498311227253191513653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68851665540818168794342435 103277498311227253191513653)
              ·
                refine ⟨9682265466677554986704405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103277498311227253191513653 9682265466677554986704405)
                ·
                  refine ⟨453856193750510390001769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9682265466677554986704405 453856193750510390001769)
                  ·
                    rfl

theorem cell23_7954936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 6].length) (baseStart_7954936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954936 prefixEnd_7954936 := by exact prefixLift 7954936
  have htrace : WordTrace (prefixWord ++ tailWord_7954936) baseStart_7954936 baseEnd_7954936 := by
    simpa [prefixWord, tailWord_7954936, baseEnd_7954936] using wordTrace_append hprefix tailTrace_7954936
  have hstable : (prefixWord ++ tailWord_7954936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954936).length < 2 ^ (prefixWord ++ tailWord_7954936).sum := by decide
  have hdescent : baseEnd_7954936 < baseStart_7954936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7954963 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 5, 1, 3]
def baseStart_7954963 : Nat := 118140960795 + 7954963 * 2 ^ 59
def prefixEnd_7954963 : Nat := 4983230072969 + 3 ^ 40 * 7954963 * 2
def baseEnd_7954963 : Nat := 4084719607732264904378297

theorem tailTrace_7954963 : CollatzResearch.WordTrace tailWord_7954963 prefixEnd_7954963 4084719607732264904378297 := by
  unfold tailWord_7954963
  simp only [CollatzResearch.WordTrace]
  refine ⟨290141336679535125361877543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193427557786356750241251695 290141336679535125361877543)
  ·
    refine ⟨435212005019302688042816315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290141336679535125361877543 435212005019302688042816315)
    ·
      refine ⟨652818007528954032064224473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435212005019302688042816315 652818007528954032064224473)
      ·
        refine ⟨489613505646715524048168355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652818007528954032064224473 489613505646715524048168355)
        ·
          refine ⟨734420258470073286072252533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489613505646715524048168355 734420258470073286072252533)
          ·
            refine ⟨68851899231569370569273675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 734420258470073286072252533 68851899231569370569273675)
            ·
              refine ⟨103277848847354055853910513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68851899231569370569273675 103277848847354055853910513)
              ·
                refine ⟨77458386635515541890432885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103277848847354055853910513 77458386635515541890432885)
                ·
                  refine ⟨7261723747079582052228083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77458386635515541890432885 7261723747079582052228083)
                  ·
                    refine ⟨10892585620619373078342125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7261723747079582052228083 10892585620619373078342125)
                    ·
                      refine ⟨4084719607732264904378297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10892585620619373078342125 4084719607732264904378297)
                      ·
                        rfl

theorem cell23_7954963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 1, 3].length) (baseStart_7954963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7954963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7954963 prefixEnd_7954963 := by exact prefixLift 7954963
  have htrace : WordTrace (prefixWord ++ tailWord_7954963) baseStart_7954963 baseEnd_7954963 := by
    simpa [prefixWord, tailWord_7954963, baseEnd_7954963] using wordTrace_append hprefix tailTrace_7954963
  have hstable : (prefixWord ++ tailWord_7954963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7954963).length < 2 ^ (prefixWord ++ tailWord_7954963).sum := by decide
  have hdescent : baseEnd_7954963 < baseStart_7954963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7954963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955013 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_7955013 : Nat := 118140960795 + 7955013 * 2 ^ 59
def prefixEnd_7955013 : Nat := 4983230072969 + 3 ^ 40 * 7955013 * 2
def baseEnd_7955013 : Nat := 1361581760588329902917689

theorem tailTrace_7955013 : CollatzResearch.WordTrace tailWord_7955013 prefixEnd_7955013 1361581760588329902917689 := by
  unfold tailWord_7955013
  simp only [CollatzResearch.WordTrace]
  refine ⟨290143160329353983901197693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193428773552902655934131795 290143160329353983901197693)
  ·
    refine ⟨108803685123507743962949135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290143160329353983901197693 108803685123507743962949135)
    ·
      refine ⟨163205527685261615944423703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108803685123507743962949135 163205527685261615944423703)
      ·
        refine ⟨244808291527892423916635555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163205527685261615944423703 244808291527892423916635555)
        ·
          refine ⟨367212437291838635874953333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244808291527892423916635555 367212437291838635874953333)
          ·
            refine ⟨34426165996109872113276875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367212437291838635874953333 34426165996109872113276875)
            ·
              refine ⟨51639248994164808169915313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34426165996109872113276875 51639248994164808169915313)
              ·
                refine ⟨38729436745623606127436485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51639248994164808169915313 38729436745623606127436485)
                ·
                  refine ⟨7261769389804426148894341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38729436745623606127436485 7261769389804426148894341)
                  ·
                    refine ⟨1361581760588329902917689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7261769389804426148894341 1361581760588329902917689)
                    ·
                      rfl

theorem cell23_7955013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_7955013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955013 prefixEnd_7955013 := by exact prefixLift 7955013
  have htrace : WordTrace (prefixWord ++ tailWord_7955013) baseStart_7955013 baseEnd_7955013 := by
    simpa [prefixWord, tailWord_7955013, baseEnd_7955013] using wordTrace_append hprefix tailTrace_7955013
  have hstable : (prefixWord ++ tailWord_7955013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955013).length < 2 ^ (prefixWord ++ tailWord_7955013).sum := by decide
  have hdescent : baseEnd_7955013 < baseStart_7955013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955038 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_7955038 : Nat := 118140960795 + 7955038 * 2 ^ 59
def prefixEnd_7955038 : Nat := 4983230072969 + 3 ^ 40 * 7955038 * 2
def baseEnd_7955038 : Nat := 453862013197928012326717

theorem tailTrace_7955038 : CollatzResearch.WordTrace tailWord_7955038 prefixEnd_7955038 453862013197928012326717 := by
  unfold tailWord_7955038
  simp only [CollatzResearch.WordTrace]
  refine ⟨36268009019282926646357221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193429381436175608780571845 36268009019282926646357221)
  ·
    refine ⟨6800251691115548746191979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36268009019282926646357221 6800251691115548746191979)
    ·
      refine ⟨10200377536673323119287969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6800251691115548746191979 10200377536673323119287969)
      ·
        refine ⟨7650283152504992339465977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10200377536673323119287969 7650283152504992339465977)
        ·
          refine ⟨5737712364378744254599483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7650283152504992339465977 5737712364378744254599483)
          ·
            refine ⟨8606568546568116381899225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737712364378744254599483 8606568546568116381899225)
            ·
              refine ⟨6454926409926087286424419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8606568546568116381899225 6454926409926087286424419)
              ·
                refine ⟨9682389614889130929636629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6454926409926087286424419 9682389614889130929636629)
                ·
                  refine ⟨453862013197928012326717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9682389614889130929636629 453862013197928012326717)
                  ·
                    rfl

theorem cell23_7955038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_7955038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955038 prefixEnd_7955038 := by exact prefixLift 7955038
  have htrace : WordTrace (prefixWord ++ tailWord_7955038) baseStart_7955038 baseEnd_7955038 := by
    simpa [prefixWord, tailWord_7955038, baseEnd_7955038] using wordTrace_append hprefix tailTrace_7955038
  have hstable : (prefixWord ++ tailWord_7955038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955038).length < 2 ^ (prefixWord ++ tailWord_7955038).sum := by decide
  have hdescent : baseEnd_7955038 < baseStart_7955038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955066 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_7955066 : Nat := 118140960795 + 7955066 * 2 ^ 59
def prefixEnd_7955066 : Nat := 4983230072969 + 3 ^ 40 * 7955066 * 2
def baseEnd_7955066 : Nat := 4084772496239678001390323

theorem tailTrace_7955066 : CollatzResearch.WordTrace tailWord_7955066 prefixEnd_7955066 4084772496239678001390323 := by
  unfold tailWord_7955066
  simp only [CollatzResearch.WordTrace]
  refine ⟨72536273349540493488219263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193430062265441315968584701 72536273349540493488219263)
  ·
    refine ⟨108804410024310740232328895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72536273349540493488219263 108804410024310740232328895)
    ·
      refine ⟨163206615036466110348493343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108804410024310740232328895 163206615036466110348493343)
      ·
        refine ⟨244809922554699165522740015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163206615036466110348493343 244809922554699165522740015)
        ·
          refine ⟨367214883832048748284110023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244809922554699165522740015 367214883832048748284110023)
          ·
            refine ⟨550822325748073122426165035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367214883832048748284110023 550822325748073122426165035)
            ·
              refine ⟨826233488622109683639247553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550822325748073122426165035 826233488622109683639247553)
              ·
                refine ⟨619675116466582262729435665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826233488622109683639247553 619675116466582262729435665)
                ·
                  refine ⟨464756337349936697047076749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619675116466582262729435665 464756337349936697047076749)
                  ·
                    refine ⟨174283626506226261392653781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 464756337349936697047076749 174283626506226261392653781)
                    ·
                      refine ⟨4084772496239678001390323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174283626506226261392653781 4084772496239678001390323)
                      ·
                        rfl

theorem cell23_7955066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_7955066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955066 prefixEnd_7955066 := by exact prefixLift 7955066
  have htrace : WordTrace (prefixWord ++ tailWord_7955066) baseStart_7955066 baseEnd_7955066 := by
    simpa [prefixWord, tailWord_7955066, baseEnd_7955066] using wordTrace_append hprefix tailTrace_7955066
  have hstable : (prefixWord ++ tailWord_7955066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955066).length < 2 ^ (prefixWord ++ tailWord_7955066).sum := by decide
  have hdescent : baseEnd_7955066 < baseStart_7955066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955140 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_7955140 : Nat := 118140960795 + 7955140 * 2 ^ 59
def prefixEnd_7955140 : Nat := 4983230072969 + 3 ^ 40 * 7955140 * 2
def baseEnd_7955140 : Nat := 4084810493808110711864983

theorem tailTrace_7955140 : CollatzResearch.WordTrace tailWord_7955140 prefixEnd_7955140 4084810493808110711864983 := by
  unfold tailWord_7955140
  simp only [CollatzResearch.WordTrace]
  refine ⟨145073896199946942295535437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193431861599929256394047249 145073896199946942295535437)
  ·
    refine ⟨54402711074980103360825789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145073896199946942295535437 54402711074980103360825789)
    ·
      refine ⟨20401016653117538760309671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54402711074980103360825789 20401016653117538760309671)
      ·
        refine ⟨30601524979676308140464507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20401016653117538760309671 30601524979676308140464507)
        ·
          refine ⟨45902287469514462210696761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30601524979676308140464507 45902287469514462210696761)
          ·
            refine ⟨34426715602135846658022571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45902287469514462210696761 34426715602135846658022571)
            ·
              refine ⟨51640073403203769987033857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34426715602135846658022571 51640073403203769987033857)
              ·
                refine ⟨38730055052402827490275393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51640073403203769987033857 38730055052402827490275393)
                ·
                  refine ⟨29047541289302120617706545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38730055052402827490275393 29047541289302120617706545)
                  ·
                    refine ⟨21785655966976590463279909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29047541289302120617706545 21785655966976590463279909)
                    ·
                      refine ⟨4084810493808110711864983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21785655966976590463279909 4084810493808110711864983)
                      ·
                        rfl

theorem cell23_7955140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_7955140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955140 prefixEnd_7955140 := by exact prefixLift 7955140
  have htrace : WordTrace (prefixWord ++ tailWord_7955140) baseStart_7955140 baseEnd_7955140 := by
    simpa [prefixWord, tailWord_7955140, baseEnd_7955140] using wordTrace_append hprefix tailTrace_7955140
  have hstable : (prefixWord ++ tailWord_7955140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955140).length < 2 ^ (prefixWord ++ tailWord_7955140).sum := by decide
  have hdescent : baseEnd_7955140 < baseStart_7955140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955144 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 2, 2, 2]
def baseStart_7955144 : Nat := 118140960795 + 7955144 * 2 ^ 59
def prefixEnd_7955144 : Nat := 4983230072969 + 3 ^ 40 * 7955144 * 2
def baseEnd_7955144 : Nat := 4084812547730728696214965

theorem tailTrace_7955144 : CollatzResearch.WordTrace tailWord_7955144 prefixEnd_7955144 4084812547730728696214965 := by
  unfold tailWord_7955144
  simp only [CollatzResearch.WordTrace]
  refine ⟨145073969145939696637108243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193431958861252928849477657 145073969145939696637108243)
  ·
    refine ⟨217610953718909544955662365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145073969145939696637108243 217610953718909544955662365)
    ·
      refine ⟨81604107644591079358373387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217610953718909544955662365 81604107644591079358373387)
      ·
        refine ⟨122406161466886619037560081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81604107644591079358373387 122406161466886619037560081)
        ·
          refine ⟨91804621100164964278170061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122406161466886619037560081 91804621100164964278170061)
          ·
            refine ⟨34426732912561861604313773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91804621100164964278170061 34426732912561861604313773)
            ·
              refine ⟨12910024842210698101617665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34426732912561861604313773 12910024842210698101617665)
              ·
                refine ⟨9682518631658023576213249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12910024842210698101617665 9682518631658023576213249)
                ·
                  refine ⟨7261888973743517682159937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9682518631658023576213249 7261888973743517682159937)
                  ·
                    refine ⟨5446416730307638261619953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7261888973743517682159937 5446416730307638261619953)
                    ·
                      refine ⟨4084812547730728696214965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446416730307638261619953 4084812547730728696214965)
                      ·
                        rfl

theorem cell23_7955144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_7955144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955144 prefixEnd_7955144 := by exact prefixLift 7955144
  have htrace : WordTrace (prefixWord ++ tailWord_7955144) baseStart_7955144 baseEnd_7955144 := by
    simpa [prefixWord, tailWord_7955144, baseEnd_7955144] using wordTrace_append hprefix tailTrace_7955144
  have hstable : (prefixWord ++ tailWord_7955144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955144).length < 2 ^ (prefixWord ++ tailWord_7955144).sum := by decide
  have hdescent : baseEnd_7955144 < baseStart_7955144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955150 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_7955150 : Nat := 118140960795 + 7955150 * 2 ^ 59
def prefixEnd_7955150 : Nat := 4983230072969 + 3 ^ 40 * 7955150 * 2
def baseEnd_7955150 : Nat := 453868403179406185859993

theorem tailTrace_7955150 : CollatzResearch.WordTrace tailWord_7955150 prefixEnd_7955150 453868403179406185859993 := by
  unfold tailWord_7955150
  simp only [CollatzResearch.WordTrace]
  refine ⟨36268519641232207037366863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193432104753238437532623269 36268519641232207037366863)
  ·
    refine ⟨54402779461848310556050295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36268519641232207037366863 54402779461848310556050295)
    ·
      refine ⟨81604169192772465834075443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54402779461848310556050295 81604169192772465834075443)
      ·
        refine ⟨122406253789158698751113165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81604169192772465834075443 122406253789158698751113165)
        ·
          refine ⟨45902345170934512031667437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122406253789158698751113165 45902345170934512031667437)
          ·
            refine ⟨17213379439100442011875289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45902345170934512031667437 17213379439100442011875289)
            ·
              refine ⟨12910034579325331508906467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17213379439100442011875289 12910034579325331508906467)
              ·
                refine ⟨19365051868987997263359701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12910034579325331508906467 19365051868987997263359701)
                ·
                  refine ⟨453868403179406185859993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19365051868987997263359701 453868403179406185859993)
                  ·
                    rfl

theorem cell23_7955150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_7955150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955150 prefixEnd_7955150 := by exact prefixLift 7955150
  have htrace : WordTrace (prefixWord ++ tailWord_7955150) baseStart_7955150 baseEnd_7955150 := by
    simpa [prefixWord, tailWord_7955150, baseEnd_7955150] using wordTrace_append hprefix tailTrace_7955150
  have hstable : (prefixWord ++ tailWord_7955150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955150).length < 2 ^ (prefixWord ++ tailWord_7955150).sum := by decide
  have hdescent : baseEnd_7955150 < baseStart_7955150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955160 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 2, 3, 3]
def baseStart_7955160 : Nat := 118140960795 + 7955160 * 2 ^ 59
def prefixEnd_7955160 : Nat := 4983230072969 + 3 ^ 40 * 7955160 * 2
def baseEnd_7955160 : Nat := 4084820763421200633614891

theorem tailTrace_7955160 : CollatzResearch.WordTrace tailWord_7955160 prefixEnd_7955160 4084820763421200633614891 := by
  unfold tailWord_7955160
  simp only [CollatzResearch.WordTrace]
  refine ⟨145074260929910714003399467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193432347906547618671199289 145074260929910714003399467)
  ·
    refine ⟨217611391394866071005099201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145074260929910714003399467 217611391394866071005099201)
    ·
      refine ⟨163208543546149553253824401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217611391394866071005099201 163208543546149553253824401)
      ·
        refine ⟨122406407659612164940368301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163208543546149553253824401 122406407659612164940368301)
        ·
          refine ⟨45902402872354561852638113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122406407659612164940368301 45902402872354561852638113)
          ·
            refine ⟨34426802154265921389478585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45902402872354561852638113 34426802154265921389478585)
            ·
              refine ⟨25820101615699441042108939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34426802154265921389478585 25820101615699441042108939)
              ·
                refine ⟨38730152423549161563163409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25820101615699441042108939 38730152423549161563163409)
                ·
                  refine ⟨29047614317661871172372557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38730152423549161563163409 29047614317661871172372557)
                  ·
                    refine ⟨10892855369123201689639709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29047614317661871172372557 10892855369123201689639709)
                    ·
                      refine ⟨4084820763421200633614891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10892855369123201689639709 4084820763421200633614891)
                      ·
                        rfl

theorem cell23_7955160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_7955160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955160 prefixEnd_7955160 := by exact prefixLift 7955160
  have htrace : WordTrace (prefixWord ++ tailWord_7955160) baseStart_7955160 baseEnd_7955160 := by
    simpa [prefixWord, tailWord_7955160, baseEnd_7955160] using wordTrace_append hprefix tailTrace_7955160
  have hstable : (prefixWord ++ tailWord_7955160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955160).length < 2 ^ (prefixWord ++ tailWord_7955160).sum := by decide
  have hdescent : baseEnd_7955160 < baseStart_7955160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955190 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_7955190 : Nat := 118140960795 + 7955190 * 2 ^ 59
def prefixEnd_7955190 : Nat := 4983230072969 + 3 ^ 40 * 7955190 * 2
def baseEnd_7955190 : Nat := 4084836167840835516239753

theorem tailTrace_7955190 : CollatzResearch.WordTrace tailWord_7955190 prefixEnd_7955190 4084836167840835516239753 := by
  unfold tailWord_7955190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18134351003107046445649439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193433077366475162086927349 18134351003107046445649439)
  ·
    refine ⟨27201526504660569668474159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18134351003107046445649439 27201526504660569668474159)
    ·
      refine ⟨40802289756990854502711239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27201526504660569668474159 40802289756990854502711239)
      ·
        refine ⟨61203434635486281754066859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40802289756990854502711239 61203434635486281754066859)
        ·
          refine ⟨91805151953229422631100289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61203434635486281754066859 91805151953229422631100289)
          ·
            refine ⟨68853863964922066973325217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91805151953229422631100289 68853863964922066973325217)
            ·
              refine ⟨51640397973691550229993913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68853863964922066973325217 51640397973691550229993913)
              ·
                refine ⟨38730298480268662672495435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51640397973691550229993913 38730298480268662672495435)
                ·
                  refine ⟨58095447720402994008743153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38730298480268662672495435 58095447720402994008743153)
                  ·
                    refine ⟨43571585790302245506557365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58095447720402994008743153 43571585790302245506557365)
                    ·
                      refine ⟨4084836167840835516239753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43571585790302245506557365 4084836167840835516239753)
                      ·
                        rfl

theorem cell23_7955190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_7955190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955190 prefixEnd_7955190 := by exact prefixLift 7955190
  have htrace : WordTrace (prefixWord ++ tailWord_7955190) baseStart_7955190 baseEnd_7955190 := by
    simpa [prefixWord, tailWord_7955190, baseEnd_7955190] using wordTrace_append hprefix tailTrace_7955190
  have hstable : (prefixWord ++ tailWord_7955190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955190).length < 2 ^ (prefixWord ++ tailWord_7955190).sum := by decide
  have hdescent : baseEnd_7955190 < baseStart_7955190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955237 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 2, 2, 3]
def baseStart_7955237 : Nat := 118140960795 + 7955237 * 2 ^ 59
def prefixEnd_7955237 : Nat := 4983230072969 + 3 ^ 40 * 7955237 * 2
def baseEnd_7955237 : Nat := 4084860301431596832352037

theorem tailTrace_7955237 : CollatzResearch.WordTrace tailWord_7955237 prefixEnd_7955237 4084860301431596832352037 := by
  unfold tailWord_7955237
  simp only [CollatzResearch.WordTrace]
  refine ⟨290151330280542470157351965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193434220187028313438234643 290151330280542470157351965)
  ·
    refine ⟨108806748855203426309006987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290151330280542470157351965 108806748855203426309006987)
    ·
      refine ⟨163210123282805139463510481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108806748855203426309006987 163210123282805139463510481)
      ·
        refine ⟨122407592462103854597632861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163210123282805139463510481 122407592462103854597632861)
        ·
          refine ⟨45902847173288945474112323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122407592462103854597632861 45902847173288945474112323)
          ·
            refine ⟨68854270759933418211168485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45902847173288945474112323 68854270759933418211168485)
            ·
              refine ⟨12910175767487515914594091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68854270759933418211168485 12910175767487515914594091)
              ·
                refine ⟨19365263651231273871891137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12910175767487515914594091 19365263651231273871891137)
                ·
                  refine ⟨14523947738423455403918353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19365263651231273871891137 14523947738423455403918353)
                  ·
                    refine ⟨10892960803817591552938765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14523947738423455403918353 10892960803817591552938765)
                    ·
                      refine ⟨4084860301431596832352037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10892960803817591552938765 4084860301431596832352037)
                      ·
                        rfl

theorem cell23_7955237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_7955237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955237 prefixEnd_7955237 := by exact prefixLift 7955237
  have htrace : WordTrace (prefixWord ++ tailWord_7955237) baseStart_7955237 baseEnd_7955237 := by
    simpa [prefixWord, tailWord_7955237, baseEnd_7955237] using wordTrace_append hprefix tailTrace_7955237
  have hstable : (prefixWord ++ tailWord_7955237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955237).length < 2 ^ (prefixWord ++ tailWord_7955237).sum := by decide
  have hdescent : baseEnd_7955237 < baseStart_7955237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955261 : List Nat := [1, 4, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_7955261 : Nat := 118140960795 + 7955261 * 2 ^ 59
def prefixEnd_7955261 : Nat := 4983230072969 + 3 ^ 40 * 7955261 * 2
def baseEnd_7955261 : Nat := 1361624208322434912817309

theorem tailTrace_7955261 : CollatzResearch.WordTrace tailWord_7955261 prefixEnd_7955261 1361624208322434912817309 := by
  unfold tailWord_7955261
  simp only [CollatzResearch.WordTrace]
  refine ⟨290152205632455522256225637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193434803754970348170817091 290152205632455522256225637)
  ·
    refine ⟨54403538556085410423042307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290152205632455522256225637 54403538556085410423042307)
    ·
      refine ⟨81605307834128115634563461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54403538556085410423042307 81605307834128115634563461)
      ·
        refine ⟨15300995218899021681480649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81605307834128115634563461 15300995218899021681480649)
        ·
          refine ⟨11475746414174266261110487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15300995218899021681480649 11475746414174266261110487)
          ·
            refine ⟨17213619621261399391665731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11475746414174266261110487 17213619621261399391665731)
            ·
              refine ⟨25820429431892099087498597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17213619621261399391665731 25820429431892099087498597)
              ·
                refine ⟨4841330518479768578905987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25820429431892099087498597 4841330518479768578905987)
                ·
                  refine ⟨7261995777719652868358981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841330518479768578905987 7261995777719652868358981)
                  ·
                    refine ⟨1361624208322434912817309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7261995777719652868358981 1361624208322434912817309)
                    ·
                      rfl

theorem cell23_7955261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_7955261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955261 prefixEnd_7955261 := by exact prefixLift 7955261
  have htrace : WordTrace (prefixWord ++ tailWord_7955261) baseStart_7955261 baseEnd_7955261 := by
    simpa [prefixWord, tailWord_7955261, baseEnd_7955261] using wordTrace_append hprefix tailTrace_7955261
  have hstable : (prefixWord ++ tailWord_7955261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955261).length < 2 ^ (prefixWord ++ tailWord_7955261).sum := by decide
  have hdescent : baseEnd_7955261 < baseStart_7955261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955267 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 3, 1, 3]
def baseStart_7955267 : Nat := 118140960795 + 7955267 * 2 ^ 59
def prefixEnd_7955267 : Nat := 4983230072969 + 3 ^ 40 * 7955267 * 2
def baseEnd_7955267 : Nat := 4084875705851231714976899

theorem tailTrace_7955267 : CollatzResearch.WordTrace tailWord_7955267 prefixEnd_7955267 4084875705851231714976899 := by
  unfold tailWord_7955267
  simp only [CollatzResearch.WordTrace]
  refine ⟨290152424470433785280944055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193434949646955856853962703 290152424470433785280944055)
  ·
    refine ⟨435228636705650677921416083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290152424470433785280944055 435228636705650677921416083)
    ·
      refine ⟨652842955058476016882124125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435228636705650677921416083 652842955058476016882124125)
      ·
        refine ⟨244816108146928506330796547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 652842955058476016882124125 244816108146928506330796547)
        ·
          refine ⟨367224162220392759496194821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244816108146928506330796547 367224162220392759496194821)
          ·
            refine ⟨68854530416323642405536529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367224162220392759496194821 68854530416323642405536529)
            ·
              refine ⟨51640897812242731804152397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68854530416323642405536529 51640897812242731804152397)
              ·
                refine ⟨19365336679591024426557149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51640897812242731804152397 19365336679591024426557149)
                ·
                  refine ⟨7262001254846634159958931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19365336679591024426557149 7262001254846634159958931)
                  ·
                    refine ⟨10893001882269951239938397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7262001254846634159958931 10893001882269951239938397)
                    ·
                      refine ⟨4084875705851231714976899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10893001882269951239938397 4084875705851231714976899)
                      ·
                        rfl

theorem cell23_7955267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_7955267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955267 prefixEnd_7955267 := by exact prefixLift 7955267
  have htrace : WordTrace (prefixWord ++ tailWord_7955267) baseStart_7955267 baseEnd_7955267 := by
    simpa [prefixWord, tailWord_7955267, baseEnd_7955267] using wordTrace_append hprefix tailTrace_7955267
  have hstable : (prefixWord ++ tailWord_7955267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955267).length < 2 ^ (prefixWord ++ tailWord_7955267).sum := by decide
  have hdescent : baseEnd_7955267 < baseStart_7955267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955304 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 1, 5]
def baseStart_7955304 : Nat := 118140960795 + 7955304 * 2 ^ 59
def prefixEnd_7955304 : Nat := 4983230072969 + 3 ^ 40 * 7955304 * 2
def baseEnd_7955304 : Nat := 1361631568211816023404743

theorem tailTrace_7955304 : CollatzResearch.WordTrace tailWord_7955304 prefixEnd_7955304 1361631568211816023404743 := by
  unfold tailWord_7955304
  simp only [CollatzResearch.WordTrace]
  refine ⟨145076886985649870300020483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193435849314199827066693977 145076886985649870300020483)
  ·
    refine ⟨217615330478474805450030725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145076886985649870300020483 217615330478474805450030725)
    ·
      refine ⟨40802874464714026021880761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217615330478474805450030725 40802874464714026021880761)
      ·
        refine ⟨30602155848535519516410571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40802874464714026021880761 30602155848535519516410571)
        ·
          refine ⟨45903233772803279274615857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30602155848535519516410571 45903233772803279274615857)
          ·
            refine ⟨34427425329602459455961893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45903233772803279274615857 34427425329602459455961893)
            ·
              refine ⟨6455142249300461147992855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34427425329602459455961893 6455142249300461147992855)
              ·
                refine ⟨9682713373950691721989283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6455142249300461147992855 9682713373950691721989283)
                ·
                  refine ⟨14524070060926037582983925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9682713373950691721989283 14524070060926037582983925)
                  ·
                    refine ⟨1361631568211816023404743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14524070060926037582983925 1361631568211816023404743)
                    ·
                      rfl

theorem cell23_7955304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_7955304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955304 prefixEnd_7955304 := by exact prefixLift 7955304
  have htrace : WordTrace (prefixWord ++ tailWord_7955304) baseStart_7955304 baseEnd_7955304 := by
    simpa [prefixWord, tailWord_7955304, baseEnd_7955304] using wordTrace_append hprefix tailTrace_7955304
  have hstable : (prefixWord ++ tailWord_7955304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955304).length < 2 ^ (prefixWord ++ tailWord_7955304).sum := by decide
  have hdescent : baseEnd_7955304 < baseStart_7955304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955318 : List Nat := [5, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_7955318 : Nat := 118140960795 + 7955318 * 2 ^ 59
def prefixEnd_7955318 : Nat := 4983230072969 + 3 ^ 40 * 7955318 * 2
def baseEnd_7955318 : Nat := 4084901893364611015439165

theorem tailTrace_7955318 : CollatzResearch.WordTrace tailWord_7955318 prefixEnd_7955318 4084901893364611015439165 := by
  unfold tailWord_7955318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18134642787078063811940663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193436189728832680660700405 18134642787078063811940663)
  ·
    refine ⟨27201964180617095717910995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18134642787078063811940663 27201964180617095717910995)
    ·
      refine ⟨40802946270925643576866493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27201964180617095717910995 40802946270925643576866493)
      ·
        refine ⟨15301104851597116341324935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40802946270925643576866493 15301104851597116341324935)
        ·
          refine ⟨22951657277395674511987403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15301104851597116341324935 22951657277395674511987403)
          ·
            refine ⟨34427485916093511767981105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22951657277395674511987403 34427485916093511767981105)
            ·
              refine ⟨25820614437070133825985829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34427485916093511767981105 25820614437070133825985829)
              ·
                refine ⟨4841365206950650092372343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25820614437070133825985829 4841365206950650092372343)
                ·
                  refine ⟨7262047810425975138558515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841365206950650092372343 7262047810425975138558515)
                  ·
                    refine ⟨10893071715638962707837773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7262047810425975138558515 10893071715638962707837773)
                    ·
                      refine ⟨4084901893364611015439165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10893071715638962707837773 4084901893364611015439165)
                      ·
                        rfl

theorem cell23_7955318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_7955318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955318 prefixEnd_7955318 := by exact prefixLift 7955318
  have htrace : WordTrace (prefixWord ++ tailWord_7955318) baseStart_7955318 baseEnd_7955318 := by
    simpa [prefixWord, tailWord_7955318, baseEnd_7955318] using wordTrace_append hprefix tailTrace_7955318
  have hstable : (prefixWord ++ tailWord_7955318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955318).length < 2 ^ (prefixWord ++ tailWord_7955318).sum := by decide
  have hdescent : baseEnd_7955318 < baseStart_7955318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955337 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 4]
def baseStart_7955337 : Nat := 118140960795 + 7955337 * 2 ^ 59
def prefixEnd_7955337 : Nat := 4983230072969 + 3 ^ 40 * 7955337 * 2
def baseEnd_7955337 : Nat := 4084911649497046441101577

theorem tailTrace_7955337 : CollatzResearch.WordTrace tailWord_7955337 prefixEnd_7955337 4084911649497046441101577 := by
  unfold tailWord_7955337
  simp only [CollatzResearch.WordTrace]
  refine ⟨290154977580180187235992265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193436651720120124823994843 290154977580180187235992265)
  ·
    refine ⟨217616233185135140426994199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290154977580180187235992265 217616233185135140426994199)
    ·
      refine ⟨326424349777702710640491299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217616233185135140426994199 326424349777702710640491299)
      ·
        refine ⟨489636524666554065960736949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326424349777702710640491299 489636524666554065960736949)
        ·
          refine ⟨45903424187489443683819089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 489636524666554065960736949 45903424187489443683819089)
          ·
            refine ⟨34427568140617082762864317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45903424187489443683819089 34427568140617082762864317)
            ·
              refine ⟨12910338052731406036074119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34427568140617082762864317 12910338052731406036074119)
              ·
                refine ⟨19365507079097109054111179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12910338052731406036074119 19365507079097109054111179)
                ·
                  refine ⟨29048260618645663581166769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19365507079097109054111179 29048260618645663581166769)
                  ·
                    refine ⟨21786195463984247685875077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29048260618645663581166769 21786195463984247685875077)
                    ·
                      refine ⟨4084911649497046441101577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21786195463984247685875077 4084911649497046441101577)
                      ·
                        rfl

theorem cell23_7955337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 2, 4].length) (baseStart_7955337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955337 prefixEnd_7955337 := by exact prefixLift 7955337
  have htrace : WordTrace (prefixWord ++ tailWord_7955337) baseStart_7955337 baseEnd_7955337 := by
    simpa [prefixWord, tailWord_7955337, baseEnd_7955337] using wordTrace_append hprefix tailTrace_7955337
  have hstable : (prefixWord ++ tailWord_7955337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955337).length < 2 ^ (prefixWord ++ tailWord_7955337).sum := by decide
  have hdescent : baseEnd_7955337 < baseStart_7955337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955357 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_7955357 : Nat := 118140960795 + 7955357 * 2 ^ 59
def prefixEnd_7955357 : Nat := 4983230072969 + 3 ^ 40 * 7955357 * 2
def baseEnd_7955357 : Nat := 4084921919110136362851485

theorem tailTrace_7955357 : CollatzResearch.WordTrace tailWord_7955357 prefixEnd_7955357 4084921919110136362851485 := by
  unfold tailWord_7955357
  simp only [CollatzResearch.WordTrace]
  refine ⟨290155707040107730651720325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193437138026738487101146883 290155707040107730651720325)
  ·
    refine ⟨54404195070020199497197561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290155707040107730651720325 54404195070020199497197561)
    ·
      refine ⟨40803146302515149622898171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54404195070020199497197561 40803146302515149622898171)
      ·
        refine ⟨61204719453772724434347257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40803146302515149622898171 61204719453772724434347257)
        ·
          refine ⟨45903539590329543325760443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61204719453772724434347257 45903539590329543325760443)
          ·
            refine ⟨68855309385494314988640665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45903539590329543325760443 68855309385494314988640665)
            ·
              refine ⟨51641482039120736241480499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68855309385494314988640665 51641482039120736241480499)
              ·
                refine ⟨77462223058681104362220749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51641482039120736241480499 77462223058681104362220749)
                ·
                  refine ⟨29048333647005414135832781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77462223058681104362220749 29048333647005414135832781)
                  ·
                    refine ⟨10893125117627030300937293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29048333647005414135832781 10893125117627030300937293)
                    ·
                      refine ⟨4084921919110136362851485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10893125117627030300937293 4084921919110136362851485)
                      ·
                        rfl

theorem cell23_7955357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_7955357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955357 prefixEnd_7955357 := by exact prefixLift 7955357
  have htrace : WordTrace (prefixWord ++ tailWord_7955357) baseStart_7955357 baseEnd_7955357 := by
    simpa [prefixWord, tailWord_7955357, baseEnd_7955357] using wordTrace_append hprefix tailTrace_7955357
  have hstable : (prefixWord ++ tailWord_7955357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955357).length < 2 ^ (prefixWord ++ tailWord_7955357).sum := by decide
  have hdescent : baseEnd_7955357 < baseStart_7955357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955417 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_7955417 : Nat := 118140960795 + 7955417 * 2 ^ 59
def prefixEnd_7955417 : Nat := 4983230072969 + 3 ^ 40 * 7955417 * 2
def baseEnd_7955417 : Nat := 4084952727949406128101209

theorem tailTrace_7955417 : CollatzResearch.WordTrace tailWord_7955417 prefixEnd_7955417 4084952727949406128101209 := by
  unfold tailWord_7955417
  simp only [CollatzResearch.WordTrace]
  refine ⟨290157895419890360898904505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193438596946593573932603003 290157895419890360898904505)
  ·
    refine ⟨217618421564917770674178379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290157895419890360898904505 217618421564917770674178379)
    ·
      refine ⟨326427632347376656011267569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217618421564917770674178379 326427632347376656011267569)
      ·
        refine ⟨244820724260532492008450677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326427632347376656011267569 244820724260532492008450677)
        ·
          refine ⟨22951942899424921125792251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244820724260532492008450677 22951942899424921125792251)
          ·
            refine ⟨34427914349137381688688377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22951942899424921125792251 34427914349137381688688377)
            ·
              refine ⟨25820935761853036266516283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34427914349137381688688377 25820935761853036266516283)
              ·
                refine ⟨38731403642779554399774425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25820935761853036266516283 38731403642779554399774425)
                ·
                  refine ⟨29048552732084665799830819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38731403642779554399774425 29048552732084665799830819)
                  ·
                    refine ⟨43572829098126998699746229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29048552732084665799830819 43572829098126998699746229)
                    ·
                      refine ⟨4084952727949406128101209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43572829098126998699746229 4084952727949406128101209)
                      ·
                        rfl

theorem cell23_7955417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_7955417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955417 prefixEnd_7955417 := by exact prefixLift 7955417
  have htrace : WordTrace (prefixWord ++ tailWord_7955417) baseStart_7955417 baseEnd_7955417 := by
    simpa [prefixWord, tailWord_7955417, baseEnd_7955417] using wordTrace_append hprefix tailTrace_7955417
  have hstable : (prefixWord ++ tailWord_7955417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955417).length < 2 ^ (prefixWord ++ tailWord_7955417).sum := by decide
  have hdescent : baseEnd_7955417 < baseStart_7955417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955418 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2]
def baseStart_7955418 : Nat := 118140960795 + 7955418 * 2 ^ 59
def prefixEnd_7955418 : Nat := 4983230072969 + 3 ^ 40 * 7955418 * 2
def baseEnd_7955418 : Nat := 4084953241430060624188705

theorem tailTrace_7955418 : CollatzResearch.WordTrace tailWord_7955418 prefixEnd_7955418 4084953241430060624188705 := by
  unfold tailWord_7955418
  simp only [CollatzResearch.WordTrace]
  refine ⟨72539482973221684517422727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193438621261924492046460605 72539482973221684517422727)
  ·
    refine ⟨108809224459832526776134091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72539482973221684517422727 108809224459832526776134091)
    ·
      refine ⟨163213836689748790164201137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108809224459832526776134091 163213836689748790164201137)
      ·
        refine ⟨122410377517311592623150853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163213836689748790164201137 122410377517311592623150853)
        ·
          refine ⟨22951945784495923616840785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122410377517311592623150853 22951945784495923616840785)
          ·
            refine ⟨17213959338371942712630589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22951945784495923616840785 17213959338371942712630589)
            ·
              refine ⟨6455234751889478517236471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17213959338371942712630589 6455234751889478517236471)
              ·
                refine ⟨9682852127834217775854707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6455234751889478517236471 9682852127834217775854707)
                ·
                  refine ⟨14524278191751326663782061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9682852127834217775854707 14524278191751326663782061)
                  ·
                    refine ⟨5446604321906747498918273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14524278191751326663782061 5446604321906747498918273)
                    ·
                      refine ⟨4084953241430060624188705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446604321906747498918273 4084953241430060624188705)
                      ·
                        rfl

theorem cell23_7955418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_7955418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955418 prefixEnd_7955418 := by exact prefixLift 7955418
  have htrace : WordTrace (prefixWord ++ tailWord_7955418) baseStart_7955418 baseEnd_7955418 := by
    simpa [prefixWord, tailWord_7955418, baseEnd_7955418] using wordTrace_append hprefix tailTrace_7955418
  have hstable : (prefixWord ++ tailWord_7955418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955418).length < 2 ^ (prefixWord ++ tailWord_7955418).sum := by decide
  have hdescent : baseEnd_7955418 < baseStart_7955418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955427 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7955427 : Nat := 118140960795 + 7955427 * 2 ^ 59
def prefixEnd_7955427 : Nat := 4983230072969 + 3 ^ 40 * 7955427 * 2
def baseEnd_7955427 : Nat := 4084957862755951088976163

theorem tailTrace_7955427 : CollatzResearch.WordTrace tailWord_7955427 prefixEnd_7955427 4084957862755951088976163 := by
  unfold tailWord_7955427
  simp only [CollatzResearch.WordTrace]
  refine ⟨290158260149854132606768535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193438840099902755071179023 290158260149854132606768535)
  ·
    refine ⟨435237390224781198910152803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290158260149854132606768535 435237390224781198910152803)
    ·
      refine ⟨652856085337171798365229205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435237390224781198910152803 652856085337171798365229205)
      ·
        refine ⟨30602629000179928048370119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 652856085337171798365229205 30602629000179928048370119)
        ·
          refine ⟨45903943500269892072555179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30602629000179928048370119 45903943500269892072555179)
          ·
            refine ⟨68855915250404838108832769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45903943500269892072555179 68855915250404838108832769)
            ·
              refine ⟨51641936437803628581624577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68855915250404838108832769 51641936437803628581624577)
              ·
                refine ⟨38731452328352721436218433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51641936437803628581624577 38731452328352721436218433)
                ·
                  refine ⟨29048589246264541077163825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38731452328352721436218433 29048589246264541077163825)
                  ·
                    refine ⟨21786441934698405807872869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29048589246264541077163825 21786441934698405807872869)
                    ·
                      refine ⟨4084957862755951088976163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21786441934698405807872869 4084957862755951088976163)
                      ·
                        rfl

theorem cell23_7955427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7955427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955427 prefixEnd_7955427 := by exact prefixLift 7955427
  have htrace : WordTrace (prefixWord ++ tailWord_7955427) baseStart_7955427 baseEnd_7955427 := by
    simpa [prefixWord, tailWord_7955427, baseEnd_7955427] using wordTrace_append hprefix tailTrace_7955427
  have hstable : (prefixWord ++ tailWord_7955427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955427).length < 2 ^ (prefixWord ++ tailWord_7955427).sum := by decide
  have hdescent : baseEnd_7955427 < baseStart_7955427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955440 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_7955440 : Nat := 118140960795 + 7955440 * 2 ^ 59
def prefixEnd_7955440 : Nat := 4983230072969 + 3 ^ 40 * 7955440 * 2
def baseEnd_7955440 : Nat := 4084964538004459538113603

theorem tailTrace_7955440 : CollatzResearch.WordTrace tailWord_7955440 prefixEnd_7955440 4084964538004459538113603 := by
  unfold tailWord_7955440
  simp only [CollatzResearch.WordTrace]
  refine ⟨145079367149403517913495887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193439156199204690551327849 145079367149403517913495887)
  ·
    refine ⟨217619050724105276870243831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145079367149403517913495887 217619050724105276870243831)
    ·
      refine ⟨326428576086157915305365747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217619050724105276870243831 326428576086157915305365747)
      ·
        refine ⟨489642864129236872958048621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326428576086157915305365747 489642864129236872958048621)
        ·
          refine ⟨183616074048463827359268233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489642864129236872958048621 183616074048463827359268233)
          ·
            refine ⟨137712055536347870519451175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183616074048463827359268233 137712055536347870519451175)
            ·
              refine ⟨206568083304521805779176763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137712055536347870519451175 206568083304521805779176763)
              ·
                refine ⟨309852124956782708668765145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206568083304521805779176763 309852124956782708668765145)
                ·
                  refine ⟨232389093717587031501573859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309852124956782708668765145 232389093717587031501573859)
                  ·
                    refine ⟨348583640576380547252360789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232389093717587031501573859 348583640576380547252360789)
                    ·
                      refine ⟨4084964538004459538113603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 348583640576380547252360789 4084964538004459538113603)
                      ·
                        rfl

theorem cell23_7955440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_7955440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955440 prefixEnd_7955440 := by exact prefixLift 7955440
  have htrace : WordTrace (prefixWord ++ tailWord_7955440) baseStart_7955440 baseEnd_7955440 := by
    simpa [prefixWord, tailWord_7955440, baseEnd_7955440] using wordTrace_append hprefix tailTrace_7955440
  have hstable : (prefixWord ++ tailWord_7955440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955440).length < 2 ^ (prefixWord ++ tailWord_7955440).sum := by decide
  have hdescent : baseEnd_7955440 < baseStart_7955440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955467 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 1, 7]
def baseStart_7955467 : Nat := 118140960795 + 7955467 * 2 ^ 59
def prefixEnd_7955467 : Nat := 4983230072969 + 3 ^ 40 * 7955467 * 2
def baseEnd_7955467 : Nat := 1361659467327376977491993

theorem tailTrace_7955467 : CollatzResearch.WordTrace tailWord_7955467 prefixEnd_7955467 1361659467327376977491993 := by
  unfold tailWord_7955467
  simp only [CollatzResearch.WordTrace]
  refine ⟨290159719069709219438224655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193439812713139479625483103 290159719069709219438224655)
  ·
    refine ⟨435239578604563829157336983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290159719069709219438224655 435239578604563829157336983)
    ·
      refine ⟨652859367906845743736005475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435239578604563829157336983 652859367906845743736005475)
      ·
        refine ⟨979289051860268615604008213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652859367906845743736005475 979289051860268615604008213)
        ·
          refine ⟨45904174305950091356437885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 979289051860268615604008213 45904174305950091356437885)
          ·
            refine ⟨17214065364731284258664207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45904174305950091356437885 17214065364731284258664207)
            ·
              refine ⟨25821098047096926387996311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17214065364731284258664207 25821098047096926387996311)
              ·
                refine ⟨38731647070645389581994467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25821098047096926387996311 38731647070645389581994467)
                ·
                  refine ⟨58097470605968084372991701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38731647070645389581994467 58097470605968084372991701)
                  ·
                    refine ⟨1361659467327376977491993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58097470605968084372991701 1361659467327376977491993)
                    ·
                      rfl

theorem cell23_7955467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 7].length) (baseStart_7955467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955467 prefixEnd_7955467 := by exact prefixLift 7955467
  have htrace : WordTrace (prefixWord ++ tailWord_7955467) baseStart_7955467 baseEnd_7955467 := by
    simpa [prefixWord, tailWord_7955467, baseEnd_7955467] using wordTrace_append hprefix tailTrace_7955467
  have hstable : (prefixWord ++ tailWord_7955467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955467).length < 2 ^ (prefixWord ++ tailWord_7955467).sum := by decide
  have hdescent : baseEnd_7955467 < baseStart_7955467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955504 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 2, 4, 2]
def baseStart_7955504 : Nat := 118140960795 + 7955504 * 2 ^ 59
def prefixEnd_7955504 : Nat := 4983230072969 + 3 ^ 40 * 7955504 * 2
def baseEnd_7955504 : Nat := 4084997400766347287713309

theorem tailTrace_7955504 : CollatzResearch.WordTrace tailWord_7955504 prefixEnd_7955504 4084997400766347287713309 := by
  unfold tailWord_7955504
  simp only [CollatzResearch.WordTrace]
  refine ⟨145080534285287587378660783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193440712380383449838214377 145080534285287587378660783)
  ·
    refine ⟨217620801427931381067991175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145080534285287587378660783 217620801427931381067991175)
    ·
      refine ⟨326431202141897071601986763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217620801427931381067991175 326431202141897071601986763)
      ·
        refine ⟨489646803212845607402980145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326431202141897071601986763 489646803212845607402980145)
        ·
          refine ⟨367235102409634205552235109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489646803212845607402980145 367235102409634205552235109)
          ·
            refine ⟨68856581701806413541044083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367235102409634205552235109 68856581701806413541044083)
            ·
              refine ⟨103284872552709620311566125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68856581701806413541044083 103284872552709620311566125)
              ·
                refine ⟨38731827207266107616837297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103284872552709620311566125 38731827207266107616837297)
                ·
                  refine ⟨29048870405449580712627973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38731827207266107616837297 29048870405449580712627973)
                  ·
                    refine ⟨5446663201021796383617745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29048870405449580712627973 5446663201021796383617745)
                    ·
                      refine ⟨4084997400766347287713309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446663201021796383617745 4084997400766347287713309)
                      ·
                        rfl

theorem cell23_7955504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 4, 2].length) (baseStart_7955504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955504 prefixEnd_7955504 := by exact prefixLift 7955504
  have htrace : WordTrace (prefixWord ++ tailWord_7955504) baseStart_7955504 baseEnd_7955504 := by
    simpa [prefixWord, tailWord_7955504, baseEnd_7955504] using wordTrace_append hprefix tailTrace_7955504
  have hstable : (prefixWord ++ tailWord_7955504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955504).length < 2 ^ (prefixWord ++ tailWord_7955504).sum := by decide
  have hdescent : baseEnd_7955504 < baseStart_7955504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955514 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_7955514 : Nat := 118140960795 + 7955514 * 2 ^ 59
def prefixEnd_7955514 : Nat := 4983230072969 + 3 ^ 40 * 7955514 * 2
def baseEnd_7955514 : Nat := 1361667511857630749529421

theorem tailTrace_7955514 : CollatzResearch.WordTrace tailWord_7955514 prefixEnd_7955514 1361667511857630749529421 := by
  unfold tailWord_7955514
  simp only [CollatzResearch.WordTrace]
  refine ⟨72540358325134736616296399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193440955533692630976790397 72540358325134736616296399)
  ·
    refine ⟨108810537487702104924444599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72540358325134736616296399 108810537487702104924444599)
    ·
      refine ⟨163215806231553157386666899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108810537487702104924444599 163215806231553157386666899)
      ·
        refine ⟨244823709347329736080000349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163215806231553157386666899 244823709347329736080000349)
        ·
          refine ⟨91808891005248651030000131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244823709347329736080000349 91808891005248651030000131)
          ·
            refine ⟨137713336507872976545000197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91808891005248651030000131 137713336507872976545000197)
            ·
              refine ⟨25821250595226183102187537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137713336507872976545000197 25821250595226183102187537)
              ·
                refine ⟨19365937946419637326640653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25821250595226183102187537 19365937946419637326640653)
                ·
                  refine ⟨7262226729907363997490245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19365937946419637326640653 7262226729907363997490245)
                  ·
                    refine ⟨1361667511857630749529421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7262226729907363997490245 1361667511857630749529421)
                    ·
                      rfl

theorem cell23_7955514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_7955514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955514 prefixEnd_7955514 := by exact prefixLift 7955514
  have htrace : WordTrace (prefixWord ++ tailWord_7955514) baseStart_7955514 baseEnd_7955514 := by
    simpa [prefixWord, tailWord_7955514, baseEnd_7955514] using wordTrace_append hprefix tailTrace_7955514
  have hstable : (prefixWord ++ tailWord_7955514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955514).length < 2 ^ (prefixWord ++ tailWord_7955514).sum := by decide
  have hdescent : baseEnd_7955514 < baseStart_7955514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955527 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 8]
def baseStart_7955527 : Nat := 118140960795 + 7955527 * 2 ^ 59
def prefixEnd_7955527 : Nat := 4983230072969 + 3 ^ 40 * 7955527 * 2
def baseEnd_7955527 : Nat := 453889912313488966413967

theorem tailTrace_7955527 : CollatzResearch.WordTrace tailWord_7955527 prefixEnd_7955527 453889912313488966413967 := by
  unfold tailWord_7955527
  simp only [CollatzResearch.WordTrace]
  refine ⟨290161907449491849685408835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193441271632994566456939223 290161907449491849685408835)
  ·
    refine ⟨435242861174237774528113253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290161907449491849685408835 435242861174237774528113253)
    ·
      refine ⟨81608036470169582724021235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435242861174237774528113253 81608036470169582724021235)
      ·
        refine ⟨122412054705254374086031853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81608036470169582724021235 122412054705254374086031853)
        ·
          refine ⟨45904520514470390282261945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122412054705254374086031853 45904520514470390282261945)
          ·
            refine ⟨34428390385852792711696459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45904520514470390282261945 34428390385852792711696459)
            ·
              refine ⟨51642585578779189067544689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34428390385852792711696459 51642585578779189067544689)
              ·
                refine ⟨38731939184084391800658517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51642585578779189067544689 38731939184084391800658517)
                ·
                  refine ⟨453889912313488966413967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38731939184084391800658517 453889912313488966413967)
                  ·
                    rfl

theorem cell23_7955527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 8].length) (baseStart_7955527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955527 prefixEnd_7955527 := by exact prefixLift 7955527
  have htrace : WordTrace (prefixWord ++ tailWord_7955527) baseStart_7955527 baseEnd_7955527 := by
    simpa [prefixWord, tailWord_7955527, baseEnd_7955527] using wordTrace_append hprefix tailTrace_7955527
  have hstable : (prefixWord ++ tailWord_7955527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955527).length < 2 ^ (prefixWord ++ tailWord_7955527).sum := by decide
  have hdescent : baseEnd_7955527 < baseStart_7955527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955561 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 6]
def baseStart_7955561 : Nat := 118140960795 + 7955561 * 2 ^ 59
def prefixEnd_7955561 : Nat := 4983230072969 + 3 ^ 40 * 7955561 * 2
def baseEnd_7955561 : Nat := 453891852129294840522283

theorem tailTrace_7955561 : CollatzResearch.WordTrace tailWord_7955561 prefixEnd_7955561 453891852129294840522283 := by
  unfold tailWord_7955561
  simp only [CollatzResearch.WordTrace]
  refine ⟨290163147531368673492146537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193442098354245782328097691 290163147531368673492146537)
  ·
    refine ⟨217622360648526505119109903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290163147531368673492146537 217622360648526505119109903)
    ·
      refine ⟨326433540972789757678664855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217622360648526505119109903 326433540972789757678664855)
      ·
        refine ⟨489650311459184636517997283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326433540972789757678664855 489650311459184636517997283)
        ·
          refine ⟨734475467188776954776995925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489650311459184636517997283 734475467188776954776995925)
          ·
            refine ⟨8607134381118479938792921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 734475467188776954776995925 8607134381118479938792921)
            ·
              refine ⟨6455350785838859954094691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8607134381118479938792921 6455350785838859954094691)
              ·
                refine ⟨9683026178758289931142037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6455350785838859954094691 9683026178758289931142037)
                ·
                  refine ⟨453891852129294840522283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9683026178758289931142037 453891852129294840522283)
                  ·
                    rfl

theorem cell23_7955561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 6].length) (baseStart_7955561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955561 prefixEnd_7955561 := by exact prefixLift 7955561
  have htrace : WordTrace (prefixWord ++ tailWord_7955561) baseStart_7955561 baseEnd_7955561 := by
    simpa [prefixWord, tailWord_7955561, baseEnd_7955561] using wordTrace_append hprefix tailTrace_7955561
  have hstable : (prefixWord ++ tailWord_7955561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955561).length < 2 ^ (prefixWord ++ tailWord_7955561).sum := by decide
  have hdescent : baseEnd_7955561 < baseStart_7955561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955598 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2]
def baseStart_7955598 : Nat := 118140960795 + 7955598 * 2 ^ 59
def prefixEnd_7955598 : Nat := 4983230072969 + 3 ^ 40 * 7955598 * 2
def baseEnd_7955598 : Nat := 4085045667947869919937877

theorem tailTrace_7955598 : CollatzResearch.WordTrace tailWord_7955598 prefixEnd_7955598 4085045667947869919937877 := by
  unfold tailWord_7955598
  simp only [CollatzResearch.WordTrace]
  refine ⟨36270562129029328601405431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193442998021489752540828965 36270562129029328601405431)
  ·
    refine ⟨54405843193543992902108147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36270562129029328601405431 54405843193543992902108147)
    ·
      refine ⟨81608764790315989353162221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54405843193543992902108147 81608764790315989353162221)
      ·
        refine ⟨30603286796368496007435833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81608764790315989353162221 30603286796368496007435833)
        ·
          refine ⟨22952465097276372005576875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30603286796368496007435833 22952465097276372005576875)
          ·
            refine ⟨34428697645914558008365313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22952465097276372005576875 34428697645914558008365313)
            ·
              refine ⟨25821523234435918506273985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34428697645914558008365313 25821523234435918506273985)
              ·
                refine ⟨19366142425826938879705489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25821523234435918506273985 19366142425826938879705489)
                ·
                  refine ⟨14524606819370204159779117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19366142425826938879705489 14524606819370204159779117)
                  ·
                    refine ⟨5446727557263826559917169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14524606819370204159779117 5446727557263826559917169)
                    ·
                      refine ⟨4085045667947869919937877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446727557263826559917169 4085045667947869919937877)
                      ·
                        rfl

theorem cell23_7955598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_7955598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955598 prefixEnd_7955598 := by exact prefixLift 7955598
  have htrace : WordTrace (prefixWord ++ tailWord_7955598) baseStart_7955598 baseEnd_7955598 := by
    simpa [prefixWord, tailWord_7955598, baseEnd_7955598] using wordTrace_append hprefix tailTrace_7955598
  have hstable : (prefixWord ++ tailWord_7955598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955598).length < 2 ^ (prefixWord ++ tailWord_7955598).sum := by decide
  have hdescent : baseEnd_7955598 < baseStart_7955598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955621 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_7955621 : Nat := 118140960795 + 7955621 * 2 ^ 59
def prefixEnd_7955621 : Nat := 4983230072969 + 3 ^ 40 * 7955621 * 2
def baseEnd_7955621 : Nat := 1361685826000974443316757

theorem tailTrace_7955621 : CollatzResearch.WordTrace tailWord_7955621 prefixEnd_7955621 1361685826000974443316757 := by
  unfold tailWord_7955621
  simp only [CollatzResearch.WordTrace]
  refine ⟨290165335911151303739330717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193443557274100869159553811 290165335911151303739330717)
  ·
    refine ⟨108812000966681738902249019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290165335911151303739330717 108812000966681738902249019)
    ·
      refine ⟨163218001450022608353373529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108812000966681738902249019 163218001450022608353373529)
      ·
        refine ⟨122413501087516956265030147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163218001450022608353373529 122413501087516956265030147)
        ·
          refine ⟨183620251631275434397545221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122413501087516956265030147 183620251631275434397545221)
          ·
            refine ⟨34428797180864143949539729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183620251631275434397545221 34428797180864143949539729)
            ·
              refine ⟨25821597885648107962154797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34428797180864143949539729 25821597885648107962154797)
              ·
                refine ⟨9683099207118040485808049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25821597885648107962154797 9683099207118040485808049)
                ·
                  refine ⟨7262324405338530364356037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9683099207118040485808049 7262324405338530364356037)
                  ·
                    refine ⟨1361685826000974443316757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7262324405338530364356037 1361685826000974443316757)
                    ·
                      rfl

theorem cell23_7955621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_7955621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955621 prefixEnd_7955621 := by exact prefixLift 7955621
  have htrace : WordTrace (prefixWord ++ tailWord_7955621) baseStart_7955621 baseEnd_7955621 := by
    simpa [prefixWord, tailWord_7955621, baseEnd_7955621] using wordTrace_append hprefix tailTrace_7955621
  have hstable : (prefixWord ++ tailWord_7955621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955621).length < 2 ^ (prefixWord ++ tailWord_7955621).sum := by decide
  have hdescent : baseEnd_7955621 < baseStart_7955621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955645 : List Nat := [1, 4, 1, 2, 1, 1, 3, 5, 1, 2, 2]
def baseStart_7955645 : Nat := 118140960795 + 7955645 * 2 ^ 59
def prefixEnd_7955645 : Nat := 4983230072969 + 3 ^ 40 * 7955645 * 2
def baseEnd_7955645 : Nat := 4085069801538631236050161

theorem tailTrace_7955645 : CollatzResearch.WordTrace tailWord_7955645 prefixEnd_7955645 4085069801538631236050161 := by
  unfold tailWord_7955645
  simp only [CollatzResearch.WordTrace]
  refine ⟨290166211263064355838204389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193444140842042903892136259 290166211263064355838204389)
  ·
    refine ⟨54406164611824566719663323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290166211263064355838204389 54406164611824566719663323)
    ·
      refine ⟨81609246917736850079494985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54406164611824566719663323 81609246917736850079494985)
      ·
        refine ⟨61206935188302637559621239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81609246917736850079494985 61206935188302637559621239)
        ·
          refine ⟨91810402782453956339431859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61206935188302637559621239 91810402782453956339431859)
          ·
            refine ⟨137715604173680934509147789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91810402782453956339431859 137715604173680934509147789)
            ·
              refine ⟨51643351565130350440930421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137715604173680934509147789 51643351565130350440930421)
              ·
                refine ⟨4841564209230970353837227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51643351565130350440930421 4841564209230970353837227)
                ·
                  refine ⟨7262346313846455530755841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841564209230970353837227 7262346313846455530755841)
                  ·
                    refine ⟨5446759735384841648066881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262346313846455530755841 5446759735384841648066881)
                    ·
                      refine ⟨4085069801538631236050161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446759735384841648066881 4085069801538631236050161)
                      ·
                        rfl

theorem cell23_7955645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_7955645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955645 prefixEnd_7955645 := by exact prefixLift 7955645
  have htrace : WordTrace (prefixWord ++ tailWord_7955645) baseStart_7955645 baseEnd_7955645 := by
    simpa [prefixWord, tailWord_7955645, baseEnd_7955645] using wordTrace_append hprefix tailTrace_7955645
  have hstable : (prefixWord ++ tailWord_7955645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955645).length < 2 ^ (prefixWord ++ tailWord_7955645).sum := by decide
  have hdescent : baseEnd_7955645 < baseStart_7955645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955648 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 3]
def baseStart_7955648 : Nat := 118140960795 + 7955648 * 2 ^ 59
def prefixEnd_7955648 : Nat := 4983230072969 + 3 ^ 40 * 7955648 * 2
def baseEnd_7955648 : Nat := 4085071341980594724312647

theorem tailTrace_7955648 : CollatzResearch.WordTrace tailWord_7955648 prefixEnd_7955648 4085071341980594724312647 := by
  unfold tailWord_7955648
  simp only [CollatzResearch.WordTrace]
  refine ⟨145083160341026743675281799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193444213788035658233709065 145083160341026743675281799)
  ·
    refine ⟨217624740511540115512922699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145083160341026743675281799 217624740511540115512922699)
    ·
      refine ⟨326437110767310173269384049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217624740511540115512922699 326437110767310173269384049)
      ·
        refine ⟨244827833075482629952038037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326437110767310173269384049 244827833075482629952038037)
        ·
          refine ⟨11476304675413248279001783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244827833075482629952038037 11476304675413248279001783)
          ·
            refine ⟨17214457013119872418502675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11476304675413248279001783 17214457013119872418502675)
            ·
              refine ⟨25821685519679808627754013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17214457013119872418502675 25821685519679808627754013)
              ·
                refine ⟨9683132069879928235407755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25821685519679808627754013 9683132069879928235407755)
                ·
                  refine ⟨14524698104819892353111633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9683132069879928235407755 14524698104819892353111633)
                  ·
                    refine ⟨10893523578614919264833725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14524698104819892353111633 10893523578614919264833725)
                    ·
                      refine ⟨4085071341980594724312647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10893523578614919264833725 4085071341980594724312647)
                      ·
                        rfl

theorem cell23_7955648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_7955648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955648 prefixEnd_7955648 := by exact prefixLift 7955648
  have htrace : WordTrace (prefixWord ++ tailWord_7955648) baseStart_7955648 baseEnd_7955648 := by
    simpa [prefixWord, tailWord_7955648, baseEnd_7955648] using wordTrace_append hprefix tailTrace_7955648
  have hstable : (prefixWord ++ tailWord_7955648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955648).length < 2 ^ (prefixWord ++ tailWord_7955648).sum := by decide
  have hdescent : baseEnd_7955648 < baseStart_7955648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955671 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 5, 3, 2]
def baseStart_7955671 : Nat := 118140960795 + 7955671 * 2 ^ 59
def prefixEnd_7955671 : Nat := 4983230072969 + 3 ^ 40 * 7955671 * 2
def baseEnd_7955671 : Nat := 4085083152035648134325041

theorem tailTrace_7955671 : CollatzResearch.WordTrace tailWord_7955671 prefixEnd_7955671 4085083152035648134325041 := by
  unfold tailWord_7955671
  simp only [CollatzResearch.WordTrace]
  refine ⟨290167159560970162278650867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193444773040646774852433911 290167159560970162278650867)
  ·
    refine ⟨435250739341455243417976301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290167159560970162278650867 435250739341455243417976301)
    ·
      refine ⟨163219027253045716281741113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435250739341455243417976301 163219027253045716281741113)
      ·
        refine ⟨122414270439784287211305835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163219027253045716281741113 122414270439784287211305835)
        ·
          refine ⟨183621405659676430816958753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122414270439784287211305835 183621405659676430816958753)
          ·
            refine ⟨137716054244757323112719065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183621405659676430816958753 137716054244757323112719065)
            ·
              refine ⟨103287040683567992334539299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137716054244757323112719065 103287040683567992334539299)
              ·
                refine ⟨154930561025351988501808949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103287040683567992334539299 154930561025351988501808949)
                ·
                  refine ⟨14524740096126748922044589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154930561025351988501808949 14524740096126748922044589)
                  ·
                    refine ⟨5446777536047530845766721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14524740096126748922044589 5446777536047530845766721)
                    ·
                      refine ⟨4085083152035648134325041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446777536047530845766721 4085083152035648134325041)
                      ·
                        rfl

theorem cell23_7955671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_7955671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955671 prefixEnd_7955671 := by exact prefixLift 7955671
  have htrace : WordTrace (prefixWord ++ tailWord_7955671) baseStart_7955671 baseEnd_7955671 := by
    simpa [prefixWord, tailWord_7955671, baseEnd_7955671] using wordTrace_append hprefix tailTrace_7955671
  have hstable : (prefixWord ++ tailWord_7955671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955671).length < 2 ^ (prefixWord ++ tailWord_7955671).sum := by decide
  have hdescent : baseEnd_7955671 < baseStart_7955671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955684 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_7955684 : Nat := 118140960795 + 7955684 * 2 ^ 59
def prefixEnd_7955684 : Nat := 4983230072969 + 3 ^ 40 * 7955684 * 2
def baseEnd_7955684 : Nat := 4085089827284156583462481

theorem tailTrace_7955684 : CollatzResearch.WordTrace tailWord_7955684 prefixEnd_7955684 4085089827284156583462481 := by
  unfold tailWord_7955684
  simp only [CollatzResearch.WordTrace]
  refine ⟨145083816854961532749437053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193445089139948710332582737 145083816854961532749437053)
  ·
    refine ⟨54406431320610574781038895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145083816854961532749437053 54406431320610574781038895)
    ·
      refine ⟨81609646980915862171558343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54406431320610574781038895 81609646980915862171558343)
      ·
        refine ⟨122414470471373793257337515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81609646980915862171558343 122414470471373793257337515)
        ·
          refine ⟨183621705707060689886006273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122414470471373793257337515 183621705707060689886006273)
          ·
            refine ⟨137716279280295517414504705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183621705707060689886006273 137716279280295517414504705)
            ·
              refine ⟨103287209460221638060878529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137716279280295517414504705 103287209460221638060878529)
              ·
                refine ⟨77465407095166228545658897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103287209460221638060878529 77465407095166228545658897)
                ·
                  refine ⟨58099055321374671409244173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77465407095166228545658897 58099055321374671409244173)
                  ·
                    refine ⟨21787145745515501778466565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58099055321374671409244173 21787145745515501778466565)
                    ·
                      refine ⟨4085089827284156583462481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21787145745515501778466565 4085089827284156583462481)
                      ·
                        rfl

theorem cell23_7955684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_7955684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955684 prefixEnd_7955684 := by exact prefixLift 7955684
  have htrace : WordTrace (prefixWord ++ tailWord_7955684) baseStart_7955684 baseEnd_7955684 := by
    simpa [prefixWord, tailWord_7955684, baseEnd_7955684] using wordTrace_append hprefix tailTrace_7955684
  have hstable : (prefixWord ++ tailWord_7955684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955684).length < 2 ^ (prefixWord ++ tailWord_7955684).sum := by decide
  have hdescent : baseEnd_7955684 < baseStart_7955684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955694 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_7955694 : Nat := 118140960795 + 7955694 * 2 ^ 59
def prefixEnd_7955694 : Nat := 4983230072969 + 3 ^ 40 * 7955694 * 2
def baseEnd_7955694 : Nat := 1361698320696900514779145

theorem tailTrace_7955694 : CollatzResearch.WordTrace tailWord_7955694 prefixEnd_7955694 1361698320696900514779145 := by
  unfold tailWord_7955694
  simp only [CollatzResearch.WordTrace]
  refine ⟨36270999804985854650842267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193445332293257891471158757 36270999804985854650842267)
  ·
    refine ⟨54406499707478781976263401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36270999804985854650842267 54406499707478781976263401)
    ·
      refine ⟨40804874780609086482197551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54406499707478781976263401 40804874780609086482197551)
      ·
        refine ⟨61207312170913629723296327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40804874780609086482197551 61207312170913629723296327)
        ·
          refine ⟨91810968256370444584944491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61207312170913629723296327 91810968256370444584944491)
          ·
            refine ⟨137716452384555666877416737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91810968256370444584944491 137716452384555666877416737)
            ·
              refine ⟨103287339288416750158062553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137716452384555666877416737 103287339288416750158062553)
              ·
                refine ⟨77465504466312562618546915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103287339288416750158062553 77465504466312562618546915)
                ·
                  refine ⟨116198256699468843927820373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77465504466312562618546915 116198256699468843927820373)
                  ·
                    refine ⟨1361698320696900514779145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116198256699468843927820373 1361698320696900514779145)
                    ·
                      rfl

theorem cell23_7955694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_7955694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955694 prefixEnd_7955694 := by exact prefixLift 7955694
  have htrace : WordTrace (prefixWord ++ tailWord_7955694) baseStart_7955694 baseEnd_7955694 := by
    simpa [prefixWord, tailWord_7955694, baseEnd_7955694] using wordTrace_append hprefix tailTrace_7955694
  have hstable : (prefixWord ++ tailWord_7955694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955694).length < 2 ^ (prefixWord ++ tailWord_7955694).sum := by decide
  have hdescent : baseEnd_7955694 < baseStart_7955694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955704 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 3, 6, 3]
def baseStart_7955704 : Nat := 118140960795 + 7955704 * 2 ^ 59
def prefixEnd_7955704 : Nat := 4983230072969 + 3 ^ 40 * 7955704 * 2
def baseEnd_7955704 : Nat := 4085100096897246505212389

theorem tailTrace_7955704 : CollatzResearch.WordTrace tailWord_7955704 prefixEnd_7955704 4085100096897246505212389 := by
  unfold tailWord_7955704
  simp only [CollatzResearch.WordTrace]
  refine ⟨145084181584925304457301083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193445575446567072609734777 145084181584925304457301083)
  ·
    refine ⟨217626272377387956685951625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145084181584925304457301083 217626272377387956685951625)
    ·
      refine ⟨163219704283040967514463719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217626272377387956685951625 163219704283040967514463719)
      ·
        refine ⟨244829556424561451271695579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163219704283040967514463719 244829556424561451271695579)
        ·
          refine ⟨367244334636842176907543369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244829556424561451271695579 367244334636842176907543369)
          ·
            refine ⟨275433250977631632680657527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367244334636842176907543369 275433250977631632680657527)
            ·
              refine ⟨413149876466447449020986291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275433250977631632680657527 413149876466447449020986291)
              ·
                refine ⟨619724814699671173531479437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413149876466447449020986291 619724814699671173531479437)
                ·
                  refine ⟨232396805512376690074304789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619724814699671173531479437 232396805512376690074304789)
                  ·
                    refine ⟨10893600258392657347233037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 232396805512376690074304789 10893600258392657347233037)
                    ·
                      refine ⟨4085100096897246505212389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10893600258392657347233037 4085100096897246505212389)
                      ·
                        rfl

theorem cell23_7955704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_7955704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955704 prefixEnd_7955704 := by exact prefixLift 7955704
  have htrace : WordTrace (prefixWord ++ tailWord_7955704) baseStart_7955704 baseEnd_7955704 := by
    simpa [prefixWord, tailWord_7955704, baseEnd_7955704] using wordTrace_append hprefix tailTrace_7955704
  have hstable : (prefixWord ++ tailWord_7955704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955704).length < 2 ^ (prefixWord ++ tailWord_7955704).sum := by decide
  have hdescent : baseEnd_7955704 < baseStart_7955704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955735 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 2, 2, 2]
def baseStart_7955735 : Nat := 118140960795 + 7955735 * 2 ^ 59
def prefixEnd_7955735 : Nat := 4983230072969 + 3 ^ 40 * 7955735 * 2
def baseEnd_7955735 : Nat := 4085116014797535883924747

theorem tailTrace_7955735 : CollatzResearch.WordTrace tailWord_7955735 prefixEnd_7955735 4085116014797535883924747 := by
  unfold tailWord_7955735
  simp only [CollatzResearch.WordTrace]
  refine ⟨290169493832738301208980659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193446329221825534139320439 290169493832738301208980659)
  ·
    refine ⟨435254240749107451813470989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290169493832738301208980659 435254240749107451813470989)
    ·
      refine ⟨163220340280915294430051621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435254240749107451813470989 163220340280915294430051621)
      ·
        refine ⟨30603813802671617705634679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163220340280915294430051621 30603813802671617705634679)
        ·
          refine ⟨45905720704007426558452019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30603813802671617705634679 45905720704007426558452019)
          ·
            refine ⟨68858581056011139837678029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45905720704007426558452019 68858581056011139837678029)
            ·
              refine ⟨25821967896004177439129261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68858581056011139837678029 25821967896004177439129261)
              ·
                refine ⟨9683237961001566539673473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25821967896004177439129261 9683237961001566539673473)
                ·
                  refine ⟨7262428470751174904755105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9683237961001566539673473 7262428470751174904755105)
                  ·
                    refine ⟨5446821353063381178566329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262428470751174904755105 5446821353063381178566329)
                    ·
                      refine ⟨4085116014797535883924747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446821353063381178566329 4085116014797535883924747)
                      ·
                        rfl

theorem cell23_7955735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_7955735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955735 prefixEnd_7955735 := by exact prefixLift 7955735
  have htrace : WordTrace (prefixWord ++ tailWord_7955735) baseStart_7955735 baseEnd_7955735 := by
    simpa [prefixWord, tailWord_7955735, baseEnd_7955735] using wordTrace_append hprefix tailTrace_7955735
  have hstable : (prefixWord ++ tailWord_7955735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955735).length < 2 ^ (prefixWord ++ tailWord_7955735).sum := by decide
  have hdescent : baseEnd_7955735 < baseStart_7955735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955775 : List Nat := [1, 1, 2, 2, 4, 4, 2, 2, 5]
def baseStart_7955775 : Nat := 118140960795 + 7955775 * 2 ^ 59
def prefixEnd_7955775 : Nat := 4983230072969 + 3 ^ 40 * 7955775 * 2
def baseEnd_7955775 : Nat := 453904061558190636380507

theorem tailTrace_7955775 : CollatzResearch.WordTrace tailWord_7955775 prefixEnd_7955775 453904061558190636380507 := by
  unfold tailWord_7955775
  simp only [CollatzResearch.WordTrace]
  refine ⟨290170952752593388040436779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193447301835062258693624519 290170952752593388040436779)
  ·
    refine ⟨435256429128890082060655169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290170952752593388040436779 435256429128890082060655169)
    ·
      refine ⟨326442321846667561545491377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435256429128890082060655169 326442321846667561545491377)
      ·
        refine ⟨244831741385000671159118533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326442321846667561545491377 244831741385000671159118533)
        ·
          refine ⟨45905951509687625842334725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244831741385000671159118533 45905951509687625842334725)
          ·
            refine ⟨8607365908066429845437761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45905951509687625842334725 8607365908066429845437761)
            ·
              refine ⟨6455524431049822384078321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8607365908066429845437761 6455524431049822384078321)
              ·
                refine ⟨4841643323287366788058741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6455524431049822384078321 4841643323287366788058741)
                ·
                  refine ⟨453904061558190636380507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4841643323287366788058741 453904061558190636380507)
                  ·
                    rfl

theorem cell23_7955775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 5].length) (baseStart_7955775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955775 prefixEnd_7955775 := by exact prefixLift 7955775
  have htrace : WordTrace (prefixWord ++ tailWord_7955775) baseStart_7955775 baseEnd_7955775 := by
    simpa [prefixWord, tailWord_7955775, baseEnd_7955775] using wordTrace_append hprefix tailTrace_7955775
  have hstable : (prefixWord ++ tailWord_7955775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955775).length < 2 ^ (prefixWord ++ tailWord_7955775).sum := by decide
  have hdescent : baseEnd_7955775 < baseStart_7955775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955782 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7955782 : Nat := 118140960795 + 7955782 * 2 ^ 59
def prefixEnd_7955782 : Nat := 4983230072969 + 3 ^ 40 * 7955782 * 2
def baseEnd_7955782 : Nat := 4085140148388297200037031

theorem tailTrace_7955782 : CollatzResearch.WordTrace tailWord_7955782 prefixEnd_7955782 4085140148388297200037031 := by
  unfold tailWord_7955782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9067850251986500882373175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193447472042378685490627733 9067850251986500882373175)
  ·
    refine ⟨13601775377979751323559763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9067850251986500882373175 13601775377979751323559763)
    ·
      refine ⟨20402663066969626985339645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13601775377979751323559763 20402663066969626985339645)
      ·
        refine ⟨7650998650113610119502367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20402663066969626985339645 7650998650113610119502367)
        ·
          refine ⟨11476497975170415179253551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7650998650113610119502367 11476497975170415179253551)
          ·
            refine ⟨17214746962755622768880327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11476497975170415179253551 17214746962755622768880327)
            ·
              refine ⟨25822120444133434153320491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17214746962755622768880327 25822120444133434153320491)
              ·
                refine ⟨38733180666200151229980737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25822120444133434153320491 38733180666200151229980737)
                ·
                  refine ⟨29049885499650113422485553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38733180666200151229980737 29049885499650113422485553)
                  ·
                    refine ⟨21787414124737585066864165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29049885499650113422485553 21787414124737585066864165)
                    ·
                      refine ⟨4085140148388297200037031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21787414124737585066864165 4085140148388297200037031)
                      ·
                        rfl

theorem cell23_7955782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7955782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955782 prefixEnd_7955782 := by exact prefixLift 7955782
  have htrace : WordTrace (prefixWord ++ tailWord_7955782) baseStart_7955782 baseEnd_7955782 := by
    simpa [prefixWord, tailWord_7955782, baseEnd_7955782] using wordTrace_append hprefix tailTrace_7955782
  have hstable : (prefixWord ++ tailWord_7955782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955782).length < 2 ^ (prefixWord ++ tailWord_7955782).sum := by decide
  have hdescent : baseEnd_7955782 < baseStart_7955782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955784 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 2, 8]
def baseStart_7955784 : Nat := 118140960795 + 7955784 * 2 ^ 59
def prefixEnd_7955784 : Nat := 4983230072969 + 3 ^ 40 * 7955784 * 2
def baseEnd_7955784 : Nat := 1361713725116535397404007

theorem tailTrace_7955784 : CollatzResearch.WordTrace tailWord_7955784 prefixEnd_7955784 1361713725116535397404007 := by
  unfold tailWord_7955784
  simp only [CollatzResearch.WordTrace]
  refine ⟨145085640504780391288757203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193447520673040521718342937 145085640504780391288757203)
  ·
    refine ⟨217628460757170586933135805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145085640504780391288757203 217628460757170586933135805)
    ·
      refine ⟨81610672783938970099925927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217628460757170586933135805 81610672783938970099925927)
      ·
        refine ⟨122416009175908455149888891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81610672783938970099925927 122416009175908455149888891)
        ·
          refine ⟨183624013763862682724833337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122416009175908455149888891 183624013763862682724833337)
          ·
            refine ⟨137718010322897012043625003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183624013763862682724833337 137718010322897012043625003)
            ·
              refine ⟨206577015484345518065437505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137718010322897012043625003 206577015484345518065437505)
              ·
                refine ⟨154932761613259138549078129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206577015484345518065437505 154932761613259138549078129)
                ·
                  refine ⟨116199571209944353911808597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154932761613259138549078129 116199571209944353911808597)
                  ·
                    refine ⟨1361713725116535397404007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116199571209944353911808597 1361713725116535397404007)
                    ·
                      rfl

theorem cell23_7955784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_7955784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955784 prefixEnd_7955784 := by exact prefixLift 7955784
  have htrace : WordTrace (prefixWord ++ tailWord_7955784) baseStart_7955784 baseEnd_7955784 := by
    simpa [prefixWord, tailWord_7955784, baseEnd_7955784] using wordTrace_append hprefix tailTrace_7955784
  have hstable : (prefixWord ++ tailWord_7955784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955784).length < 2 ^ (prefixWord ++ tailWord_7955784).sum := by decide
  have hdescent : baseEnd_7955784 < baseStart_7955784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955801 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 5, 4]
def baseStart_7955801 : Nat := 118140960795 + 7955801 * 2 ^ 59
def prefixEnd_7955801 : Nat := 4983230072969 + 3 ^ 40 * 7955801 * 2
def baseEnd_7955801 : Nat := 1361716634840244208566481

theorem tailTrace_7955801 : CollatzResearch.WordTrace tailWord_7955801 prefixEnd_7955801 1361716634840244208566481 := by
  unfold tailWord_7955801
  simp only [CollatzResearch.WordTrace]
  refine ⟨290171901050499194480883257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193447934033666129653922171 290171901050499194480883257)
  ·
    refine ⟨217628925787874395860662443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290171901050499194480883257 217628925787874395860662443)
    ·
      refine ⟨326443388681811593790993665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217628925787874395860662443 326443388681811593790993665)
      ·
        refine ⟨244832541511358695343245249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326443388681811593790993665 244832541511358695343245249)
        ·
          refine ⟨183624406133519021507433937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244832541511358695343245249 183624406133519021507433937)
          ·
            refine ⟨137718304600139266130575453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183624406133519021507433937 137718304600139266130575453)
            ·
              refine ⟨51644364225052224798965795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137718304600139266130575453 51644364225052224798965795)
              ·
                refine ⟨77466546337578337198448693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51644364225052224798965795 77466546337578337198448693)
                ·
                  refine ⟨7262488719147969112354565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77466546337578337198448693 7262488719147969112354565)
                  ·
                    refine ⟨1361716634840244208566481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7262488719147969112354565 1361716634840244208566481)
                    ·
                      rfl

theorem cell23_7955801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 4].length) (baseStart_7955801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955801 prefixEnd_7955801 := by exact prefixLift 7955801
  have htrace : WordTrace (prefixWord ++ tailWord_7955801) baseStart_7955801 baseEnd_7955801 := by
    simpa [prefixWord, tailWord_7955801, baseEnd_7955801] using wordTrace_append hprefix tailTrace_7955801
  have hstable : (prefixWord ++ tailWord_7955801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955801).length < 2 ^ (prefixWord ++ tailWord_7955801).sum := by decide
  have hdescent : baseEnd_7955801 < baseStart_7955801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955808 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 4]
def baseStart_7955808 : Nat := 118140960795 + 7955808 * 2 ^ 59
def prefixEnd_7955808 : Nat := 4983230072969 + 3 ^ 40 * 7955808 * 2
def baseEnd_7955808 : Nat := 4085153498885314098311911

theorem tailTrace_7955808 : CollatzResearch.WordTrace tailWord_7955808 prefixEnd_7955808 4085153498885314098311911 := by
  unfold tailWord_7955808
  simp only [CollatzResearch.WordTrace]
  refine ⟨145086078180736917338194039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193448104240982556450925385 145086078180736917338194039)
  ·
    refine ⟨217629117271105376007291059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145086078180736917338194039 217629117271105376007291059)
    ·
      refine ⟨326443675906658064010936589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217629117271105376007291059 326443675906658064010936589)
      ·
        refine ⟨122416378464996774004101221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326443675906658064010936589 122416378464996774004101221)
        ·
          refine ⟨22953070962186895125768979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122416378464996774004101221 22953070962186895125768979)
          ·
            refine ⟨34429606443280342688653469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22953070962186895125768979 34429606443280342688653469)
            ·
              refine ⟨12911102416230128508245051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34429606443280342688653469 12911102416230128508245051)
              ·
                refine ⟨19366653624345192762367577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12911102416230128508245051 19366653624345192762367577)
                ·
                  refine ⟨14524990218258894571775683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19366653624345192762367577 14524990218258894571775683)
                  ·
                    refine ⟨21787485327388341857663525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14524990218258894571775683 21787485327388341857663525)
                    ·
                      refine ⟨4085153498885314098311911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21787485327388341857663525 4085153498885314098311911)
                      ·
                        rfl

theorem cell23_7955808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_7955808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955808 prefixEnd_7955808 := by exact prefixLift 7955808
  have htrace : WordTrace (prefixWord ++ tailWord_7955808) baseStart_7955808 baseEnd_7955808 := by
    simpa [prefixWord, tailWord_7955808, baseEnd_7955808] using wordTrace_append hprefix tailTrace_7955808
  have hstable : (prefixWord ++ tailWord_7955808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955808).length < 2 ^ (prefixWord ++ tailWord_7955808).sum := by decide
  have hdescent : baseEnd_7955808 < baseStart_7955808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955821 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_7955821 : Nat := 118140960795 + 7955821 * 2 ^ 59
def prefixEnd_7955821 : Nat := 4983230072969 + 3 ^ 40 * 7955821 * 2
def baseEnd_7955821 : Nat := 4085160174133822547449351

theorem tailTrace_7955821 : CollatzResearch.WordTrace tailWord_7955821 prefixEnd_7955821 4085160174133822547449351 := by
  unfold tailWord_7955821
  simp only [CollatzResearch.WordTrace]
  refine ⟨290172630510426737896611317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193448420340284491931074211 290172630510426737896611317)
  ·
    refine ⟨27203684110352506677807311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 290172630510426737896611317 27203684110352506677807311)
    ·
      refine ⟨40805526165528760016710967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27203684110352506677807311 40805526165528760016710967)
      ·
        refine ⟨61208289248293140025066451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40805526165528760016710967 61208289248293140025066451)
        ·
          refine ⟨91812433872439710037599677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61208289248293140025066451 91812433872439710037599677)
          ·
            refine ⟨34429662702164891264099879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91812433872439710037599677 34429662702164891264099879)
            ·
              refine ⟨51644494053247336896149819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34429662702164891264099879 51644494053247336896149819)
              ·
                refine ⟨77466741079871005344224729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51644494053247336896149819 77466741079871005344224729)
                ·
                  refine ⟨58100055809903254008168547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77466741079871005344224729 58100055809903254008168547)
                  ·
                    refine ⟨87150083714854881012252821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58100055809903254008168547 87150083714854881012252821)
                    ·
                      refine ⟨4085160174133822547449351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87150083714854881012252821 4085160174133822547449351)
                      ·
                        rfl

theorem cell23_7955821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_7955821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955821 prefixEnd_7955821 := by exact prefixLift 7955821
  have htrace : WordTrace (prefixWord ++ tailWord_7955821) baseStart_7955821 baseEnd_7955821 := by
    simpa [prefixWord, tailWord_7955821, baseEnd_7955821] using wordTrace_append hprefix tailTrace_7955821
  have hstable : (prefixWord ++ tailWord_7955821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955821).length < 2 ^ (prefixWord ++ tailWord_7955821).sum := by decide
  have hdescent : baseEnd_7955821 < baseStart_7955821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955842 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_7955842 : Nat := 118140960795 + 7955842 * 2 ^ 59
def prefixEnd_7955842 : Nat := 4983230072969 + 3 ^ 40 * 7955842 * 2
def baseEnd_7955842 : Nat := 4085170957227566965286755

theorem tailTrace_7955842 : CollatzResearch.WordTrace tailWord_7955842 prefixEnd_7955842 4085170957227566965286755 := by
  unfold tailWord_7955842
  simp only [CollatzResearch.WordTrace]
  refine ⟨72543349110837664620781445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193448930962233772322083853 72543349110837664620781445)
  ·
    refine ⟨13601877958282062116396521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72543349110837664620781445 13601877958282062116396521)
    ·
      refine ⟨10201408468711546587297391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13601877958282062116396521 10201408468711546587297391)
      ·
        refine ⟨15302112703067319880946087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10201408468711546587297391 15302112703067319880946087)
        ·
          refine ⟨22953169054600979821419131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15302112703067319880946087 22953169054600979821419131)
          ·
            refine ⟨34429753581901469732128697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22953169054600979821419131 34429753581901469732128697)
            ·
              refine ⟨25822315186426102299096523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34429753581901469732128697 25822315186426102299096523)
              ·
                refine ⟨38733472779639153448644785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25822315186426102299096523 38733472779639153448644785)
                ·
                  refine ⟨29050104584729365086483589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38733472779639153448644785 29050104584729365086483589)
                  ·
                    refine ⟨5446894609636755953715673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29050104584729365086483589 5446894609636755953715673)
                    ·
                      refine ⟨4085170957227566965286755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446894609636755953715673 4085170957227566965286755)
                      ·
                        rfl

theorem cell23_7955842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_7955842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955842 prefixEnd_7955842 := by exact prefixLift 7955842
  have htrace : WordTrace (prefixWord ++ tailWord_7955842) baseStart_7955842 baseEnd_7955842 := by
    simpa [prefixWord, tailWord_7955842, baseEnd_7955842] using wordTrace_append hprefix tailTrace_7955842
  have hstable : (prefixWord ++ tailWord_7955842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955842).length < 2 ^ (prefixWord ++ tailWord_7955842).sum := by decide
  have hdescent : baseEnd_7955842 < baseStart_7955842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955861 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_7955861 : Nat := 118140960795 + 7955861 * 2 ^ 59
def prefixEnd_7955861 : Nat := 4983230072969 + 3 ^ 40 * 7955861 * 2
def baseEnd_7955861 : Nat := 1361726904453334130316389

theorem tailTrace_7955861 : CollatzResearch.WordTrace tailWord_7955861 prefixEnd_7955861 1361726904453334130316389 := by
  unfold tailWord_7955861
  simp only [CollatzResearch.WordTrace]
  refine ⟨290174089430281824728067437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193449392953521216485378291 290174089430281824728067437)
  ·
    refine ⟨108815283536355684273025289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290174089430281824728067437 108815283536355684273025289)
    ·
      refine ⟨81611462652266763204768967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108815283536355684273025289 81611462652266763204768967)
      ·
        refine ⟨122417193978400144807153451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81611462652266763204768967 122417193978400144807153451)
        ·
          refine ⟨183625790967600217210730177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122417193978400144807153451 183625790967600217210730177)
          ·
            refine ⟨137719343225700162908047633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183625790967600217210730177 137719343225700162908047633)
            ·
              refine ⟨103289507419275122181035725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137719343225700162908047633 103289507419275122181035725)
              ·
                refine ⟨38733565282228170817888397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103289507419275122181035725 38733565282228170817888397)
                ·
                  refine ⟨14525086980835564056708149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38733565282228170817888397 14525086980835564056708149)
                  ·
                    refine ⟨1361726904453334130316389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14525086980835564056708149 1361726904453334130316389)
                    ·
                      rfl

theorem cell23_7955861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_7955861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955861 prefixEnd_7955861 := by exact prefixLift 7955861
  have htrace : WordTrace (prefixWord ++ tailWord_7955861) baseStart_7955861 baseEnd_7955861 := by
    simpa [prefixWord, tailWord_7955861, baseEnd_7955861] using wordTrace_append hprefix tailTrace_7955861
  have hstable : (prefixWord ++ tailWord_7955861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955861).length < 2 ^ (prefixWord ++ tailWord_7955861).sum := by decide
  have hdescent : baseEnd_7955861 < baseStart_7955861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955881 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 4]
def baseStart_7955881 : Nat := 118140960795 + 7955881 * 2 ^ 59
def prefixEnd_7955881 : Nat := 4983230072969 + 3 ^ 40 * 7955881 * 2
def baseEnd_7955881 : Nat := 4085190982973092312699075

theorem tailTrace_7955881 : CollatzResearch.WordTrace tailWord_7955881 prefixEnd_7955881 4085190982973092312699075 := by
  unfold tailWord_7955881
  simp only [CollatzResearch.WordTrace]
  refine ⟨290174818890209368143795497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193449879260139578762530331 290174818890209368143795497)
  ·
    refine ⟨217631114167657026107846623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290174818890209368143795497 217631114167657026107846623)
    ·
      refine ⟨326446671251485539161769935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217631114167657026107846623 326446671251485539161769935)
      ·
        refine ⟨489670006877228308742654903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326446671251485539161769935 489670006877228308742654903)
        ·
          refine ⟨734505010315842463113982355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489670006877228308742654903 734505010315842463113982355)
          ·
            refine ⟨1101757515473763694670973533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734505010315842463113982355 1101757515473763694670973533)
            ·
              refine ⟨413159068302661385501615075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1101757515473763694670973533 413159068302661385501615075)
              ·
                refine ⟨619738602453992078252422613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413159068302661385501615075 619738602453992078252422613)
                ·
                  refine ⟨14525123495015439334041155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 619738602453992078252422613 14525123495015439334041155)
                  ·
                    refine ⟨21787685242523159001061733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14525123495015439334041155 21787685242523159001061733)
                    ·
                      refine ⟨4085190982973092312699075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21787685242523159001061733 4085190982973092312699075)
                      ·
                        rfl

theorem cell23_7955881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_7955881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955881 prefixEnd_7955881 := by exact prefixLift 7955881
  have htrace : WordTrace (prefixWord ++ tailWord_7955881) baseStart_7955881 baseEnd_7955881 := by
    simpa [prefixWord, tailWord_7955881, baseEnd_7955881] using wordTrace_append hprefix tailTrace_7955881
  have hstable : (prefixWord ++ tailWord_7955881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955881).length < 2 ^ (prefixWord ++ tailWord_7955881).sum := by decide
  have hdescent : baseEnd_7955881 < baseStart_7955881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955911 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_7955911 : Nat := 118140960795 + 7955911 * 2 ^ 59
def prefixEnd_7955911 : Nat := 4983230072969 + 3 ^ 40 * 7955911 * 2
def baseEnd_7955911 : Nat := 4085206387392727195323937

theorem tailTrace_7955911 : CollatzResearch.WordTrace tailWord_7955911 prefixEnd_7955911 4085206387392727195323937 := by
  unfold tailWord_7955911
  simp only [CollatzResearch.WordTrace]
  refine ⟨290175913080100683267387587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193450608720067122178258391 290175913080100683267387587)
  ·
    refine ⟨435263869620151024901081381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290175913080100683267387587 435263869620151024901081381)
    ·
      refine ⟨81611975553778317168952759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435263869620151024901081381 81611975553778317168952759)
      ·
        refine ⟨122417963330667475753429139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81611975553778317168952759 122417963330667475753429139)
        ·
          refine ⟨183626944996001213630143709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122417963330667475753429139 183626944996001213630143709)
          ·
            refine ⟨68860104373500455111303891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183626944996001213630143709 68860104373500455111303891)
            ·
              refine ⟨103290156560250682666955837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68860104373500455111303891 103290156560250682666955837)
              ·
                refine ⟨38733808710094006000108439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103290156560250682666955837 38733808710094006000108439)
                ·
                  refine ⟨58100713065141009000162659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38733808710094006000108439 58100713065141009000162659)
                  ·
                    refine ⟨87151069597711513500243989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58100713065141009000162659 87151069597711513500243989)
                    ·
                      refine ⟨4085206387392727195323937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87151069597711513500243989 4085206387392727195323937)
                      ·
                        rfl

theorem cell23_7955911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_7955911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955911 prefixEnd_7955911 := by exact prefixLift 7955911
  have htrace : WordTrace (prefixWord ++ tailWord_7955911) baseStart_7955911 baseEnd_7955911 := by
    simpa [prefixWord, tailWord_7955911, baseEnd_7955911] using wordTrace_append hprefix tailTrace_7955911
  have hstable : (prefixWord ++ tailWord_7955911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955911).length < 2 ^ (prefixWord ++ tailWord_7955911).sum := by decide
  have hdescent : baseEnd_7955911 < baseStart_7955911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955915 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 3, 2, 2]
def baseStart_7955915 : Nat := 118140960795 + 7955915 * 2 ^ 59
def prefixEnd_7955915 : Nat := 4983230072969 + 3 ^ 40 * 7955915 * 2
def baseEnd_7955915 : Nat := 4085208441315345179673919

theorem tailTrace_7955915 : CollatzResearch.WordTrace tailWord_7955915 prefixEnd_7955915 4085208441315345179673919 := by
  unfold tailWord_7955915
  simp only [CollatzResearch.WordTrace]
  refine ⟨290176058972086191950533199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193450705981390794633688799 290176058972086191950533199)
  ·
    refine ⟨435264088458129287925799799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290176058972086191950533199 435264088458129287925799799)
    ·
      refine ⟨652896132687193931888699699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435264088458129287925799799 652896132687193931888699699)
      ·
        refine ⟨979344199030790897833049549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652896132687193931888699699 979344199030790897833049549)
        ·
          refine ⟨367254074636546586687393581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 979344199030790897833049549 367254074636546586687393581)
          ·
            refine ⟨137720277988704970007772593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367254074636546586687393581 137720277988704970007772593)
            ·
              refine ⟨103290208491528727505829445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137720277988704970007772593 103290208491528727505829445)
              ·
                refine ⟨19366914092161636407343021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103290208491528727505829445 19366914092161636407343021)
                ·
                  refine ⟨7262592784560613652753633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19366914092161636407343021 7262592784560613652753633)
                  ·
                    refine ⟨5446944588420460239565225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262592784560613652753633 5446944588420460239565225)
                    ·
                      refine ⟨4085208441315345179673919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446944588420460239565225 4085208441315345179673919)
                      ·
                        rfl

theorem cell23_7955915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 2, 2].length) (baseStart_7955915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955915 prefixEnd_7955915 := by exact prefixLift 7955915
  have htrace : WordTrace (prefixWord ++ tailWord_7955915) baseStart_7955915 baseEnd_7955915 := by
    simpa [prefixWord, tailWord_7955915, baseEnd_7955915] using wordTrace_append hprefix tailTrace_7955915
  have hstable : (prefixWord ++ tailWord_7955915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955915).length < 2 ^ (prefixWord ++ tailWord_7955915).sum := by decide
  have hdescent : baseEnd_7955915 < baseStart_7955915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955951 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 2, 7]
def baseStart_7955951 : Nat := 118140960795 + 7955951 * 2 ^ 59
def prefixEnd_7955951 : Nat := 4983230072969 + 3 ^ 40 * 7955951 * 2
def baseEnd_7955951 : Nat := 1361742308872969012941251

theorem tailTrace_7955951 : CollatzResearch.WordTrace tailWord_7955951 prefixEnd_7955951 1361742308872969012941251 := by
  unfold tailWord_7955951
  simp only [CollatzResearch.WordTrace]
  refine ⟨290177371999955770098843707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193451581333303846732562471 290177371999955770098843707)
  ·
    refine ⟨435266057999933655148265561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290177371999955770098843707 435266057999933655148265561)
    ·
      refine ⟨326449543499950241361199171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435266057999933655148265561 326449543499950241361199171)
      ·
        refine ⟨489674315249925362041798757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326449543499950241361199171 489674315249925362041798757)
        ·
          refine ⟨91813934109361005382837267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489674315249925362041798757 91813934109361005382837267)
          ·
            refine ⟨137720901164041508074255901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91813934109361005382837267 137720901164041508074255901)
            ·
              refine ⟨51645337936515565527845963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137720901164041508074255901 51645337936515565527845963)
              ·
                refine ⟨77468006904773348291768945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51645337936515565527845963 77468006904773348291768945)
                ·
                  refine ⟨58101005178580011218826709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77468006904773348291768945 58101005178580011218826709)
                  ·
                    refine ⟨1361742308872969012941251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58101005178580011218826709 1361742308872969012941251)
                    ·
                      rfl

theorem cell23_7955951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_7955951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955951 prefixEnd_7955951 := by exact prefixLift 7955951
  have htrace : WordTrace (prefixWord ++ tailWord_7955951) baseStart_7955951 baseEnd_7955951 := by
    simpa [prefixWord, tailWord_7955951, baseEnd_7955951] using wordTrace_append hprefix tailTrace_7955951
  have hstable : (prefixWord ++ tailWord_7955951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955951).length < 2 ^ (prefixWord ++ tailWord_7955951).sum := by decide
  have hdescent : baseEnd_7955951 < baseStart_7955951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955961 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_7955961 : Nat := 118140960795 + 7955961 * 2 ^ 59
def prefixEnd_7955961 : Nat := 4983230072969 + 3 ^ 40 * 7955961 * 2
def baseEnd_7955961 : Nat := 4085232061425451999698707

theorem tailTrace_7955961 : CollatzResearch.WordTrace tailWord_7955961 prefixEnd_7955961 4085232061425451999698707 := by
  unfold tailWord_7955961
  simp only [CollatzResearch.WordTrace]
  refine ⟨290177736729919541806707737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193451824486613027871138491 290177736729919541806707737)
  ·
    refine ⟨217633302547439656355030803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290177736729919541806707737 217633302547439656355030803)
    ·
      refine ⟨326449953821159484532546205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217633302547439656355030803 326449953821159484532546205)
      ·
        refine ⟨122418732682934806699704827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326449953821159484532546205 122418732682934806699704827)
        ·
          refine ⟨183628099024402210049557241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122418732682934806699704827 183628099024402210049557241)
          ·
            refine ⟨137721074268301657537167931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183628099024402210049557241 137721074268301657537167931)
            ·
              refine ⟨206581611402452486305751897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137721074268301657537167931 206581611402452486305751897)
              ·
                refine ⟨154936208551839364729313923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206581611402452486305751897 154936208551839364729313923)
                ·
                  refine ⟨232404312827759047093970885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154936208551839364729313923 232404312827759047093970885)
                  ·
                    refine ⟨43575808655204821330119541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232404312827759047093970885 43575808655204821330119541)
                    ·
                      refine ⟨4085232061425451999698707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43575808655204821330119541 4085232061425451999698707)
                      ·
                        rfl

theorem cell23_7955961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_7955961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955961 prefixEnd_7955961 := by exact prefixLift 7955961
  have htrace : WordTrace (prefixWord ++ tailWord_7955961) baseStart_7955961 baseEnd_7955961 := by
    simpa [prefixWord, tailWord_7955961, baseEnd_7955961] using wordTrace_append hprefix tailTrace_7955961
  have hstable : (prefixWord ++ tailWord_7955961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955961).length < 2 ^ (prefixWord ++ tailWord_7955961).sum := by decide
  have hdescent : baseEnd_7955961 < baseStart_7955961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955965 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_7955965 : Nat := 118140960795 + 7955965 * 2 ^ 59
def prefixEnd_7955965 : Nat := 4983230072969 + 3 ^ 40 * 7955965 * 2
def baseEnd_7955965 : Nat := 4085234115348069984048689

theorem tailTrace_7955965 : CollatzResearch.WordTrace tailWord_7955965 prefixEnd_7955965 4085234115348069984048689 := by
  unfold tailWord_7955965
  simp only [CollatzResearch.WordTrace]
  refine ⟨290177882621905050489853349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193451921747936700326568899 290177882621905050489853349)
  ·
    refine ⟨54408352991607196966847503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290177882621905050489853349 54408352991607196966847503)
    ·
      refine ⟨81612529487410795450271255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54408352991607196966847503 81612529487410795450271255)
      ·
        refine ⟨122418794231116193175406883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81612529487410795450271255 122418794231116193175406883)
        ·
          refine ⟨183628191346674289763110325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122418794231116193175406883 183628191346674289763110325)
          ·
            refine ⟨17215142938750714665291593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183628191346674289763110325 17215142938750714665291593)
            ·
              refine ⟨12911357204063035998968695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17215142938750714665291593 12911357204063035998968695)
              ·
                refine ⟨19367035806094553998453043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12911357204063035998968695 19367035806094553998453043)
                ·
                  refine ⟨29050553709141830997679565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19367035806094553998453043 29050553709141830997679565)
                  ·
                    refine ⟨10893957640928186624129837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29050553709141830997679565 10893957640928186624129837)
                    ·
                      refine ⟨4085234115348069984048689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10893957640928186624129837 4085234115348069984048689)
                      ·
                        rfl

theorem cell23_7955965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_7955965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955965 prefixEnd_7955965 := by exact prefixLift 7955965
  have htrace : WordTrace (prefixWord ++ tailWord_7955965) baseStart_7955965 baseEnd_7955965 := by
    simpa [prefixWord, tailWord_7955965, baseEnd_7955965] using wordTrace_append hprefix tailTrace_7955965
  have hstable : (prefixWord ++ tailWord_7955965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955965).length < 2 ^ (prefixWord ++ tailWord_7955965).sum := by decide
  have hdescent : baseEnd_7955965 < baseStart_7955965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7955966 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7955966 : Nat := 118140960795 + 7955966 * 2 ^ 59
def prefixEnd_7955966 : Nat := 4983230072969 + 3 ^ 40 * 7955966 * 2
def baseEnd_7955966 : Nat := 4085234628828724480136185

theorem tailTrace_7955966 : CollatzResearch.WordTrace tailWord_7955966 prefixEnd_7955966 4085234628828724480136185 := by
  unfold tailWord_7955966
  simp only [CollatzResearch.WordTrace]
  refine ⟨36272239886862678457579969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193451946063267618440426501 36272239886862678457579969)
  ·
    refine ⟨27204179915147008843184977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36272239886862678457579969 27204179915147008843184977)
    ·
      refine ⟨20403134936360256632388733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27204179915147008843184977 20403134936360256632388733)
      ·
        refine ⟨7651175601135096237145775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20403134936360256632388733 7651175601135096237145775)
        ·
          refine ⟨11476763401702644355718663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7651175601135096237145775 11476763401702644355718663)
          ·
            refine ⟨17215145102553966533577995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11476763401702644355718663 17215145102553966533577995)
            ·
              refine ⟨25822717653830949800366993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17215145102553966533577995 25822717653830949800366993)
              ·
                refine ⟨19367038240373212350275245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25822717653830949800366993 19367038240373212350275245)
                ·
                  refine ⟨7262639340139954631353217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19367038240373212350275245 7262639340139954631353217)
                  ·
                    refine ⟨5446979505104965973514913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262639340139954631353217 5446979505104965973514913)
                    ·
                      refine ⟨4085234628828724480136185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5446979505104965973514913 4085234628828724480136185)
                      ·
                        rfl

theorem cell23_7955966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7955966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7955966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7955966 prefixEnd_7955966 := by exact prefixLift 7955966
  have htrace : WordTrace (prefixWord ++ tailWord_7955966) baseStart_7955966 baseEnd_7955966 := by
    simpa [prefixWord, tailWord_7955966, baseEnd_7955966] using wordTrace_append hprefix tailTrace_7955966
  have hstable : (prefixWord ++ tailWord_7955966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7955966).length < 2 ^ (prefixWord ++ tailWord_7955966).sum := by decide
  have hdescent : baseEnd_7955966 < baseStart_7955966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7955966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956065 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 2, 5, 2]
def baseStart_7956065 : Nat := 118140960795 + 7956065 * 2 ^ 59
def prefixEnd_7956065 : Nat := 4983230072969 + 3 ^ 40 * 7956065 * 2
def baseEnd_7956065 : Nat := 4085285463413519592798229

theorem tailTrace_7956065 : CollatzResearch.WordTrace tailWord_7956065 prefixEnd_7956065 4085285463413519592798229 := by
  unfold tailWord_7956065
  simp only [CollatzResearch.WordTrace]
  refine ⟨290181529921542767568493649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193454353281028511712329099 290181529921542767568493649)
  ·
    refine ⟨217636147441157075676370237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290181529921542767568493649 217636147441157075676370237)
    ·
      refine ⟨81613555290433903378638839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217636147441157075676370237 81613555290433903378638839)
      ·
        refine ⟨122420332935650855067958259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81613555290433903378638839 122420332935650855067958259)
        ·
          refine ⟨183630499403476282601937389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122420332935650855067958259 183630499403476282601937389)
          ·
            refine ⟨68861437276303605975726521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183630499403476282601937389 68861437276303605975726521)
            ·
              refine ⟨51646077957227704481794891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68861437276303605975726521 51646077957227704481794891)
              ·
                refine ⟨77469116935841556722692337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51646077957227704481794891 77469116935841556722692337)
                ·
                  refine ⟨58101837701881167542019253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77469116935841556722692337 58101837701881167542019253)
                  ·
                    refine ⟨5447047284551359457064305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58101837701881167542019253 5447047284551359457064305)
                    ·
                      refine ⟨4085285463413519592798229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5447047284551359457064305 4085285463413519592798229)
                      ·
                        rfl

theorem cell23_7956065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_7956065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956065 prefixEnd_7956065 := by exact prefixLift 7956065
  have htrace : WordTrace (prefixWord ++ tailWord_7956065) baseStart_7956065 baseEnd_7956065 := by
    simpa [prefixWord, tailWord_7956065, baseEnd_7956065] using wordTrace_append hprefix tailTrace_7956065
  have hstable : (prefixWord ++ tailWord_7956065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956065).length < 2 ^ (prefixWord ++ tailWord_7956065).sum := by decide
  have hdescent : baseEnd_7956065 < baseStart_7956065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956068 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_7956068 : Nat := 118140960795 + 7956068 * 2 ^ 59
def prefixEnd_7956068 : Nat := 4983230072969 + 3 ^ 40 * 7956068 * 2
def baseEnd_7956068 : Nat := 4085287003855483081060715

theorem tailTrace_7956068 : CollatzResearch.WordTrace tailWord_7956068 prefixEnd_7956068 4085287003855483081060715 := by
  unfold tailWord_7956068
  simp only [CollatzResearch.WordTrace]
  refine ⟨145090819670265949540426429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193454426227021266053901905 145090819670265949540426429)
  ·
    refine ⟨54409057376349731077659911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145090819670265949540426429 54409057376349731077659911)
    ·
      refine ⟨81613586064524596616489867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54409057376349731077659911 81613586064524596616489867)
      ·
        refine ⟨122420379096786894924734801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81613586064524596616489867 122420379096786894924734801)
        ·
          refine ⟨91815284322590171193551101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122420379096786894924734801 91815284322590171193551101)
          ·
            refine ⟨34430731620971314197581663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91815284322590171193551101 34430731620971314197581663)
            ·
              refine ⟨51646097431456971296372495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34430731620971314197581663 51646097431456971296372495)
              ·
                refine ⟨77469146147185456944558743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51646097431456971296372495 77469146147185456944558743)
                ·
                  refine ⟨116203719220778185416838115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77469146147185456944558743 116203719220778185416838115)
                  ·
                    refine ⟨174305578831167278125257173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116203719220778185416838115 174305578831167278125257173)
                    ·
                      refine ⟨4085287003855483081060715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174305578831167278125257173 4085287003855483081060715)
                      ·
                        rfl

theorem cell23_7956068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_7956068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956068 prefixEnd_7956068 := by exact prefixLift 7956068
  have htrace : WordTrace (prefixWord ++ tailWord_7956068) baseStart_7956068 baseEnd_7956068 := by
    simpa [prefixWord, tailWord_7956068, baseEnd_7956068] using wordTrace_append hprefix tailTrace_7956068
  have hstable : (prefixWord ++ tailWord_7956068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956068).length < 2 ^ (prefixWord ++ tailWord_7956068).sum := by decide
  have hdescent : baseEnd_7956068 < baseStart_7956068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956108 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_7956108 : Nat := 118140960795 + 7956108 * 2 ^ 59
def prefixEnd_7956108 : Nat := 4983230072969 + 3 ^ 40 * 7956108 * 2
def baseEnd_7956108 : Nat := 4085307543081662924560531

theorem tailTrace_7956108 : CollatzResearch.WordTrace tailWord_7956108 prefixEnd_7956108 4085307543081662924560531 := by
  unfold tailWord_7956108
  simp only [CollatzResearch.WordTrace]
  refine ⟨145091549130193492956154489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193455398840257990608205985 145091549130193492956154489)
  ·
    refine ⟨108818661847645119717115867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145091549130193492956154489 108818661847645119717115867)
    ·
      refine ⟨163227992771467679575673801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108818661847645119717115867 163227992771467679575673801)
      ·
        refine ⟨122420994578600759681755351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163227992771467679575673801 122420994578600759681755351)
        ·
          refine ⟨183631491867901139522633027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122420994578600759681755351 183631491867901139522633027)
          ·
            refine ⟨275447237801851709283949541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183631491867901139522633027 275447237801851709283949541)
            ·
              refine ⟨51646357087847195490740539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275447237801851709283949541 51646357087847195490740539)
              ·
                refine ⟨77469535631770793236110809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51646357087847195490740539 77469535631770793236110809)
                ·
                  refine ⟨58102151723828094927083107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77469535631770793236110809 58102151723828094927083107)
                  ·
                    refine ⟨87153227585742142390624661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58102151723828094927083107 87153227585742142390624661)
                    ·
                      refine ⟨4085307543081662924560531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87153227585742142390624661 4085307543081662924560531)
                      ·
                        rfl

theorem cell23_7956108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_7956108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956108 prefixEnd_7956108 := by exact prefixLift 7956108
  have htrace : WordTrace (prefixWord ++ tailWord_7956108) baseStart_7956108 baseEnd_7956108 := by
    simpa [prefixWord, tailWord_7956108, baseEnd_7956108] using wordTrace_append hprefix tailTrace_7956108
  have hstable : (prefixWord ++ tailWord_7956108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956108).length < 2 ^ (prefixWord ++ tailWord_7956108).sum := by decide
  have hdescent : baseEnd_7956108 < baseStart_7956108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956165 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_7956165 : Nat := 118140960795 + 7956165 * 2 ^ 59
def prefixEnd_7956165 : Nat := 4983230072969 + 3 ^ 40 * 7956165 * 2
def baseEnd_7956165 : Nat := 1361778937159656400515923

theorem tailTrace_7956165 : CollatzResearch.WordTrace tailWord_7956165 prefixEnd_7956165 1361778937159656400515923 := by
  unfold tailWord_7956165
  simp only [CollatzResearch.WordTrace]
  refine ⟨290185177221180484647133949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193456784814120323098089299 290185177221180484647133949)
  ·
    refine ⟨108819441457942681742675231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290185177221180484647133949 108819441457942681742675231)
    ·
      refine ⟨163229162186914022614012847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108819441457942681742675231 163229162186914022614012847)
      ·
        refine ⟨244843743280371033921019271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163229162186914022614012847 244843743280371033921019271)
        ·
          refine ⟨367265614920556550881528907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244843743280371033921019271 367265614920556550881528907)
          ·
            refine ⟨550898422380834826322293361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367265614920556550881528907 550898422380834826322293361)
            ·
              refine ⟨413173816785626119741720021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550898422380834826322293361 413173816785626119741720021)
              ·
                refine ⟨9683761330913112181446563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 413173816785626119741720021 9683761330913112181446563)
                ·
                  refine ⟨14525641996369668272169845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9683761330913112181446563 14525641996369668272169845)
                  ·
                    refine ⟨1361778937159656400515923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14525641996369668272169845 1361778937159656400515923)
                    ·
                      rfl

theorem cell23_7956165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_7956165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956165 prefixEnd_7956165 := by exact prefixLift 7956165
  have htrace : WordTrace (prefixWord ++ tailWord_7956165) baseStart_7956165 baseEnd_7956165 := by
    simpa [prefixWord, tailWord_7956165, baseEnd_7956165] using wordTrace_append hprefix tailTrace_7956165
  have hstable : (prefixWord ++ tailWord_7956165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956165).length < 2 ^ (prefixWord ++ tailWord_7956165).sum := by decide
  have hdescent : baseEnd_7956165 < baseStart_7956165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956202 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_7956202 : Nat := 118140960795 + 7956202 * 2 ^ 59
def prefixEnd_7956202 : Nat := 4983230072969 + 3 ^ 40 * 7956202 * 2
def baseEnd_7956202 : Nat := 4085355810263185556785099

theorem tailTrace_7956202 : CollatzResearch.WordTrace tailWord_7956202 prefixEnd_7956202 4085355810263185556785099 := by
  unfold tailWord_7956202
  simp only [CollatzResearch.WordTrace]
  refine ⟨72546631680511609991557715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193457684481364293310820573 72546631680511609991557715)
  ·
    refine ⟨108819947520767414987336573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72546631680511609991557715 108819947520767414987336573)
    ·
      refine ⟨40807480320287780620251215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108819947520767414987336573 40807480320287780620251215)
      ·
        refine ⟨61211220480431670930376823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40807480320287780620251215 61211220480431670930376823)
        ·
          refine ⟨91816830720647506395565235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61211220480431670930376823 91816830720647506395565235)
          ·
            refine ⟨137725246080971259593347853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91816830720647506395565235 137725246080971259593347853)
            ·
              refine ⟨51646967280364222347505445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137725246080971259593347853 51646967280364222347505445)
              ·
                refine ⟨9683806365068291690157271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51646967280364222347505445 9683806365068291690157271)
                ·
                  refine ⟨14525709547602437535235907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9683806365068291690157271 14525709547602437535235907)
                  ·
                    refine ⟨21788564321403656302853861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14525709547602437535235907 21788564321403656302853861)
                    ·
                      refine ⟨4085355810263185556785099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21788564321403656302853861 4085355810263185556785099)
                      ·
                        rfl

theorem cell23_7956202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_7956202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956202 prefixEnd_7956202 := by exact prefixLift 7956202
  have htrace : WordTrace (prefixWord ++ tailWord_7956202) baseStart_7956202 baseEnd_7956202 := by
    simpa [prefixWord, tailWord_7956202, baseEnd_7956202] using wordTrace_append hprefix tailTrace_7956202
  have hstable : (prefixWord ++ tailWord_7956202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956202).length < 2 ^ (prefixWord ++ tailWord_7956202).sum := by decide
  have hdescent : baseEnd_7956202 < baseStart_7956202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956215 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_7956215 : Nat := 118140960795 + 7956215 * 2 ^ 59
def prefixEnd_7956215 : Nat := 4983230072969 + 3 ^ 40 * 7956215 * 2
def baseEnd_7956215 : Nat := 4085362485511694005922539

theorem tailTrace_7956215 : CollatzResearch.WordTrace tailWord_7956215 prefixEnd_7956215 4085362485511694005922539 := by
  unfold tailWord_7956215
  simp only [CollatzResearch.WordTrace]
  refine ⟨290187000870999343186454099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193458000580666228790969399 290187000870999343186454099)
  ·
    refine ⟨435280501306499014779681149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290187000870999343186454099 435280501306499014779681149)
    ·
      refine ⟨163230187989937130542380431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435280501306499014779681149 163230187989937130542380431)
      ·
        refine ⟨244845281984905695813570647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163230187989937130542380431 244845281984905695813570647)
        ·
          refine ⟨367267922977358543720355971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244845281984905695813570647 367267922977358543720355971)
          ·
            refine ⟨550901884466037815580533957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367267922977358543720355971 550901884466037815580533957)
            ·
              refine ⟨103294103337382090421350117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 550901884466037815580533957 103294103337382090421350117)
              ·
                refine ⟨19367644375759141954003147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103294103337382090421350117 19367644375759141954003147)
                ·
                  refine ⟨29051466563638712931004721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19367644375759141954003147 29051466563638712931004721)
                  ·
                    refine ⟨21788599922729034698253541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29051466563638712931004721 21788599922729034698253541)
                    ·
                      refine ⟨4085362485511694005922539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21788599922729034698253541 4085362485511694005922539)
                      ·
                        rfl

theorem cell23_7956215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_7956215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956215 prefixEnd_7956215 := by exact prefixLift 7956215
  have htrace : WordTrace (prefixWord ++ tailWord_7956215) baseStart_7956215 baseEnd_7956215 := by
    simpa [prefixWord, tailWord_7956215, baseEnd_7956215] using wordTrace_append hprefix tailTrace_7956215
  have hstable : (prefixWord ++ tailWord_7956215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956215).length < 2 ^ (prefixWord ++ tailWord_7956215).sum := by decide
  have hdescent : baseEnd_7956215 < baseStart_7956215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956236 : List Nat := [2, 2, 1, 2, 2, 1, 2, 6, 1, 2, 2]
def baseStart_7956236 : Nat := 118140960795 + 7956236 * 2 ^ 59
def prefixEnd_7956236 : Nat := 4983230072969 + 3 ^ 40 * 7956236 * 2
def baseEnd_7956236 : Nat := 4085373268605438423759943

theorem tailTrace_7956236 : CollatzResearch.WordTrace tailWord_7956236 prefixEnd_7956236 4085373268605438423759943 := by
  unfold tailWord_7956236
  simp only [CollatzResearch.WordTrace]
  refine ⟨145093883401961631886484281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193458511202615509181979041 145093883401961631886484281)
  ·
    refine ⟨108820412551471223914863211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145093883401961631886484281 108820412551471223914863211)
    ·
      refine ⟨163230618827206835872294817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108820412551471223914863211 163230618827206835872294817)
      ·
        refine ⟨122422964120405126904221113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163230618827206835872294817 122422964120405126904221113)
        ·
          refine ⟨91817223090303845178165835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122422964120405126904221113 91817223090303845178165835)
          ·
            refine ⟨137725834635455767767248753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91817223090303845178165835 137725834635455767767248753)
            ·
              refine ⟨103294375976591825825436565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137725834635455767767248753 103294375976591825825436565)
              ·
                refine ⟨4841923873902741835567339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103294375976591825825436565 4841923873902741835567339)
                ·
                  refine ⟨7262885810854112753351009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841923873902741835567339 7262885810854112753351009)
                  ·
                    refine ⟨5447164358140584565013257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262885810854112753351009 5447164358140584565013257)
                    ·
                      refine ⟨4085373268605438423759943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5447164358140584565013257 4085373268605438423759943)
                      ·
                        rfl

theorem cell23_7956236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_7956236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956236 prefixEnd_7956236 := by exact prefixLift 7956236
  have htrace : WordTrace (prefixWord ++ tailWord_7956236) baseStart_7956236 baseEnd_7956236 := by
    simpa [prefixWord, tailWord_7956236, baseEnd_7956236] using wordTrace_append hprefix tailTrace_7956236
  have hstable : (prefixWord ++ tailWord_7956236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956236).length < 2 ^ (prefixWord ++ tailWord_7956236).sum := by decide
  have hdescent : baseEnd_7956236 < baseStart_7956236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956237 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 6]
def baseStart_7956237 : Nat := 118140960795 + 7956237 * 2 ^ 59
def prefixEnd_7956237 : Nat := 4983230072969 + 3 ^ 40 * 7956237 * 2
def baseEnd_7956237 : Nat := 453930420231788102205271

theorem tailTrace_7956237 : CollatzResearch.WordTrace tailWord_7956237 prefixEnd_7956237 453930420231788102205271 := by
  unfold tailWord_7956237
  simp only [CollatzResearch.WordTrace]
  refine ⟨290187803276919640943754965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193458535517946427295836643 290187803276919640943754965)
  ·
    refine ⟨6801276639302804084619257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 290187803276919640943754965 6801276639302804084619257)
    ·
      refine ⟨5100957479477103063464443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6801276639302804084619257 5100957479477103063464443)
      ·
        refine ⟨7651436219215654595196665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100957479477103063464443 7651436219215654595196665)
        ·
          refine ⟨5738577164411740946397499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7651436219215654595196665 5738577164411740946397499)
          ·
            refine ⟨8607865746617611419596249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5738577164411740946397499 8607865746617611419596249)
            ·
              refine ⟨6455899309963208564697187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8607865746617611419596249 6455899309963208564697187)
              ·
                refine ⟨9683848964944812847045781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6455899309963208564697187 9683848964944812847045781)
                ·
                  refine ⟨453930420231788102205271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9683848964944812847045781 453930420231788102205271)
                  ·
                    rfl

theorem cell23_7956237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_7956237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956237 prefixEnd_7956237 := by exact prefixLift 7956237
  have htrace : WordTrace (prefixWord ++ tailWord_7956237) baseStart_7956237 baseEnd_7956237 := by
    simpa [prefixWord, tailWord_7956237, baseEnd_7956237] using wordTrace_append hprefix tailTrace_7956237
  have hstable : (prefixWord ++ tailWord_7956237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956237).length < 2 ^ (prefixWord ++ tailWord_7956237).sum := by decide
  have hdescent : baseEnd_7956237 < baseStart_7956237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956242 : List Nat := [3, 2, 4, 1, 1, 1, 1, 10]
def baseStart_7956242 : Nat := 118140960795 + 7956242 * 2 ^ 59
def prefixEnd_7956242 : Nat := 4983230072969 + 3 ^ 40 * 7956242 * 2
def baseEnd_7956242 : Nat := 151310235166272792603145

theorem tailTrace_7956242 : CollatzResearch.WordTrace tailWord_7956242 prefixEnd_7956242 151310235166272792603145 := by
  unfold tailWord_7956242
  simp only [CollatzResearch.WordTrace]
  refine ⟨72546996410475381699421745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193458657094601017865124653 72546996410475381699421745)
  ·
    refine ⟨54410247307856536274566309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72546996410475381699421745 54410247307856536274566309)
    ·
      refine ⟨10201921370223100551481183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54410247307856536274566309 10201921370223100551481183)
      ·
        refine ⟨15302882055334650827221775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10201921370223100551481183 15302882055334650827221775)
        ·
          refine ⟨22954323083001976240832663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15302882055334650827221775 22954323083001976240832663)
          ·
            refine ⟨34431484624502964361248995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22954323083001976240832663 34431484624502964361248995)
            ·
              refine ⟨51647226936754446541873493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34431484624502964361248995 51647226936754446541873493)
              ·
                refine ⟨151310235166272792603145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51647226936754446541873493 151310235166272792603145)
                ·
                  rfl

theorem cell23_7956242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 10].length) (baseStart_7956242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956242 prefixEnd_7956242 := by exact prefixLift 7956242
  have htrace : WordTrace (prefixWord ++ tailWord_7956242) baseStart_7956242 baseEnd_7956242 := by
    simpa [prefixWord, tailWord_7956242, baseEnd_7956242] using wordTrace_append hprefix tailTrace_7956242
  have hstable : (prefixWord ++ tailWord_7956242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956242).length < 2 ^ (prefixWord ++ tailWord_7956242).sum := by decide
  have hdescent : baseEnd_7956242 < baseStart_7956242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956252 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_7956252 : Nat := 118140960795 + 7956252 * 2 ^ 59
def prefixEnd_7956252 : Nat := 4983230072969 + 3 ^ 40 * 7956252 * 2
def baseEnd_7956252 : Nat := 4085381484295910361159869

theorem tailTrace_7956252 : CollatzResearch.WordTrace tailWord_7956252 prefixEnd_7956252 4085381484295910361159869 := by
  unfold tailWord_7956252
  simp only [CollatzResearch.WordTrace]
  refine ⟨145094175185932649252775505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193458900247910199003700673 145094175185932649252775505)
  ·
    refine ⟨108820631389449486939581629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145094175185932649252775505 108820631389449486939581629)
    ·
      refine ⟨40807736771043557602343111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108820631389449486939581629 40807736771043557602343111)
      ·
        refine ⟨61211605156565336403514667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40807736771043557602343111 61211605156565336403514667)
        ·
          refine ⟨91817407734848004605272001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61211605156565336403514667 91817407734848004605272001)
          ·
            refine ⟨68863055801136003453954001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91817407734848004605272001 68863055801136003453954001)
            ·
              refine ⟨51647291850852002590465501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68863055801136003453954001 51647291850852002590465501)
              ·
                refine ⟨19367734444069500971424563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51647291850852002590465501 19367734444069500971424563)
                ·
                  refine ⟨29051601666104251457136845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19367734444069500971424563 29051601666104251457136845)
                  ·
                    refine ⟨10894350624789094296426317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29051601666104251457136845 10894350624789094296426317)
                    ·
                      refine ⟨4085381484295910361159869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10894350624789094296426317 4085381484295910361159869)
                      ·
                        rfl

theorem cell23_7956252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_7956252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956252 prefixEnd_7956252 := by exact prefixLift 7956252
  have htrace : WordTrace (prefixWord ++ tailWord_7956252) baseStart_7956252 baseEnd_7956252 := by
    simpa [prefixWord, tailWord_7956252, baseEnd_7956252] using wordTrace_append hprefix tailTrace_7956252
  have hstable : (prefixWord ++ tailWord_7956252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956252).length < 2 ^ (prefixWord ++ tailWord_7956252).sum := by decide
  have hdescent : baseEnd_7956252 < baseStart_7956252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956286 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_7956286 : Nat := 118140960795 + 7956286 * 2 ^ 59
def prefixEnd_7956286 : Nat := 4983230072969 + 3 ^ 40 * 7956286 * 2
def baseEnd_7956286 : Nat := 4085398942638163228134713

theorem tailTrace_7956286 : CollatzResearch.WordTrace tailWord_7956286 prefixEnd_7956286 4085398942638163228134713 := by
  unfold tailWord_7956286
  simp only [CollatzResearch.WordTrace]
  refine ⟨36273698806717765289036089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193459726969161414874859141 36273698806717765289036089)
  ·
    refine ⟨27205274105038323966777067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36273698806717765289036089 27205274105038323966777067)
    ·
      refine ⟨40807911157557485950165601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27205274105038323966777067 40807911157557485950165601)
      ·
        refine ⟨30605933368168114462624201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40807911157557485950165601 30605933368168114462624201)
        ·
          refine ⟨22954450026126085846968151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30605933368168114462624201 22954450026126085846968151)
          ·
            refine ⟨34431675039189128770452227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22954450026126085846968151 34431675039189128770452227)
            ·
              refine ⟨51647512558783693155678341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34431675039189128770452227 51647512558783693155678341)
              ·
                refine ⟨9683908604771942466689689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51647512558783693155678341 9683908604771942466689689)
                ·
                  refine ⟨7262931453578956850017267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9683908604771942466689689 7262931453578956850017267)
                  ·
                    refine ⟨10894397180368435275025901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7262931453578956850017267 10894397180368435275025901)
                    ·
                      refine ⟨4085398942638163228134713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10894397180368435275025901 4085398942638163228134713)
                      ·
                        rfl

theorem cell23_7956286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_7956286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956286 prefixEnd_7956286 := by exact prefixLift 7956286
  have htrace : WordTrace (prefixWord ++ tailWord_7956286) baseStart_7956286 baseEnd_7956286 := by
    simpa [prefixWord, tailWord_7956286, baseEnd_7956286] using wordTrace_append hprefix tailTrace_7956286
  have hstable : (prefixWord ++ tailWord_7956286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956286).length < 2 ^ (prefixWord ++ tailWord_7956286).sum := by decide
  have hdescent : baseEnd_7956286 < baseStart_7956286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956287 : List Nat := [1, 1, 2, 2, 7, 1, 2, 2, 1, 2, 2]
def baseStart_7956287 : Nat := 118140960795 + 7956287 * 2 ^ 59
def prefixEnd_7956287 : Nat := 4983230072969 + 3 ^ 40 * 7956287 * 2
def baseEnd_7956287 : Nat := 4085399456118817724222209

theorem tailTrace_7956287 : CollatzResearch.WordTrace tailWord_7956287 prefixEnd_7956287 4085399456118817724222209 := by
  unfold tailWord_7956287
  simp only [CollatzResearch.WordTrace]
  refine ⟨290189626926738499483075115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193459751284492332988716743 290189626926738499483075115)
  ·
    refine ⟨435284440390107749224612673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290189626926738499483075115 435284440390107749224612673)
    ·
      refine ⟨326463330292580811918459505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435284440390107749224612673 326463330292580811918459505)
      ·
        refine ⟨244847497719435608938844629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326463330292580811918459505 244847497719435608938844629)
        ·
          refine ⟨5738613227799272084504171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 244847497719435608938844629 5738613227799272084504171)
          ·
            refine ⟨8607919841698908126756257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5738613227799272084504171 8607919841698908126756257)
            ·
              refine ⟨6455939881274181095067193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8607919841698908126756257 6455939881274181095067193)
              ·
                refine ⟨4841954910955635821300395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6455939881274181095067193 4841954910955635821300395)
                ·
                  refine ⟨7262932366433453731950593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841954910955635821300395 7262932366433453731950593)
                  ·
                    refine ⟨5447199274825090298962945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262932366433453731950593 5447199274825090298962945)
                    ·
                      refine ⟨4085399456118817724222209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5447199274825090298962945 4085399456118817724222209)
                      ·
                        rfl

theorem cell23_7956287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 1, 2, 2].length) (baseStart_7956287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956287 prefixEnd_7956287 := by exact prefixLift 7956287
  have htrace : WordTrace (prefixWord ++ tailWord_7956287) baseStart_7956287 baseEnd_7956287 := by
    simpa [prefixWord, tailWord_7956287, baseEnd_7956287] using wordTrace_append hprefix tailTrace_7956287
  have hstable : (prefixWord ++ tailWord_7956287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956287).length < 2 ^ (prefixWord ++ tailWord_7956287).sum := by decide
  have hdescent : baseEnd_7956287 < baseStart_7956287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956295 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_7956295 : Nat := 118140960795 + 7956295 * 2 ^ 59
def prefixEnd_7956295 : Nat := 4983230072969 + 3 ^ 40 * 7956295 * 2
def baseEnd_7956295 : Nat := 4085403563964053692922171

theorem tailTrace_7956295 : CollatzResearch.WordTrace tailWord_7956295 prefixEnd_7956295 4085403563964053692922171 := by
  unfold tailWord_7956295
  simp only [CollatzResearch.WordTrace]
  refine ⟨290189918710709516849366339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193459945807139677899577559 290189918710709516849366339)
  ·
    refine ⟨435284878066064275274049509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290189918710709516849366339 435284878066064275274049509)
    ·
      refine ⟨81615914637387051613884283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435284878066064275274049509 81615914637387051613884283)
      ·
        refine ⟨122423871956080577420826425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81615914637387051613884283 122423871956080577420826425)
        ·
          refine ⟨91817903967060433065619819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122423871956080577420826425 91817903967060433065619819)
          ·
            refine ⟨137726855950590649598429729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91817903967060433065619819 137726855950590649598429729)
            ·
              refine ⟨103295141962942987198822297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137726855950590649598429729 103295141962942987198822297)
              ·
                refine ⟨77471356472207240399116723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103295141962942987198822297 77471356472207240399116723)
                ·
                  refine ⟨116207034708310860598675085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77471356472207240399116723 116207034708310860598675085)
                  ·
                    refine ⟨43577638015616572724503157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116207034708310860598675085 43577638015616572724503157)
                    ·
                      refine ⟨4085403563964053692922171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43577638015616572724503157 4085403563964053692922171)
                      ·
                        rfl

theorem cell23_7956295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_7956295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956295 prefixEnd_7956295 := by exact prefixLift 7956295
  have htrace : WordTrace (prefixWord ++ tailWord_7956295) baseStart_7956295 baseEnd_7956295 := by
    simpa [prefixWord, tailWord_7956295, baseEnd_7956295] using wordTrace_append hprefix tailTrace_7956295
  have hstable : (prefixWord ++ tailWord_7956295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956295).length < 2 ^ (prefixWord ++ tailWord_7956295).sum := by decide
  have hdescent : baseEnd_7956295 < baseStart_7956295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956309 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 1, 4, 2]
def baseStart_7956309 : Nat := 118140960795 + 7956309 * 2 ^ 59
def prefixEnd_7956309 : Nat := 4983230072969 + 3 ^ 40 * 7956309 * 2
def baseEnd_7956309 : Nat := 4085410752693216638147107

theorem tailTrace_7956309 : CollatzResearch.WordTrace tailWord_7956309 prefixEnd_7956309 4085410752693216638147107 := by
  unfold tailWord_7956309
  simp only [CollatzResearch.WordTrace]
  refine ⟨290190429332658797240375981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193460286221772531493583987 290190429332658797240375981)
  ·
    refine ⟨108821410999747048965140993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290190429332658797240375981 108821410999747048965140993)
    ·
      refine ⟨81616058249810286723855745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108821410999747048965140993 81616058249810286723855745)
      ·
        refine ⟨61212043687357715042891809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81616058249810286723855745 61212043687357715042891809)
        ·
          refine ⟨45909032765518286282168857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61212043687357715042891809 45909032765518286282168857)
          ·
            refine ⟨34431774574138714711626643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45909032765518286282168857 34431774574138714711626643)
            ·
              refine ⟨51647661861208072067439965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34431774574138714711626643 51647661861208072067439965)
              ·
                refine ⟨19367873197953027025289987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51647661861208072067439965 19367873197953027025289987)
                ·
                  refine ⟨29051809796929540537934981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19367873197953027025289987 29051809796929540537934981)
                  ·
                    refine ⟨5447214336924288850862809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29051809796929540537934981 5447214336924288850862809)
                    ·
                      refine ⟨4085410752693216638147107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5447214336924288850862809 4085410752693216638147107)
                      ·
                        rfl

theorem cell23_7956309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_7956309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956309 prefixEnd_7956309 := by exact prefixLift 7956309
  have htrace : WordTrace (prefixWord ++ tailWord_7956309) baseStart_7956309 baseEnd_7956309 := by
    simpa [prefixWord, tailWord_7956309, baseEnd_7956309] using wordTrace_append hprefix tailTrace_7956309
  have hstable : (prefixWord ++ tailWord_7956309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956309).length < 2 ^ (prefixWord ++ tailWord_7956309).sum := by decide
  have hdescent : baseEnd_7956309 < baseStart_7956309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956325 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_7956325 : Nat := 118140960795 + 7956325 * 2 ^ 59
def prefixEnd_7956325 : Nat := 4983230072969 + 3 ^ 40 * 7956325 * 2
def baseEnd_7956325 : Nat := 4085418968383688575547033

theorem tailTrace_7956325 : CollatzResearch.WordTrace tailWord_7956325 prefixEnd_7956325 4085418968383688575547033 := by
  unfold tailWord_7956325
  simp only [CollatzResearch.WordTrace]
  refine ⟨290191012900600831972958429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193460675267067221315305619 290191012900600831972958429)
  ·
    refine ⟨108821629837725311989859411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290191012900600831972958429 108821629837725311989859411)
    ·
      refine ⟨163232444756587967984789117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108821629837725311989859411 163232444756587967984789117)
      ·
        refine ⟨61212166783720487994295919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163232444756587967984789117 61212166783720487994295919)
        ·
          refine ⟨91818250175580731991443879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61212166783720487994295919 91818250175580731991443879)
          ·
            refine ⟨137727375263371097987165819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91818250175580731991443879 137727375263371097987165819)
            ·
              refine ⟨206591062895056646980748729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137727375263371097987165819 206591062895056646980748729)
              ·
                refine ⟨154943297171292485235561547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206591062895056646980748729 154943297171292485235561547)
                ·
                  refine ⟨232414945756938727853342321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154943297171292485235561547 232414945756938727853342321)
                  ·
                    refine ⟨174311209317704045890006741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 232414945756938727853342321 174311209317704045890006741)
                    ·
                      refine ⟨4085418968383688575547033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174311209317704045890006741 4085418968383688575547033)
                      ·
                        rfl

theorem cell23_7956325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_7956325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956325 prefixEnd_7956325 := by exact prefixLift 7956325
  have htrace : WordTrace (prefixWord ++ tailWord_7956325) baseStart_7956325 baseEnd_7956325 := by
    simpa [prefixWord, tailWord_7956325, baseEnd_7956325] using wordTrace_append hprefix tailTrace_7956325
  have hstable : (prefixWord ++ tailWord_7956325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956325).length < 2 ^ (prefixWord ++ tailWord_7956325).sum := by decide
  have hdescent : baseEnd_7956325 < baseStart_7956325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956360 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 2, 2, 2]
def baseStart_7956360 : Nat := 118140960795 + 7956360 * 2 ^ 59
def prefixEnd_7956360 : Nat := 4983230072969 + 3 ^ 40 * 7956360 * 2
def baseEnd_7956360 : Nat := 4085436940206595938609373

theorem tailTrace_7956360 : CollatzResearch.WordTrace tailWord_7956360 prefixEnd_7956360 4085436940206595938609373 := by
  unfold tailWord_7956360
  simp only [CollatzResearch.WordTrace]
  refine ⟨145096144727737016475241267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193461526303649355300321689 145096144727737016475241267)
  ·
    refine ⟨217644217091605524712861901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145096144727737016475241267 217644217091605524712861901)
    ·
      refine ⟨81616581409352071767323213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217644217091605524712861901 81616581409352071767323213)
      ·
        refine ⟨30606218028507026912746205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81616581409352071767323213 30606218028507026912746205)
        ·
          refine ⟨11477331760690135092279827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30606218028507026912746205 11477331760690135092279827)
          ·
            refine ⟨17215997641035202638419741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11477331760690135092279827 17215997641035202638419741)
            ·
              refine ⟨6455999115388200989407403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17215997641035202638419741 6455999115388200989407403)
              ·
                refine ⟨9683998673082301484111105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6455999115388200989407403 9683998673082301484111105)
                ·
                  refine ⟨7262999004811726113083329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9683998673082301484111105 7262999004811726113083329)
                  ·
                    refine ⟨5447249253608794584812497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7262999004811726113083329 5447249253608794584812497)
                    ·
                      refine ⟨4085436940206595938609373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5447249253608794584812497 4085436940206595938609373)
                      ·
                        rfl

theorem cell23_7956360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_7956360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956360 prefixEnd_7956360 := by exact prefixLift 7956360
  have htrace : WordTrace (prefixWord ++ tailWord_7956360) baseStart_7956360 baseEnd_7956360 := by
    simpa [prefixWord, tailWord_7956360, baseEnd_7956360] using wordTrace_append hprefix tailTrace_7956360
  have hstable : (prefixWord ++ tailWord_7956360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956360).length < 2 ^ (prefixWord ++ tailWord_7956360).sum := by decide
  have hdescent : baseEnd_7956360 < baseStart_7956360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956383 : List Nat := [1, 1, 2, 5, 4, 1, 1, 3, 5]
def baseStart_7956383 : Nat := 118140960795 + 7956383 * 2 ^ 59
def prefixEnd_7956383 : Nat := 4983230072969 + 3 ^ 40 * 7956383 * 2
def baseEnd_7956383 : Nat := 453938750029072149846863

theorem tailTrace_7956383 : CollatzResearch.WordTrace tailWord_7956383 prefixEnd_7956383 453938750029072149846863 := by
  unfold tailWord_7956383
  simp only [CollatzResearch.WordTrace]
  refine ⟨290193128334390707878569803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193462085556260471919046535 290193128334390707878569803)
  ·
    refine ⟨435289692501586061817854705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290193128334390707878569803 435289692501586061817854705)
    ·
      refine ⟨326467269376189546363391029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435289692501586061817854705 326467269376189546363391029)
      ·
        refine ⟨30606306504017769971567909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326467269376189546363391029 30606306504017769971567909)
        ·
          refine ⟨5738682469503331869668983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30606306504017769971567909 5738682469503331869668983)
          ·
            refine ⟨8608023704254997804503475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5738682469503331869668983 8608023704254997804503475)
            ·
              refine ⟨12912035556382496706755213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8608023704254997804503475 12912035556382496706755213)
              ·
                refine ⟨4842013333643436265033205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12912035556382496706755213 4842013333643436265033205)
                ·
                  refine ⟨453938750029072149846863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4842013333643436265033205 453938750029072149846863)
                  ·
                    rfl

theorem cell23_7956383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 5].length) (baseStart_7956383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956383 prefixEnd_7956383 := by exact prefixLift 7956383
  have htrace : WordTrace (prefixWord ++ tailWord_7956383) baseStart_7956383 baseEnd_7956383 := by
    simpa [prefixWord, tailWord_7956383, baseEnd_7956383] using wordTrace_append hprefix tailTrace_7956383
  have hstable : (prefixWord ++ tailWord_7956383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956383).length < 2 ^ (prefixWord ++ tailWord_7956383).sum := by decide
  have hdescent : baseEnd_7956383 < baseStart_7956383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956432 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 3]
def baseStart_7956432 : Nat := 118140960795 + 7956432 * 2 ^ 59
def prefixEnd_7956432 : Nat := 4983230072969 + 3 ^ 40 * 7956432 * 2
def baseEnd_7956432 : Nat := 4085473910813719656909041

theorem tailTrace_7956432 : CollatzResearch.WordTrace tailWord_7956432 prefixEnd_7956432 4085473910813719656909041 := by
  unfold tailWord_7956432
  simp only [CollatzResearch.WordTrace]
  refine ⟨145097457755606594623551775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193463277007475459498069033 145097457755606594623551775)
  ·
    refine ⟨217646186633409891935327663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145097457755606594623551775 217646186633409891935327663)
    ·
      refine ⟨326469279950114837902991495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217646186633409891935327663 326469279950114837902991495)
      ·
        refine ⟨489703919925172256854487243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326469279950114837902991495 489703919925172256854487243)
        ·
          refine ⟨734555879887758385281730865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489703919925172256854487243 734555879887758385281730865)
          ·
            refine ⟨550916909915818788961298149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734555879887758385281730865 550916909915818788961298149)
            ·
              refine ⟨103296920609216022930243403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 550916909915818788961298149 103296920609216022930243403)
              ·
                refine ⟨154945380913824034395365105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103296920609216022930243403 154945380913824034395365105)
                ·
                  refine ⟨116209035685368025796523829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154945380913824034395365105 116209035685368025796523829)
                  ·
                    refine ⟨10894597095503252418424109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116209035685368025796523829 10894597095503252418424109)
                    ·
                      refine ⟨4085473910813719656909041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10894597095503252418424109 4085473910813719656909041)
                      ·
                        rfl

theorem cell23_7956432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 3].length) (baseStart_7956432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956432 prefixEnd_7956432 := by exact prefixLift 7956432
  have htrace : WordTrace (prefixWord ++ tailWord_7956432) baseStart_7956432 baseEnd_7956432 := by
    simpa [prefixWord, tailWord_7956432, baseEnd_7956432] using wordTrace_append hprefix tailTrace_7956432
  have hstable : (prefixWord ++ tailWord_7956432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956432).length < 2 ^ (prefixWord ++ tailWord_7956432).sum := by decide
  have hdescent : baseEnd_7956432 < baseStart_7956432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956436 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_7956436 : Nat := 118140960795 + 7956436 * 2 ^ 59
def prefixEnd_7956436 : Nat := 4983230072969 + 3 ^ 40 * 7956436 * 2
def baseEnd_7956436 : Nat := 4085475964736337641259023

theorem tailTrace_7956436 : CollatzResearch.WordTrace tailWord_7956436 prefixEnd_7956436 4085475964736337641259023 := by
  unfold tailWord_7956436
  simp only [CollatzResearch.WordTrace]
  refine ⟨145097530701599348965124581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193463374268799131953499441 145097530701599348965124581)
  ·
    refine ⟨27205787006549877930960859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145097530701599348965124581 27205787006549877930960859)
    ·
      refine ⟨40808680509824816896441289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27205787006549877930960859 40808680509824816896441289)
      ·
        refine ⟨30606510382368612672330967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40808680509824816896441289 30606510382368612672330967)
        ·
          refine ⟨45909765573552919008496451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30606510382368612672330967 45909765573552919008496451)
          ·
            refine ⟨68864648360329378512744677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45909765573552919008496451 68864648360329378512744677)
            ·
              refine ⟨12912121567561758471139627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68864648360329378512744677 12912121567561758471139627)
              ·
                refine ⟨19368182351342637706709441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12912121567561758471139627 19368182351342637706709441)
                ·
                  refine ⟨14526136763506978280032081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19368182351342637706709441 14526136763506978280032081)
                  ·
                    refine ⟨10894602572630233710024061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14526136763506978280032081 10894602572630233710024061)
                    ·
                      refine ⟨4085475964736337641259023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10894602572630233710024061 4085475964736337641259023)
                      ·
                        rfl

theorem cell23_7956436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_7956436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956436 prefixEnd_7956436 := by exact prefixLift 7956436
  have htrace : WordTrace (prefixWord ++ tailWord_7956436) baseStart_7956436 baseEnd_7956436 := by
    simpa [prefixWord, tailWord_7956436, baseEnd_7956436] using wordTrace_append hprefix tailTrace_7956436
  have hstable : (prefixWord ++ tailWord_7956436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956436).length < 2 ^ (prefixWord ++ tailWord_7956436).sum := by decide
  have hdescent : baseEnd_7956436 < baseStart_7956436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956506 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4]
def baseStart_7956506 : Nat := 118140960795 + 7956506 * 2 ^ 59
def prefixEnd_7956506 : Nat := 4983230072969 + 3 ^ 40 * 7956506 * 2
def baseEnd_7956506 : Nat := 4085511908382152367383701

theorem tailTrace_7956506 : CollatzResearch.WordTrace tailWord_7956506 prefixEnd_7956506 4085511908382152367383701 := by
  unfold tailWord_7956506
  simp only [CollatzResearch.WordTrace]
  refine ⟨72549403628236274971324343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193465076341963399923531581 72549403628236274971324343)
  ·
    refine ⟨108824105442354412456986515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72549403628236274971324343 108824105442354412456986515)
    ·
      refine ⟨163236158163531618685479773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108824105442354412456986515 163236158163531618685479773)
      ·
        refine ⟨61213559311324357007054915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163236158163531618685479773 61213559311324357007054915)
        ·
          refine ⟨91820338966986535510582373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61213559311324357007054915 91820338966986535510582373)
          ·
            refine ⟨17216313556309975408234195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91820338966986535510582373 17216313556309975408234195)
            ·
              refine ⟨25824470334464963112351293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17216313556309975408234195 25824470334464963112351293)
              ·
                refine ⟨9684176375424361167131735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25824470334464963112351293 9684176375424361167131735)
                ·
                  refine ⟨14526264563136541750697603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9684176375424361167131735 14526264563136541750697603)
                  ·
                    refine ⟨21789396844704812626046405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14526264563136541750697603 21789396844704812626046405)
                    ·
                      refine ⟨4085511908382152367383701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21789396844704812626046405 4085511908382152367383701)
                      ·
                        rfl

theorem cell23_7956506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_7956506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956506 prefixEnd_7956506 := by exact prefixLift 7956506
  have htrace : WordTrace (prefixWord ++ tailWord_7956506) baseStart_7956506 baseEnd_7956506 := by
    simpa [prefixWord, tailWord_7956506, baseEnd_7956506] using wordTrace_append hprefix tailTrace_7956506
  have hstable : (prefixWord ++ tailWord_7956506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956506).length < 2 ^ (prefixWord ++ tailWord_7956506).sum := by decide
  have hdescent : baseEnd_7956506 < baseStart_7956506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956526 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_7956526 : Nat := 118140960795 + 7956526 * 2 ^ 59
def prefixEnd_7956526 : Nat := 4983230072969 + 3 ^ 40 * 7956526 * 2
def baseEnd_7956526 : Nat := 4085522177995242289133609

theorem tailTrace_7956526 : CollatzResearch.WordTrace tailWord_7956526 prefixEnd_7956526 4085522177995242289133609 := by
  unfold tailWord_7956526
  simp only [CollatzResearch.WordTrace]
  refine ⟨36274792996609080412628179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193465562648581762200683621 36274792996609080412628179)
  ·
    refine ⟨54412189494913620618942269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36274792996609080412628179 54412189494913620618942269)
    ·
      refine ⟨20404571060592607732103351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54412189494913620618942269 20404571060592607732103351)
      ·
        refine ⟨30606856590888911598155027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20404571060592607732103351 30606856590888911598155027)
        ·
          refine ⟨45910284886333367397232541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30606856590888911598155027 45910284886333367397232541)
          ·
            refine ⟨17216356832375012773962203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45910284886333367397232541 17216356832375012773962203)
            ·
              refine ⟨25824535248562519160943305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17216356832375012773962203 25824535248562519160943305)
              ·
                refine ⟨19368401436421889370707479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25824535248562519160943305 19368401436421889370707479)
                ·
                  refine ⟨29052602154632834056061219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19368401436421889370707479 29052602154632834056061219)
                  ·
                    refine ⟨43578903231949251084091829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29052602154632834056061219 43578903231949251084091829)
                    ·
                      refine ⟨4085522177995242289133609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43578903231949251084091829 4085522177995242289133609)
                      ·
                        rfl

theorem cell23_7956526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_7956526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956526 prefixEnd_7956526 := by exact prefixLift 7956526
  have htrace : WordTrace (prefixWord ++ tailWord_7956526) baseStart_7956526 baseEnd_7956526 := by
    simpa [prefixWord, tailWord_7956526, baseEnd_7956526] using wordTrace_append hprefix tailTrace_7956526
  have hstable : (prefixWord ++ tailWord_7956526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956526).length < 2 ^ (prefixWord ++ tailWord_7956526).sum := by decide
  have hdescent : baseEnd_7956526 < baseStart_7956526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956556 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 4, 1, 3]
def baseStart_7956556 : Nat := 118140960795 + 7956556 * 2 ^ 59
def prefixEnd_7956556 : Nat := 4983230072969 + 3 ^ 40 * 7956556 * 2
def baseEnd_7956556 : Nat := 4085537582414877171758471

theorem tailTrace_7956556 : CollatzResearch.WordTrace tailWord_7956556 prefixEnd_7956556 4085537582414877171758471 := by
  unfold tailWord_7956556
  simp only [CollatzResearch.WordTrace]
  refine ⟨145099719081381979212308761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193466292108509305616411681 145099719081381979212308761)
  ·
    refine ⟨108824789311036484409231571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145099719081381979212308761 108824789311036484409231571)
    ·
      refine ⟨163237183966554726613847357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108824789311036484409231571 163237183966554726613847357)
      ·
        refine ⟨61213943987458022480192759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163237183966554726613847357 61213943987458022480192759)
        ·
          refine ⟨91820915981187033720289139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61213943987458022480192759 91820915981187033720289139)
          ·
            refine ⟨137731373971780550580433709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91820915981187033720289139 137731373971780550580433709)
            ·
              refine ⟨51649265239417706467662641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137731373971780550580433709 51649265239417706467662641)
              ·
                refine ⟨38736948929563279850746981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51649265239417706467662641 38736948929563279850746981)
                ·
                  refine ⟨7263177924293114972015059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38736948929563279850746981 7263177924293114972015059)
                  ·
                    refine ⟨10894766886439672458022589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7263177924293114972015059 10894766886439672458022589)
                    ·
                      refine ⟨4085537582414877171758471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10894766886439672458022589 4085537582414877171758471)
                      ·
                        rfl

theorem cell23_7956556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_7956556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956556 prefixEnd_7956556 := by exact prefixLift 7956556
  have htrace : WordTrace (prefixWord ++ tailWord_7956556) baseStart_7956556 baseEnd_7956556 := by
    simpa [prefixWord, tailWord_7956556, baseEnd_7956556] using wordTrace_append hprefix tailTrace_7956556
  have hstable : (prefixWord ++ tailWord_7956556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956556).length < 2 ^ (prefixWord ++ tailWord_7956556).sum := by decide
  have hdescent : baseEnd_7956556 < baseStart_7956556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956589 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_7956589 : Nat := 118140960795 + 7956589 * 2 ^ 59
def prefixEnd_7956589 : Nat := 4983230072969 + 3 ^ 40 * 7956589 * 2
def baseEnd_7956589 : Nat := 1361851509092158514215273

theorem tailTrace_7956589 : CollatzResearch.WordTrace tailWord_7956589 prefixEnd_7956589 1361851509092158514215273 := by
  unfold tailWord_7956589
  simp only [CollatzResearch.WordTrace]
  refine ⟨290200641771644405060568821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193467094514429603373712547 290200641771644405060568821)
  ·
    refine ⟨27206310166091662974428327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 290200641771644405060568821 27206310166091662974428327)
    ·
      refine ⟨40809465249137494461642491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27206310166091662974428327 40809465249137494461642491)
      ·
        refine ⟨61214197873706241692463737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40809465249137494461642491 61214197873706241692463737)
        ·
          refine ⟨45910648405279681269347803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61214197873706241692463737 45910648405279681269347803)
          ·
            refine ⟨68865972607919521904021705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45910648405279681269347803 68865972607919521904021705)
            ·
              refine ⟨51649479455939641428016279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68865972607919521904021705 51649479455939641428016279)
              ·
                refine ⟨77474219183909462142024419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51649479455939641428016279 77474219183909462142024419)
                ·
                  refine ⟨116211328775864193213036629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77474219183909462142024419 116211328775864193213036629)
                  ·
                    refine ⟨1361851509092158514215273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116211328775864193213036629 1361851509092158514215273)
                    ·
                      rfl

theorem cell23_7956589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_7956589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956589 prefixEnd_7956589 := by exact prefixLift 7956589
  have htrace : WordTrace (prefixWord ++ tailWord_7956589) baseStart_7956589 baseEnd_7956589 := by
    simpa [prefixWord, tailWord_7956589, baseEnd_7956589] using wordTrace_append hprefix tailTrace_7956589
  have hstable : (prefixWord ++ tailWord_7956589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956589).length < 2 ^ (prefixWord ++ tailWord_7956589).sum := by decide
  have hdescent : baseEnd_7956589 < baseStart_7956589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956599 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_7956599 : Nat := 118140960795 + 7956599 * 2 ^ 59
def prefixEnd_7956599 : Nat := 4983230072969 + 3 ^ 40 * 7956599 * 2
def baseEnd_7956599 : Nat := 4085559662083020503520773

theorem tailTrace_7956599 : CollatzResearch.WordTrace tailWord_7956599 prefixEnd_7956599 4085559662083020503520773 := by
  unfold tailWord_7956599
  simp only [CollatzResearch.WordTrace]
  refine ⟨290201006501608176768432851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193467337667738784512288567 290201006501608176768432851)
  ·
    refine ⟨435301509752412265152649277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290201006501608176768432851 435301509752412265152649277)
    ·
      refine ⟨163238066157154599432243479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435301509752412265152649277 163238066157154599432243479)
      ·
        refine ⟨244857099235731899148365219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163238066157154599432243479 244857099235731899148365219)
        ·
          refine ⟨367285648853597848722547829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244857099235731899148365219 367285648853597848722547829)
          ·
            refine ⟨34433029580024798317738859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367285648853597848722547829 34433029580024798317738859)
            ·
              refine ⟨51649544370037197476608289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34433029580024798317738859 51649544370037197476608289)
              ·
                refine ⟨38737158277527898107456217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51649544370037197476608289 38737158277527898107456217)
                ·
                  refine ⟨29052868708145923580592163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38737158277527898107456217 29052868708145923580592163)
                  ·
                    refine ⟨43579303062218885370888245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29052868708145923580592163 43579303062218885370888245)
                    ·
                      refine ⟨4085559662083020503520773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43579303062218885370888245 4085559662083020503520773)
                      ·
                        rfl

theorem cell23_7956599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_7956599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956599 prefixEnd_7956599 := by exact prefixLift 7956599
  have htrace : WordTrace (prefixWord ++ tailWord_7956599) baseStart_7956599 baseEnd_7956599 := by
    simpa [prefixWord, tailWord_7956599, baseEnd_7956599] using wordTrace_append hprefix tailTrace_7956599
  have hstable : (prefixWord ++ tailWord_7956599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956599).length < 2 ^ (prefixWord ++ tailWord_7956599).sum := by decide
  have hdescent : baseEnd_7956599 < baseStart_7956599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956613 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 1, 4, 2]
def baseStart_7956613 : Nat := 118140960795 + 7956613 * 2 ^ 59
def prefixEnd_7956613 : Nat := 4983230072969 + 3 ^ 40 * 7956613 * 2
def baseEnd_7956613 : Nat := 4085566850812183448745709

theorem tailTrace_7956613 : CollatzResearch.WordTrace tailWord_7956613 prefixEnd_7956613 4085566850812183448745709 := by
  unfold tailWord_7956613
  simp only [CollatzResearch.WordTrace]
  refine ⟨290201517123557457159442493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193467678082371638106294995 290201517123557457159442493)
  ·
    refine ⟨108825568921334046434790935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290201517123557457159442493 108825568921334046434790935)
    ·
      refine ⟨163238353382001069652186403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108825568921334046434790935 163238353382001069652186403)
      ·
        refine ⟨244857530073001604478279605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163238353382001069652186403 244857530073001604478279605)
        ·
          refine ⟨22955393444343900419838713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244857530073001604478279605 22955393444343900419838713)
          ·
            refine ⟨17216545083257925314879035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22955393444343900419838713 17216545083257925314879035)
            ·
              refine ⟨25824817624886887972318553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17216545083257925314879035 25824817624886887972318553)
              ·
                refine ⟨19368613218665165979238915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25824817624886887972318553 19368613218665165979238915)
                ·
                  refine ⟨29052919827997748968858373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19368613218665165979238915 29052919827997748968858373)
                  ·
                    refine ⟨5447422467749577931660945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29052919827997748968858373 5447422467749577931660945)
                    ·
                      refine ⟨4085566850812183448745709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5447422467749577931660945 4085566850812183448745709)
                      ·
                        rfl

theorem cell23_7956613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_7956613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956613 prefixEnd_7956613 := by exact prefixLift 7956613
  have htrace : WordTrace (prefixWord ++ tailWord_7956613) baseStart_7956613 baseEnd_7956613 := by
    simpa [prefixWord, tailWord_7956613, baseEnd_7956613] using wordTrace_append hprefix tailTrace_7956613
  have hstable : (prefixWord ++ tailWord_7956613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956613).length < 2 ^ (prefixWord ++ tailWord_7956613).sum := by decide
  have hdescent : baseEnd_7956613 < baseStart_7956613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956616 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7956616 : Nat := 118140960795 + 7956616 * 2 ^ 59
def prefixEnd_7956616 : Nat := 4983230072969 + 3 ^ 40 * 7956616 * 2
def baseEnd_7956616 : Nat := 4085568391254146937008195

theorem tailTrace_7956616 : CollatzResearch.WordTrace tailWord_7956616 prefixEnd_7956616 4085568391254146937008195 := by
  unfold tailWord_7956616
  simp only [CollatzResearch.WordTrace]
  refine ⟨145100813271273294335900851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193467751028364392447867801 145100813271273294335900851)
  ·
    refine ⟨217651219906909941503851277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145100813271273294335900851 217651219906909941503851277)
    ·
      refine ⟨81619207465091228063944229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217651219906909941503851277 81619207465091228063944229)
      ·
        refine ⟨15303601399704605261989543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81619207465091228063944229 15303601399704605261989543)
        ·
          refine ⟨22955402099556907892984315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15303601399704605261989543 22955402099556907892984315)
          ·
            refine ⟨34433103149335361839476473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22955402099556907892984315 34433103149335361839476473)
            ·
              refine ⟨25824827362001521379607355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34433103149335361839476473 25824827362001521379607355)
              ·
                refine ⟨38737241043002282069411033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25824827362001521379607355 38737241043002282069411033)
                ·
                  refine ⟨29052930782251711552058275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38737241043002282069411033 29052930782251711552058275)
                  ·
                    refine ⟨43579396173377567328087413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29052930782251711552058275 43579396173377567328087413)
                    ·
                      refine ⟨4085568391254146937008195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43579396173377567328087413 4085568391254146937008195)
                      ·
                        rfl

theorem cell23_7956616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7956616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956616 prefixEnd_7956616 := by exact prefixLift 7956616
  have htrace : WordTrace (prefixWord ++ tailWord_7956616) baseStart_7956616 baseEnd_7956616 := by
    simpa [prefixWord, tailWord_7956616, baseEnd_7956616] using wordTrace_append hprefix tailTrace_7956616
  have hstable : (prefixWord ++ tailWord_7956616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956616).length < 2 ^ (prefixWord ++ tailWord_7956616).sum := by decide
  have hdescent : baseEnd_7956616 < baseStart_7956616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956626 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7956626 : Nat := 118140960795 + 7956626 * 2 ^ 59
def prefixEnd_7956626 : Nat := 4983230072969 + 3 ^ 40 * 7956626 * 2
def baseEnd_7956626 : Nat := 4085573526060691897883149

theorem tailTrace_7956626 : CollatzResearch.WordTrace tailWord_7956626 prefixEnd_7956626 4085573526060691897883149 := by
  unfold tailWord_7956626
  simp only [CollatzResearch.WordTrace]
  refine ⟨72550497818127590094916433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193467994181673573586443821 72550497818127590094916433)
  ·
    refine ⟨54412873363595692571187325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72550497818127590094916433 54412873363595692571187325)
    ·
      refine ⟨20404827511348384714195247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54412873363595692571187325 20404827511348384714195247)
      ·
        refine ⟨30607241267022577071292871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20404827511348384714195247 30607241267022577071292871)
        ·
          refine ⟨45910861900533865606939307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30607241267022577071292871 45910861900533865606939307)
          ·
            refine ⟨68866292850800798410408961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45910861900533865606939307 68866292850800798410408961)
            ·
              refine ⟨51649719638100598807806721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68866292850800798410408961 51649719638100598807806721)
              ·
                refine ⟨38737289728575449105855041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51649719638100598807806721 38737289728575449105855041)
                ·
                  refine ⟨29052967296431586829391281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38737289728575449105855041 29052967296431586829391281)
                  ·
                    refine ⟨21789725472323690122043461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29052967296431586829391281 21789725472323690122043461)
                    ·
                      refine ⟨4085573526060691897883149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21789725472323690122043461 4085573526060691897883149)
                      ·
                        rfl

theorem cell23_7956626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7956626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956626 prefixEnd_7956626 := by exact prefixLift 7956626
  have htrace : WordTrace (prefixWord ++ tailWord_7956626) baseStart_7956626 baseEnd_7956626 := by
    simpa [prefixWord, tailWord_7956626, baseEnd_7956626] using wordTrace_append hprefix tailTrace_7956626
  have hstable : (prefixWord ++ tailWord_7956626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956626).length < 2 ^ (prefixWord ++ tailWord_7956626).sum := by decide
  have hdescent : baseEnd_7956626 < baseStart_7956626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956666 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_7956666 : Nat := 118140960795 + 7956666 * 2 ^ 59
def prefixEnd_7956666 : Nat := 4983230072969 + 3 ^ 40 * 7956666 * 2
def baseEnd_7956666 : Nat := 1361864688428957247127655

theorem tailTrace_7956666 : CollatzResearch.WordTrace tailWord_7956666 prefixEnd_7956666 1361864688428957247127655 := by
  unfold tailWord_7956666
  simp only [CollatzResearch.WordTrace]
  refine ⟨72550862548091361802780463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193468966794910298140747901 72550862548091361802780463)
  ·
    refine ⟨108826293822137042704170695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72550862548091361802780463 108826293822137042704170695)
    ·
      refine ⟨163239440733205564056256043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108826293822137042704170695 163239440733205564056256043)
      ·
        refine ⟨244859161099808346084384065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163239440733205564056256043 244859161099808346084384065)
        ·
          refine ⟨183644370824856259563288049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244859161099808346084384065 183644370824856259563288049)
          ·
            refine ⟨137733278118642194672466037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183644370824856259563288049 137733278118642194672466037)
            ·
              refine ⟨12912494823622705750543691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137733278118642194672466037 12912494823622705750543691)
              ·
                refine ⟨19368742235434058625815537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12912494823622705750543691 19368742235434058625815537)
                ·
                  refine ⟨14526556676575543969361653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19368742235434058625815537 14526556676575543969361653)
                  ·
                    refine ⟨1361864688428957247127655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14526556676575543969361653 1361864688428957247127655)
                    ·
                      rfl

theorem cell23_7956666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_7956666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956666 prefixEnd_7956666 := by exact prefixLift 7956666
  have htrace : WordTrace (prefixWord ++ tailWord_7956666) baseStart_7956666 baseEnd_7956666 := by
    simpa [prefixWord, tailWord_7956666, baseEnd_7956666] using wordTrace_append hprefix tailTrace_7956666
  have hstable : (prefixWord ++ tailWord_7956666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956666).length < 2 ^ (prefixWord ++ tailWord_7956666).sum := by decide
  have hdescent : baseEnd_7956666 < baseStart_7956666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956670 : List Nat := [4, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_7956670 : Nat := 118140960795 + 7956670 * 2 ^ 59
def prefixEnd_7956670 : Nat := 4983230072969 + 3 ^ 40 * 7956670 * 2
def baseEnd_7956670 : Nat := 453955124356609969525883

theorem tailTrace_7956670 : CollatzResearch.WordTrace tailWord_7956670 prefixEnd_7956670 453955124356609969525883 := by
  unfold tailWord_7956670
  simp only [CollatzResearch.WordTrace]
  refine ⟨36275449510543869486783433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193469064056233970596178309 36275449510543869486783433)
  ·
    refine ⟨27206587132907902115087575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36275449510543869486783433 27206587132907902115087575)
    ·
      refine ⟨40809880699361853172631363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27206587132907902115087575 40809880699361853172631363)
      ·
        refine ⟨61214821049042779758947045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40809880699361853172631363 61214821049042779758947045)
        ·
          refine ⟨11477778946695521204802571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61214821049042779758947045 11477778946695521204802571)
          ·
            refine ⟨17216668420043281807203857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11477778946695521204802571 17216668420043281807203857)
            ·
              refine ⟨12912501315032461355402893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17216668420043281807203857 12912501315032461355402893)
              ·
                refine ⟨4842187993137173008276085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12912501315032461355402893 4842187993137173008276085)
                ·
                  refine ⟨453955124356609969525883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4842187993137173008276085 453955124356609969525883)
                  ·
                    rfl

theorem cell23_7956670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_7956670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956670 prefixEnd_7956670 := by exact prefixLift 7956670
  have htrace : WordTrace (prefixWord ++ tailWord_7956670) baseStart_7956670 baseEnd_7956670 := by
    simpa [prefixWord, tailWord_7956670, baseEnd_7956670] using wordTrace_append hprefix tailTrace_7956670
  have hstable : (prefixWord ++ tailWord_7956670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956670).length < 2 ^ (prefixWord ++ tailWord_7956670).sum := by decide
  have hdescent : baseEnd_7956670 < baseStart_7956670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956689 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_7956689 : Nat := 118140960795 + 7956689 * 2 ^ 59
def prefixEnd_7956689 : Nat := 4983230072969 + 3 ^ 40 * 7956689 * 2
def baseEnd_7956689 : Nat := 4085605875341925151395359

theorem tailTrace_7956689 : CollatzResearch.WordTrace tailWord_7956689 prefixEnd_7956689 4085605875341925151395359 := by
  unfold tailWord_7956689
  simp only [CollatzResearch.WordTrace]
  refine ⟨290204289071282122139209121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193469526047521414759472747 290204289071282122139209121)
  ·
    refine ⟨217653216803461591604406841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290204289071282122139209121 217653216803461591604406841)
    ·
      refine ⟨163239912602596193703305131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217653216803461591604406841 163239912602596193703305131)
      ·
        refine ⟨244859868903894290554957697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163239912602596193703305131 244859868903894290554957697)
        ·
          refine ⟨183644901677920717916218273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244859868903894290554957697 183644901677920717916218273)
          ·
            refine ⟨137733676258440538437163705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183644901677920717916218273 137733676258440538437163705)
            ·
              refine ⟨103300257193830403827872779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137733676258440538437163705 103300257193830403827872779)
              ·
                refine ⟨154950385790745605741809169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103300257193830403827872779 154950385790745605741809169)
                ·
                  refine ⟨116212789343059204306356877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154950385790745605741809169 116212789343059204306356877)
                  ·
                    refine ⟨43579796003647201614883829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116212789343059204306356877 43579796003647201614883829)
                    ·
                      refine ⟨4085605875341925151395359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43579796003647201614883829 4085605875341925151395359)
                      ·
                        rfl

theorem cell23_7956689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_7956689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956689 prefixEnd_7956689 := by exact prefixLift 7956689
  have htrace : WordTrace (prefixWord ++ tailWord_7956689) baseStart_7956689 baseEnd_7956689 := by
    simpa [prefixWord, tailWord_7956689, baseEnd_7956689] using wordTrace_append hprefix tailTrace_7956689
  have hstable : (prefixWord ++ tailWord_7956689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956689).length < 2 ^ (prefixWord ++ tailWord_7956689).sum := by decide
  have hdescent : baseEnd_7956689 < baseStart_7956689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956699 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 4]
def baseStart_7956699 : Nat := 118140960795 + 7956699 * 2 ^ 59
def prefixEnd_7956699 : Nat := 4983230072969 + 3 ^ 40 * 7956699 * 2
def baseEnd_7956699 : Nat := 4085611010148470112270313

theorem tailTrace_7956699 : CollatzResearch.WordTrace tailWord_7956699 prefixEnd_7956699 4085611010148470112270313 := by
  unfold tailWord_7956699
  simp only [CollatzResearch.WordTrace]
  refine ⟨290204653801245893847073151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193469769200830595898048767 290204653801245893847073151)
  ·
    refine ⟨435306980701868840770609727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290204653801245893847073151 435306980701868840770609727)
    ·
      refine ⟨652960471052803261155914591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435306980701868840770609727 652960471052803261155914591)
      ·
        refine ⟨979440706579204891733871887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652960471052803261155914591 979440706579204891733871887)
        ·
          refine ⟨1469161059868807337600807831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979440706579204891733871887 1469161059868807337600807831)
          ·
            refine ⟨2203741589803211006401211747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469161059868807337600807831 2203741589803211006401211747)
            ·
              refine ⟨3305612384704816509601817621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203741589803211006401211747 3305612384704816509601817621)
              ·
                refine ⟨154950580533038273887585201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3305612384704816509601817621 154950580533038273887585201)
                ·
                  refine ⟨116212935399778705415688901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154950580533038273887585201 116212935399778705415688901)
                  ·
                    refine ⟨21789925387458507265441669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116212935399778705415688901 21789925387458507265441669)
                    ·
                      refine ⟨4085611010148470112270313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21789925387458507265441669 4085611010148470112270313)
                      ·
                        rfl

theorem cell23_7956699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 4].length) (baseStart_7956699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956699 prefixEnd_7956699 := by exact prefixLift 7956699
  have htrace : WordTrace (prefixWord ++ tailWord_7956699) baseStart_7956699 baseEnd_7956699 := by
    simpa [prefixWord, tailWord_7956699, baseEnd_7956699] using wordTrace_append hprefix tailTrace_7956699
  have hstable : (prefixWord ++ tailWord_7956699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956699).length < 2 ^ (prefixWord ++ tailWord_7956699).sum := by decide
  have hdescent : baseEnd_7956699 < baseStart_7956699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956726 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_7956726 : Nat := 118140960795 + 7956726 * 2 ^ 59
def prefixEnd_7956726 : Nat := 4983230072969 + 3 ^ 40 * 7956726 * 2
def baseEnd_7956726 : Nat := 453958319347349056292521

theorem tailTrace_7956726 : CollatzResearch.WordTrace tailWord_7956726 prefixEnd_7956726 453958319347349056292521 := by
  unfold tailWord_7956726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18137852410759254841144127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193470425714765384972204021 18137852410759254841144127)
  ·
    refine ⟨27206778616138882261716191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18137852410759254841144127 27206778616138882261716191)
    ·
      refine ⟨40810167924208323392574287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27206778616138882261716191 40810167924208323392574287)
      ·
        refine ⟨61215251886312485088861431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40810167924208323392574287 61215251886312485088861431)
        ·
          refine ⟨91822877829468727633292147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61215251886312485088861431 91822877829468727633292147)
          ·
            refine ⟨137734316744203091449938221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91822877829468727633292147 137734316744203091449938221)
            ·
              refine ⟨51650368779076159293726833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137734316744203091449938221 51650368779076159293726833)
              ·
                refine ⟨38737776584307119470295125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51650368779076159293726833 38737776584307119470295125)
                ·
                  refine ⟨453958319347349056292521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38737776584307119470295125 453958319347349056292521)
                  ·
                    rfl

theorem cell23_7956726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_7956726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956726 prefixEnd_7956726 := by exact prefixLift 7956726
  have htrace : WordTrace (prefixWord ++ tailWord_7956726) baseStart_7956726 baseEnd_7956726 := by
    simpa [prefixWord, tailWord_7956726, baseEnd_7956726] using wordTrace_append hprefix tailTrace_7956726
  have hstable : (prefixWord ++ tailWord_7956726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956726).length < 2 ^ (prefixWord ++ tailWord_7956726).sum := by decide
  have hdescent : baseEnd_7956726 < baseStart_7956726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956729 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_7956729 : Nat := 118140960795 + 7956729 * 2 ^ 59
def prefixEnd_7956729 : Nat := 4983230072969 + 3 ^ 40 * 7956729 * 2
def baseEnd_7956729 : Nat := 4085626414568104994895175

theorem tailTrace_7956729 : CollatzResearch.WordTrace tailWord_7956729 prefixEnd_7956729 4085626414568104994895175 := by
  unfold tailWord_7956729
  simp only [CollatzResearch.WordTrace]
  refine ⟨290205747991137208970665241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193470498660758139313776827 290205747991137208970665241)
  ·
    refine ⟨217654310993352906727998931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290205747991137208970665241 217654310993352906727998931)
    ·
      refine ⟨326481466490029360091998397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217654310993352906727998931 326481466490029360091998397)
      ·
        refine ⟨122430549933761010034499399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326481466490029360091998397 122430549933761010034499399)
        ·
          refine ⟨183645824900641515051749099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122430549933761010034499399 183645824900641515051749099)
          ·
            refine ⟨275468737350962272577623649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183645824900641515051749099 275468737350962272577623649)
            ·
              refine ⟨206601553013221704433217737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275468737350962272577623649 206601553013221704433217737)
              ·
                refine ⟨154951164759916278324913303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206601553013221704433217737 154951164759916278324913303)
                ·
                  refine ⟨232426747139874417487369955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154951164759916278324913303 232426747139874417487369955)
                  ·
                    refine ⟨348640120709811626231054933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 232426747139874417487369955 348640120709811626231054933)
                    ·
                      refine ⟨4085626414568104994895175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 348640120709811626231054933 4085626414568104994895175)
                      ·
                        rfl

theorem cell23_7956729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_7956729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956729 prefixEnd_7956729 := by exact prefixLift 7956729
  have htrace : WordTrace (prefixWord ++ tailWord_7956729) baseStart_7956729 baseEnd_7956729 := by
    simpa [prefixWord, tailWord_7956729, baseEnd_7956729] using wordTrace_append hprefix tailTrace_7956729
  have hstable : (prefixWord ++ tailWord_7956729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956729).length < 2 ^ (prefixWord ++ tailWord_7956729).sum := by decide
  have hdescent : baseEnd_7956729 < baseStart_7956729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956730 : List Nat := [3, 1, 1, 1, 1, 5, 3, 3, 1, 4]
def baseStart_7956730 : Nat := 118140960795 + 7956730 * 2 ^ 59
def prefixEnd_7956730 : Nat := 4983230072969 + 3 ^ 40 * 7956730 * 2
def baseEnd_7956730 : Nat := 1361875642682919830327557

theorem tailTrace_7956730 : CollatzResearch.WordTrace tailWord_7956730 prefixEnd_7956730 1361875642682919830327557 := by
  unfold tailWord_7956730
  simp only [CollatzResearch.WordTrace]
  refine ⟨72551446116033396535362911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193470522976089057427634429 72551446116033396535362911)
  ·
    refine ⟨108827169174050094803044367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72551446116033396535362911 108827169174050094803044367)
    ·
      refine ⟨163240753761075142204566551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108827169174050094803044367 163240753761075142204566551)
      ·
        refine ⟨244861130641612713306849827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163240753761075142204566551 244861130641612713306849827)
        ·
          refine ⟨367291695962419069960274741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244861130641612713306849827 367291695962419069960274741)
          ·
            refine ⟨34433596496476787808775757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367291695962419069960274741 34433596496476787808775757)
            ·
              refine ⟨12912598686178795428290909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34433596496476787808775757 12912598686178795428290909)
              ·
                refine ⟨4842224507317048285609091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12912598686178795428290909 4842224507317048285609091)
                ·
                  refine ⟨7263336760975572428413637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4842224507317048285609091 7263336760975572428413637)
                  ·
                    refine ⟨1361875642682919830327557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7263336760975572428413637 1361875642682919830327557)
                    ·
                      rfl

theorem cell23_7956730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_7956730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956730 prefixEnd_7956730 := by exact prefixLift 7956730
  have htrace : WordTrace (prefixWord ++ tailWord_7956730) baseStart_7956730 baseEnd_7956730 := by
    simpa [prefixWord, tailWord_7956730, baseEnd_7956730] using wordTrace_append hprefix tailTrace_7956730
  have hstable : (prefixWord ++ tailWord_7956730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956730).length < 2 ^ (prefixWord ++ tailWord_7956730).sum := by decide
  have hdescent : baseEnd_7956730 < baseStart_7956730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956740 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_7956740 : Nat := 118140960795 + 7956740 * 2 ^ 59
def prefixEnd_7956740 : Nat := 4983230072969 + 3 ^ 40 * 7956740 * 2
def baseEnd_7956740 : Nat := 4085632062855304451857625

theorem tailTrace_7956740 : CollatzResearch.WordTrace tailWord_7956740 prefixEnd_7956740 4085632062855304451857625 := by
  unfold tailWord_7956740
  simp only [CollatzResearch.WordTrace]
  refine ⟨145103074597048678924657837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193470766129398238566210449 145103074597048678924657837)
  ·
    refine ⟨54413652973893254596746689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145103074597048678924657837 54413652973893254596746689)
    ·
      refine ⟨40810239730419940947560017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54413652973893254596746689 40810239730419940947560017)
      ·
        refine ⟨30607679797814955710670013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40810239730419940947560017 30607679797814955710670013)
        ·
          refine ⟨11477879924180608391501255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30607679797814955710670013 11477879924180608391501255)
          ·
            refine ⟨17216819886270912587251883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11477879924180608391501255 17216819886270912587251883)
            ·
              refine ⟨25825229829406368880877825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17216819886270912587251883 25825229829406368880877825)
              ·
                refine ⟨19368922372054776660658369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25825229829406368880877825 19368922372054776660658369)
                ·
                  refine ⟨14526691779041082495493777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19368922372054776660658369 14526691779041082495493777)
                  ·
                    refine ⟨10895018834280811871620333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14526691779041082495493777 10895018834280811871620333)
                    ·
                      refine ⟨4085632062855304451857625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10895018834280811871620333 4085632062855304451857625)
                      ·
                        rfl

theorem cell23_7956740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_7956740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956740 prefixEnd_7956740 := by exact prefixLift 7956740
  have htrace : WordTrace (prefixWord ++ tailWord_7956740) baseStart_7956740 baseEnd_7956740 := by
    simpa [prefixWord, tailWord_7956740, baseEnd_7956740] using wordTrace_append hprefix tailTrace_7956740
  have hstable : (prefixWord ++ tailWord_7956740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956740).length < 2 ^ (prefixWord ++ tailWord_7956740).sum := by decide
  have hdescent : baseEnd_7956740 < baseStart_7956740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956773 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_7956773 : Nat := 118140960795 + 7956773 * 2 ^ 59
def prefixEnd_7956773 : Nat := 4983230072969 + 3 ^ 40 * 7956773 * 2
def baseEnd_7956773 : Nat := 1361883002572300940914991

theorem tailTrace_7956773 : CollatzResearch.WordTrace tailWord_7956773 prefixEnd_7956773 1361883002572300940914991 := by
  unfold tailWord_7956773
  simp only [CollatzResearch.WordTrace]
  refine ⟨290207352802977804485266973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193471568535318536323511315 290207352802977804485266973)
  ·
    refine ⟨108827757301116676681975115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290207352802977804485266973 108827757301116676681975115)
    ·
      refine ⟨163241635951675015022962673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108827757301116676681975115 163241635951675015022962673)
      ·
        refine ⟨122431226963756261267222005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163241635951675015022962673 122431226963756261267222005)
        ·
          refine ⟨11477927527852149493802063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122431226963756261267222005 11477927527852149493802063)
          ·
            refine ⟨17216891291778224240703095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11477927527852149493802063 17216891291778224240703095)
            ·
              refine ⟨25825336937667336361054643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17216891291778224240703095 25825336937667336361054643)
              ·
                refine ⟨38738005406501004541581965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25825336937667336361054643 38738005406501004541581965)
                ·
                  refine ⟨14526752027437876703093237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38738005406501004541581965 14526752027437876703093237)
                  ·
                    refine ⟨1361883002572300940914991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14526752027437876703093237 1361883002572300940914991)
                    ·
                      rfl

theorem cell23_7956773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_7956773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956773 prefixEnd_7956773 := by exact prefixLift 7956773
  have htrace : WordTrace (prefixWord ++ tailWord_7956773) baseStart_7956773 baseEnd_7956773 := by
    simpa [prefixWord, tailWord_7956773, baseEnd_7956773] using wordTrace_append hprefix tailTrace_7956773
  have hstable : (prefixWord ++ tailWord_7956773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956773).length < 2 ^ (prefixWord ++ tailWord_7956773).sum := by decide
  have hdescent : baseEnd_7956773 < baseStart_7956773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956803 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 2, 4]
def baseStart_7956803 : Nat := 118140960795 + 7956803 * 2 ^ 59
def prefixEnd_7956803 : Nat := 4983230072969 + 3 ^ 40 * 7956803 * 2
def baseEnd_7956803 : Nat := 1361888137378845901789945

theorem tailTrace_7956803 : CollatzResearch.WordTrace tailWord_7956803 prefixEnd_7956803 1361888137378845901789945 := by
  unfold tailWord_7956803
  simp only [CollatzResearch.WordTrace]
  refine ⟨290208446992869119608859063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193472297995246079739239375 290208446992869119608859063)
  ·
    refine ⟨435312670489303679413288595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290208446992869119608859063 435312670489303679413288595)
    ·
      refine ⟨652969005733955519119932893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435312670489303679413288595 652969005733955519119932893)
      ·
        refine ⟨244863377150233319669974835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 652969005733955519119932893 244863377150233319669974835)
        ·
          refine ⟨367295065725349979504962253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244863377150233319669974835 367295065725349979504962253)
          ·
            refine ⟨137735649647006242314360845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367295065725349979504962253 137735649647006242314360845)
            ·
              refine ⟨51650868617627340867885317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137735649647006242314360845 51650868617627340867885317)
              ·
                refine ⟨9684537865805126412728497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51650868617627340867885317 9684537865805126412728497)
                ·
                  refine ⟨7263403399353844809546373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9684537865805126412728497 7263403399353844809546373)
                  ·
                    refine ⟨1361888137378845901789945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7263403399353844809546373 1361888137378845901789945)
                    ·
                      rfl

theorem cell23_7956803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 4].length) (baseStart_7956803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956803 prefixEnd_7956803 := by exact prefixLift 7956803
  have htrace : WordTrace (prefixWord ++ tailWord_7956803) baseStart_7956803 baseEnd_7956803 := by
    simpa [prefixWord, tailWord_7956803, baseEnd_7956803] using wordTrace_append hprefix tailTrace_7956803
  have hstable : (prefixWord ++ tailWord_7956803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956803).length < 2 ^ (prefixWord ++ tailWord_7956803).sum := by decide
  have hdescent : baseEnd_7956803 < baseStart_7956803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956816 : List Nat := [2, 1, 1, 1, 1, 6, 3, 8]
def baseStart_7956816 : Nat := 118140960795 + 7956816 * 2 ^ 59
def prefixEnd_7956816 : Nat := 4983230072969 + 3 ^ 40 * 7956816 * 2
def baseEnd_7956816 : Nat := 151321151384631339055825

theorem tailTrace_7956816 : CollatzResearch.WordTrace tailWord_7956816 prefixEnd_7956816 151321151384631339055825 := by
  unfold tailWord_7956816
  simp only [CollatzResearch.WordTrace]
  refine ⟨145104460570911011414541151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193472614094548015219388201 145104460570911011414541151)
  ·
    refine ⟨217656690856366517121811727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145104460570911011414541151 217656690856366517121811727)
    ·
      refine ⟨326485036284549775682717591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217656690856366517121811727 326485036284549775682717591)
      ·
        refine ⟨489727554426824663524076387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326485036284549775682717591 489727554426824663524076387)
        ·
          refine ⟨734591331640236995286114581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489727554426824663524076387 734591331640236995286114581)
          ·
            refine ⟨34433968670636109154036621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 734591331640236995286114581 34433968670636109154036621)
            ·
              refine ⟨12912738251488540932763733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34433968670636109154036621 12912738251488540932763733)
              ·
                refine ⟨151321151384631339055825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12912738251488540932763733 151321151384631339055825)
                ·
                  rfl

theorem cell23_7956816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 8].length) (baseStart_7956816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956816 prefixEnd_7956816 := by exact prefixLift 7956816
  have htrace : WordTrace (prefixWord ++ tailWord_7956816) baseStart_7956816 baseEnd_7956816 := by
    simpa [prefixWord, tailWord_7956816, baseEnd_7956816] using wordTrace_append hprefix tailTrace_7956816
  have hstable : (prefixWord ++ tailWord_7956816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956816).length < 2 ^ (prefixWord ++ tailWord_7956816).sum := by decide
  have hdescent : baseEnd_7956816 < baseStart_7956816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956820 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_7956820 : Nat := 118140960795 + 7956820 * 2 ^ 59
def prefixEnd_7956820 : Nat := 4983230072969 + 3 ^ 40 * 7956820 * 2
def baseEnd_7956820 : Nat := 1361891047102554712952419

theorem tailTrace_7956820 : CollatzResearch.WordTrace tailWord_7956820 prefixEnd_7956820 1361891047102554712952419 := by
  unfold tailWord_7956820
  simp only [CollatzResearch.WordTrace]
  refine ⟨145104533516903765756113957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193472711355871687674818609 145104533516903765756113957)
  ·
    refine ⟨27207100034419456079271367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145104533516903765756113957 27207100034419456079271367)
    ·
      refine ⟨40810650051629184118907051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27207100034419456079271367 40810650051629184118907051)
      ·
        refine ⟨61215975077443776178360577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40810650051629184118907051 61215975077443776178360577)
        ·
          refine ⟨45911981308082832133770433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61215975077443776178360577 45911981308082832133770433)
          ·
            refine ⟨34433985981062124100327825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45911981308082832133770433 34433985981062124100327825)
            ·
              refine ⟨25825489485796593075245869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34433985981062124100327825 25825489485796593075245869)
              ·
                refine ⟨9684558557173722403217201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25825489485796593075245869 9684558557173722403217201)
                ·
                  refine ⟨7263418917880291802412901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9684558557173722403217201 7263418917880291802412901)
                  ·
                    refine ⟨1361891047102554712952419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7263418917880291802412901 1361891047102554712952419)
                    ·
                      rfl

theorem cell23_7956820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_7956820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956820 prefixEnd_7956820 := by exact prefixLift 7956820
  have htrace : WordTrace (prefixWord ++ tailWord_7956820) baseStart_7956820 baseEnd_7956820 := by
    simpa [prefixWord, tailWord_7956820, baseEnd_7956820] using wordTrace_append hprefix tailTrace_7956820
  have hstable : (prefixWord ++ tailWord_7956820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956820).length < 2 ^ (prefixWord ++ tailWord_7956820).sum := by decide
  have hdescent : baseEnd_7956820 < baseStart_7956820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956823 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 4]
def baseStart_7956823 : Nat := 118140960795 + 7956823 * 2 ^ 59
def prefixEnd_7956823 : Nat := 4983230072969 + 3 ^ 40 * 7956823 * 2
def baseEnd_7956823 : Nat := 4085674681749627627119743

theorem tailTrace_7956823 : CollatzResearch.WordTrace tailWord_7956823 prefixEnd_7956823 4085674681749627627119743 := by
  unfold tailWord_7956823
  simp only [CollatzResearch.WordTrace]
  refine ⟨290209176452796663024587123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193472784301864442016391415 290209176452796663024587123)
  ·
    refine ⟨435313764679194994536880685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290209176452796663024587123 435313764679194994536880685)
    ·
      refine ⟨163242661754698122951330257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435313764679194994536880685 163242661754698122951330257)
      ·
        refine ⟨122431996316023592213497693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163242661754698122951330257 122431996316023592213497693)
        ·
          refine ⟨45911998618508847080061635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122431996316023592213497693 45911998618508847080061635)
          ·
            refine ⟨68867997927763270620092453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45911998618508847080061635 68867997927763270620092453)
            ·
              refine ⟨12912749611455613241267335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68867997927763270620092453 12912749611455613241267335)
              ·
                refine ⟨19369124417183419861901003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12912749611455613241267335 19369124417183419861901003)
                ·
                  refine ⟨29053686625775129792851505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19369124417183419861901003 29053686625775129792851505)
                  ·
                    refine ⟨21790264969331347344638629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29053686625775129792851505 21790264969331347344638629)
                    ·
                      refine ⟨4085674681749627627119743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21790264969331347344638629 4085674681749627627119743)
                      ·
                        rfl

theorem cell23_7956823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_7956823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956823 prefixEnd_7956823 := by exact prefixLift 7956823
  have htrace : WordTrace (prefixWord ++ tailWord_7956823) baseStart_7956823 baseEnd_7956823 := by
    simpa [prefixWord, tailWord_7956823, baseEnd_7956823] using wordTrace_append hprefix tailTrace_7956823
  have hstable : (prefixWord ++ tailWord_7956823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956823).length < 2 ^ (prefixWord ++ tailWord_7956823).sum := by decide
  have hdescent : baseEnd_7956823 < baseStart_7956823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956843 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 6, 1, 3]
def baseStart_7956843 : Nat := 118140960795 + 7956843 * 2 ^ 59
def prefixEnd_7956843 : Nat := 4983230072969 + 3 ^ 40 * 7956843 * 2
def baseEnd_7956843 : Nat := 4085684951362717548869651

theorem tailTrace_7956843 : CollatzResearch.WordTrace tailWord_7956843 prefixEnd_7956843 4085684951362717548869651 := by
  unfold tailWord_7956843
  simp only [CollatzResearch.WordTrace]
  refine ⟨290209905912724206440315183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193473270608482804293543455 290209905912724206440315183)
  ·
    refine ⟨435314858869086309660472775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290209905912724206440315183 435314858869086309660472775)
    ·
      refine ⟨652972288303629464490709163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435314858869086309660472775 652972288303629464490709163)
      ·
        refine ⟨979458432455444196736063745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652972288303629464490709163 979458432455444196736063745)
        ·
          refine ⟨734593824341583147552047809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 979458432455444196736063745 734593824341583147552047809)
          ·
            refine ⟨550945368256187360664035857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734593824341583147552047809 550945368256187360664035857)
            ·
              refine ⟨413209026192140520498026893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550945368256187360664035857 413209026192140520498026893)
              ·
                refine ⟨154953384822052695186760085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413209026192140520498026893 154953384822052695186760085)
                ·
                  refine ⟨7263439913533720086879379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154953384822052695186760085 7263439913533720086879379)
                  ·
                    refine ⟨10895159870300580130319069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7263439913533720086879379 10895159870300580130319069)
                    ·
                      refine ⟨4085684951362717548869651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10895159870300580130319069 4085684951362717548869651)
                      ·
                        rfl

theorem cell23_7956843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 1, 3].length) (baseStart_7956843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956843 prefixEnd_7956843 := by exact prefixLift 7956843
  have htrace : WordTrace (prefixWord ++ tailWord_7956843) baseStart_7956843 baseEnd_7956843 := by
    simpa [prefixWord, tailWord_7956843, baseEnd_7956843] using wordTrace_append hprefix tailTrace_7956843
  have hstable : (prefixWord ++ tailWord_7956843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956843).length < 2 ^ (prefixWord ++ tailWord_7956843).sum := by decide
  have hdescent : baseEnd_7956843 < baseStart_7956843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956844 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 1, 1, 4]
def baseStart_7956844 : Nat := 118140960795 + 7956844 * 2 ^ 59
def prefixEnd_7956844 : Nat := 4983230072969 + 3 ^ 40 * 7956844 * 2
def baseEnd_7956844 : Nat := 4085685464843372044957147

theorem tailTrace_7956844 : CollatzResearch.WordTrace tailWord_7956844 prefixEnd_7956844 4085685464843372044957147 := by
  unfold tailWord_7956844
  simp only [CollatzResearch.WordTrace]
  refine ⟨145104971192860291805550793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193473294923813722407401057 145104971192860291805550793)
  ·
    refine ⟨108828728394645218854163095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145104971192860291805550793 108828728394645218854163095)
    ·
      refine ⟨163243092591967828281244643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108828728394645218854163095 163243092591967828281244643)
      ·
        refine ⟨244864638887951742421866965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163243092591967828281244643 244864638887951742421866965)
        ·
          refine ⟨5739014973936368963012507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 244864638887951742421866965 5739014973936368963012507)
          ·
            refine ⟨8608522460904553444518761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739014973936368963012507 8608522460904553444518761)
            ·
              refine ⟨6456391845678415083389071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8608522460904553444518761 6456391845678415083389071)
              ·
                refine ⟨9684587768517622625083607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6456391845678415083389071 9684587768517622625083607)
                ·
                  refine ⟨14526881652776433937625411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9684587768517622625083607 14526881652776433937625411)
                  ·
                    refine ⟨21790322479164650906438117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14526881652776433937625411 21790322479164650906438117)
                    ·
                      refine ⟨4085685464843372044957147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21790322479164650906438117 4085685464843372044957147)
                      ·
                        rfl

theorem cell23_7956844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_7956844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956844 prefixEnd_7956844 := by exact prefixLift 7956844
  have htrace : WordTrace (prefixWord ++ tailWord_7956844) baseStart_7956844 baseEnd_7956844 := by
    simpa [prefixWord, tailWord_7956844, baseEnd_7956844] using wordTrace_append hprefix tailTrace_7956844
  have hstable : (prefixWord ++ tailWord_7956844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956844).length < 2 ^ (prefixWord ++ tailWord_7956844).sum := by decide
  have hdescent : baseEnd_7956844 < baseStart_7956844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956860 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_7956860 : Nat := 118140960795 + 7956860 * 2 ^ 59
def prefixEnd_7956860 : Nat := 4983230072969 + 3 ^ 40 * 7956860 * 2
def baseEnd_7956860 : Nat := 4085693680533843982357073

theorem tailTrace_7956860 : CollatzResearch.WordTrace tailWord_7956860 prefixEnd_7956860 4085693680533843982357073 := by
  unfold tailWord_7956860
  simp only [CollatzResearch.WordTrace]
  refine ⟨145105262976831309171842017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193473683969108412229122689 145105262976831309171842017)
  ·
    refine ⟨108828947232623481878881513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145105262976831309171842017 108828947232623481878881513)
    ·
      refine ⟨81621710424467611409161135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108828947232623481878881513 81621710424467611409161135)
      ·
        refine ⟨122432565636701417113741703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81621710424467611409161135 122432565636701417113741703)
        ·
          refine ⟨183648848455052125670612555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122432565636701417113741703 183648848455052125670612555)
          ·
            refine ⟨275473272682578188505918833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183648848455052125670612555 275473272682578188505918833)
            ·
              refine ⟨206604954511933641379439125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275473272682578188505918833 206604954511933641379439125)
              ·
                refine ⟨9684607242746889439661209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206604954511933641379439125 9684607242746889439661209)
                ·
                  refine ⟨7263455432060167079745907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9684607242746889439661209 7263455432060167079745907)
                  ·
                    refine ⟨10895183148090250619618861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7263455432060167079745907 10895183148090250619618861)
                    ·
                      refine ⟨4085693680533843982357073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10895183148090250619618861 4085693680533843982357073)
                      ·
                        rfl

theorem cell23_7956860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_7956860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956860 prefixEnd_7956860 := by exact prefixLift 7956860
  have htrace : WordTrace (prefixWord ++ tailWord_7956860) baseStart_7956860 baseEnd_7956860 := by
    simpa [prefixWord, tailWord_7956860, baseEnd_7956860] using wordTrace_append hprefix tailTrace_7956860
  have hstable : (prefixWord ++ tailWord_7956860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956860).length < 2 ^ (prefixWord ++ tailWord_7956860).sum := by decide
  have hdescent : baseEnd_7956860 < baseStart_7956860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956874 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4]
def baseStart_7956874 : Nat := 118140960795 + 7956874 * 2 ^ 59
def prefixEnd_7956874 : Nat := 4983230072969 + 3 ^ 40 * 7956874 * 2
def baseEnd_7956874 : Nat := 4085700869263006927582009

theorem tailTrace_7956874 : CollatzResearch.WordTrace tailWord_7956874 prefixEnd_7956874 4085700869263006927582009 := by
  unfold tailWord_7956874
  simp only [CollatzResearch.WordTrace]
  refine ⟨72552759143902974683673419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193474024383741265823129117 72552759143902974683673419)
  ·
    refine ⟨108829138715854462025510129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72552759143902974683673419 108829138715854462025510129)
    ·
      refine ⟨81621854036890846519132597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108829138715854462025510129 81621854036890846519132597)
      ·
        refine ⟨7652048815958516861168681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81621854036890846519132597 7652048815958516861168681)
        ·
          refine ⟨5739036611968887645876511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7652048815958516861168681 5739036611968887645876511)
          ·
            refine ⟨8608554917953331468814767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739036611968887645876511 8608554917953331468814767)
            ·
              refine ⟨12912832376929997203222151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8608554917953331468814767 12912832376929997203222151)
              ·
                refine ⟨19369248565394995804833227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12912832376929997203222151 19369248565394995804833227)
                ·
                  refine ⟨29053872848092493707249841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19369248565394995804833227 29053872848092493707249841)
                  ·
                    refine ⟨21790404636069370280437381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29053872848092493707249841 21790404636069370280437381)
                    ·
                      refine ⟨4085700869263006927582009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21790404636069370280437381 4085700869263006927582009)
                      ·
                        rfl

theorem cell23_7956874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_7956874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956874 prefixEnd_7956874 := by exact prefixLift 7956874
  have htrace : WordTrace (prefixWord ++ tailWord_7956874) baseStart_7956874 baseEnd_7956874 := by
    simpa [prefixWord, tailWord_7956874, baseEnd_7956874] using wordTrace_append hprefix tailTrace_7956874
  have hstable : (prefixWord ++ tailWord_7956874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956874).length < 2 ^ (prefixWord ++ tailWord_7956874).sum := by decide
  have hdescent : baseEnd_7956874 < baseStart_7956874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956900 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 1, 4, 2]
def baseStart_7956900 : Nat := 118140960795 + 7956900 * 2 ^ 59
def prefixEnd_7956900 : Nat := 4983230072969 + 3 ^ 40 * 7956900 * 2
def baseEnd_7956900 : Nat := 4085714219760023825856889

theorem tailTrace_7956900 : CollatzResearch.WordTrace tailWord_7956900 prefixEnd_7956900 4085714219760023825856889 := by
  unfold tailWord_7956900
  simp only [CollatzResearch.WordTrace]
  refine ⟨145105992436758852587570077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193474656582345136783426769 145105992436758852587570077)
  ·
    refine ⟨54414747163784569720338779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145105992436758852587570077 54414747163784569720338779)
    ·
      refine ⟨81622120745676854580508169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54414747163784569720338779 81622120745676854580508169)
      ·
        refine ⟨61216590559257640935381127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81622120745676854580508169 61216590559257640935381127)
        ·
          refine ⟨91824885838886461403071691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61216590559257640935381127 91824885838886461403071691)
          ·
            refine ⟨137737328758329692104607537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91824885838886461403071691 137737328758329692104607537)
            ·
              refine ⟨103302996568747269078455653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137737328758329692104607537 103302996568747269078455653)
              ·
                refine ⟨19369311856640112952210435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103302996568747269078455653 19369311856640112952210435)
                ·
                  refine ⟨29053967784960169428315653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19369311856640112952210435 29053967784960169428315653)
                  ·
                    refine ⟨5447618959680031767809185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29053967784960169428315653 5447618959680031767809185)
                    ·
                      refine ⟨4085714219760023825856889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5447618959680031767809185 4085714219760023825856889)
                      ·
                        rfl

theorem cell23_7956900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_7956900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956900 prefixEnd_7956900 := by exact prefixLift 7956900
  have htrace : WordTrace (prefixWord ++ tailWord_7956900) baseStart_7956900 baseEnd_7956900 := by
    simpa [prefixWord, tailWord_7956900, baseEnd_7956900] using wordTrace_append hprefix tailTrace_7956900
  have hstable : (prefixWord ++ tailWord_7956900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956900).length < 2 ^ (prefixWord ++ tailWord_7956900).sum := by decide
  have hdescent : baseEnd_7956900 < baseStart_7956900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956903 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7956903 : Nat := 118140960795 + 7956903 * 2 ^ 59
def prefixEnd_7956903 : Nat := 4983230072969 + 3 ^ 40 * 7956903 * 2
def baseEnd_7956903 : Nat := 4085715760201987314119375

theorem tailTrace_7956903 : CollatzResearch.WordTrace tailWord_7956903 prefixEnd_7956903 4085715760201987314119375 := by
  unfold tailWord_7956903
  simp only [CollatzResearch.WordTrace]
  refine ⟨290212094292506836687499363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193474729528337891124999575 290212094292506836687499363)
  ·
    refine ⟨435318141438760255031249045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290212094292506836687499363 435318141438760255031249045)
    ·
      refine ⟨20405537879941886954589799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 435318141438760255031249045 20405537879941886954589799)
      ·
        refine ⟨30608306819912830431884699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20405537879941886954589799 30608306819912830431884699)
        ·
          refine ⟨45912460229869245647827049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30608306819912830431884699 45912460229869245647827049)
          ·
            refine ⟨34434345172401934235870287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45912460229869245647827049 34434345172401934235870287)
            ·
              refine ⟨51651517758602901353805431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34434345172401934235870287 51651517758602901353805431)
              ·
                refine ⟨77477276637904352030708147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51651517758602901353805431 77477276637904352030708147)
                ·
                  refine ⟨116215914956856528046062221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77477276637904352030708147 116215914956856528046062221)
                  ·
                    refine ⟨43580968108821198017273333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116215914956856528046062221 43580968108821198017273333)
                    ·
                      refine ⟨4085715760201987314119375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43580968108821198017273333 4085715760201987314119375)
                      ·
                        rfl

theorem cell23_7956903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7956903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956903 prefixEnd_7956903 := by exact prefixLift 7956903
  have htrace : WordTrace (prefixWord ++ tailWord_7956903) baseStart_7956903 baseEnd_7956903 := by
    simpa [prefixWord, tailWord_7956903, baseEnd_7956903] using wordTrace_append hprefix tailTrace_7956903
  have hstable : (prefixWord ++ tailWord_7956903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956903).length < 2 ^ (prefixWord ++ tailWord_7956903).sum := by decide
  have hdescent : baseEnd_7956903 < baseStart_7956903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956904 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_7956904 : Nat := 118140960795 + 7956904 * 2 ^ 59
def prefixEnd_7956904 : Nat := 4983230072969 + 3 ^ 40 * 7956904 * 2
def baseEnd_7956904 : Nat := 4085716273682641810206871

theorem tailTrace_7956904 : CollatzResearch.WordTrace tailWord_7956904 prefixEnd_7956904 4085716273682641810206871 := by
  unfold tailWord_7956904
  simp only [CollatzResearch.WordTrace]
  refine ⟨145106065382751606929142883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193474753843668809238857177 145106065382751606929142883)
  ·
    refine ⟨217659098074127410393714325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145106065382751606929142883 217659098074127410393714325)
    ·
      refine ⟨10202770222224722362205359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217659098074127410393714325 10202770222224722362205359)
      ·
        refine ⟨15304155333337083543308039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10202770222224722362205359 15304155333337083543308039)
        ·
          refine ⟨22956233000005625314962059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15304155333337083543308039 22956233000005625314962059)
          ·
            refine ⟨34434349500008437972443089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22956233000005625314962059 34434349500008437972443089)
            ·
              refine ⟨25825762125006328479332317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34434349500008437972443089 25825762125006328479332317)
              ·
                refine ⟨9684660796877373179749619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25825762125006328479332317 9684660796877373179749619)
                ·
                  refine ⟨14526991195316059769624429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9684660796877373179749619 14526991195316059769624429)
                  ·
                    refine ⟨5447621698243522413609161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14526991195316059769624429 5447621698243522413609161)
                    ·
                      refine ⟨4085716273682641810206871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5447621698243522413609161 4085716273682641810206871)
                      ·
                        rfl

theorem cell23_7956904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_7956904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956904 prefixEnd_7956904 := by exact prefixLift 7956904
  have htrace : WordTrace (prefixWord ++ tailWord_7956904) baseStart_7956904 baseEnd_7956904 := by
    simpa [prefixWord, tailWord_7956904, baseEnd_7956904] using wordTrace_append hprefix tailTrace_7956904
  have hstable : (prefixWord ++ tailWord_7956904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956904).length < 2 ^ (prefixWord ++ tailWord_7956904).sum := by decide
  have hdescent : baseEnd_7956904 < baseStart_7956904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956970 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_7956970 : Nat := 118140960795 + 7956970 * 2 ^ 59
def prefixEnd_7956970 : Nat := 4983230072969 + 3 ^ 40 * 7956970 * 2
def baseEnd_7956970 : Nat := 1361916721135279517327189

theorem tailTrace_7956970 : CollatzResearch.WordTrace tailWord_7956970 prefixEnd_7956970 1361916721135279517327189 := by
  unfold tailWord_7956970
  simp only [CollatzResearch.WordTrace]
  refine ⟨72553634495816026782547091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193476358655509404753458909 72553634495816026782547091)
  ·
    refine ⟨108830451743724040173820637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72553634495816026782547091 108830451743724040173820637)
    ·
      refine ⟨40811419403896515065182739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108830451743724040173820637 40811419403896515065182739)
      ·
        refine ⟨61217129105844772597774109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40811419403896515065182739 61217129105844772597774109)
        ·
          refine ⟨22956423414691789724165291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61217129105844772597774109 22956423414691789724165291)
          ·
            refine ⟨34434635122037684586247937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22956423414691789724165291 34434635122037684586247937)
            ·
              refine ⟨25825976341528263439685953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34434635122037684586247937 25825976341528263439685953)
              ·
                refine ⟨19369482256146197579764465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25825976341528263439685953 19369482256146197579764465)
                ·
                  refine ⟨14527111692109648184823349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19369482256146197579764465 14527111692109648184823349)
                  ·
                    refine ⟨1361916721135279517327189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14527111692109648184823349 1361916721135279517327189)
                    ·
                      rfl

theorem cell23_7956970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_7956970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956970 prefixEnd_7956970 := by exact prefixLift 7956970
  have htrace : WordTrace (prefixWord ++ tailWord_7956970) baseStart_7956970 baseEnd_7956970 := by
    simpa [prefixWord, tailWord_7956970, baseEnd_7956970] using wordTrace_append hprefix tailTrace_7956970
  have hstable : (prefixWord ++ tailWord_7956970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956970).length < 2 ^ (prefixWord ++ tailWord_7956970).sum := by decide
  have hdescent : baseEnd_7956970 < baseStart_7956970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956974 : List Nat := [4, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_7956974 : Nat := 118140960795 + 7956974 * 2 ^ 59
def prefixEnd_7956974 : Nat := 4983230072969 + 3 ^ 40 * 7956974 * 2
def baseEnd_7956974 : Nat := 453972468592050726259061

theorem tailTrace_7956974 : CollatzResearch.WordTrace tailWord_7956974 prefixEnd_7956974 453972468592050726259061 := by
  unfold tailWord_7956974
  simp only [CollatzResearch.WordTrace]
  refine ⟨36276835484406201976666747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193476455916833077208889317 36276835484406201976666747)
  ·
    refine ⟨54415253226609302965000121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36276835484406201976666747 54415253226609302965000121)
    ·
      refine ⟨40811439919956977223750091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54415253226609302965000121 40811439919956977223750091)
      ·
        refine ⟨61217159879935465835625137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40811439919956977223750091 61217159879935465835625137)
        ·
          refine ⟨45912869909951599376718853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61217159879935465835625137 45912869909951599376718853)
          ·
            refine ⟨8608663108115924883134785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45912869909951599376718853 8608663108115924883134785)
            ·
              refine ⟨6456497331086943662351089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8608663108115924883134785 6456497331086943662351089)
              ·
                refine ⟨4842372998315207746763317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6456497331086943662351089 4842372998315207746763317)
                ·
                  refine ⟨453972468592050726259061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4842372998315207746763317 453972468592050726259061)
                  ·
                    rfl

theorem cell23_7956974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_7956974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7956974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7956974 prefixEnd_7956974 := by exact prefixLift 7956974
  have htrace : WordTrace (prefixWord ++ tailWord_7956974) baseStart_7956974 baseEnd_7956974 := by
    simpa [prefixWord, tailWord_7956974, baseEnd_7956974] using wordTrace_append hprefix tailTrace_7956974
  have hstable : (prefixWord ++ tailWord_7956974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956974).length < 2 ^ (prefixWord ++ tailWord_7956974).sum := by decide
  have hdescent : baseEnd_7956974 < baseStart_7956974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957013 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 8]
def baseStart_7957013 : Nat := 118140960795 + 7957013 * 2 ^ 59
def prefixEnd_7957013 : Nat := 4983230072969 + 3 ^ 40 * 7957013 * 2
def baseEnd_7957013 : Nat := 453974693674886875971541

theorem tailTrace_7957013 : CollatzResearch.WordTrace tailWord_7957013 prefixEnd_7957013 453974693674886875971541 := by
  unfold tailWord_7957013
  simp only [CollatzResearch.WordTrace]
  refine ⟨290216106322108325474003693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193477404214738883649335795 290216106322108325474003693)
  ·
    refine ⟨108831039870790622052751385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290216106322108325474003693 108831039870790622052751385)
    ·
      refine ⟨81623279903092966539563539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108831039870790622052751385 81623279903092966539563539)
      ·
        refine ⟨122434919854639449809345309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81623279903092966539563539 122434919854639449809345309)
        ·
          refine ⟨45913094945489793678504491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122434919854639449809345309 45913094945489793678504491)
          ·
            refine ⟨68869642418234690517756737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45913094945489793678504491 68869642418234690517756737)
            ·
              refine ⟨51652231813676017888317553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68869642418234690517756737 51652231813676017888317553)
              ·
                refine ⟨38739173860257013416238165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51652231813676017888317553 38739173860257013416238165)
                ·
                  refine ⟨453974693674886875971541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38739173860257013416238165 453974693674886875971541)
                  ·
                    rfl

theorem cell23_7957013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_7957013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957013 prefixEnd_7957013 := by exact prefixLift 7957013
  have htrace : WordTrace (prefixWord ++ tailWord_7957013) baseStart_7957013 baseEnd_7957013 := by
    simpa [prefixWord, tailWord_7957013, baseEnd_7957013] using wordTrace_append hprefix tailTrace_7957013
  have hstable : (prefixWord ++ tailWord_7957013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957013).length < 2 ^ (prefixWord ++ tailWord_7957013).sum := by decide
  have hdescent : baseEnd_7957013 < baseStart_7957013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957034 : List Nat := [3, 1, 4, 1, 1, 2, 2, 4, 1, 4]
def baseStart_7957034 : Nat := 118140960795 + 7957034 * 2 ^ 59
def prefixEnd_7957034 : Nat := 4983230072969 + 3 ^ 40 * 7957034 * 2
def baseEnd_7957034 : Nat := 1361927675389242100527091

theorem tailTrace_7957034 : CollatzResearch.WordTrace tailWord_7957034 prefixEnd_7957034 1361927675389242100527091 := by
  unfold tailWord_7957034
  simp only [CollatzResearch.WordTrace]
  refine ⟨72554218063758061515129539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193477914836688164040345437 72554218063758061515129539)
  ·
    refine ⟨108831327095637092272694309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72554218063758061515129539 108831327095637092272694309)
    ·
      refine ⟨20405873830431954801130183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108831327095637092272694309 20405873830431954801130183)
      ·
        refine ⟨30608810745647932201695275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20405873830431954801130183 30608810745647932201695275)
        ·
          refine ⟨45913216118471898302542913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30608810745647932201695275 45913216118471898302542913)
          ·
            refine ⟨34434912088853923726907185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45913216118471898302542913 34434912088853923726907185)
            ·
              refine ⟨25826184066640442795180389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34434912088853923726907185 25826184066640442795180389)
              ·
                refine ⟨4842409512495083024096323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25826184066640442795180389 4842409512495083024096323)
                ·
                  refine ⟨7263614268742624536144485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4842409512495083024096323 7263614268742624536144485)
                  ·
                    refine ⟨1361927675389242100527091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7263614268742624536144485 1361927675389242100527091)
                    ·
                      rfl

theorem cell23_7957034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_7957034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957034 prefixEnd_7957034 := by exact prefixLift 7957034
  have htrace : WordTrace (prefixWord ++ tailWord_7957034) baseStart_7957034 baseEnd_7957034 := by
    simpa [prefixWord, tailWord_7957034, baseEnd_7957034] using wordTrace_append hprefix tailTrace_7957034
  have hstable : (prefixWord ++ tailWord_7957034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957034).length < 2 ^ (prefixWord ++ tailWord_7957034).sum := by decide
  have hdescent : baseEnd_7957034 < baseStart_7957034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957091 : List Nat := [1, 1, 1, 5, 1, 2, 5, 2, 1, 1, 3]
def baseStart_7957091 : Nat := 118140960795 + 7957091 * 2 ^ 59
def prefixEnd_7957091 : Nat := 4983230072969 + 3 ^ 40 * 7957091 * 2
def baseEnd_7957091 : Nat := 4085812294565032578568511

theorem tailTrace_7957091 : CollatzResearch.WordTrace tailWord_7957091 prefixEnd_7957091 4085812294565032578568511 := by
  unfold tailWord_7957091
  simp only [CollatzResearch.WordTrace]
  refine ⟨290218951215825744795343127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193479300810550496530228751 290218951215825744795343127)
  ·
    refine ⟨435328426823738617193014691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290218951215825744795343127 435328426823738617193014691)
    ·
      refine ⟨652992640235607925789522037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435328426823738617193014691 652992640235607925789522037)
      ·
        refine ⟨61218060022088243042767691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 652992640235607925789522037 61218060022088243042767691)
        ·
          refine ⟨91827090033132364564151537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61218060022088243042767691 91827090033132364564151537)
          ·
            refine ⟨68870317524849273423113653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91827090033132364564151537 68870317524849273423113653)
            ·
              refine ⟨6456592267954619383416905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68870317524849273423113653 6456592267954619383416905)
              ·
                refine ⟨4842444200965964537562679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6456592267954619383416905 4842444200965964537562679)
                ·
                  refine ⟨7263666301448946806344019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4842444200965964537562679 7263666301448946806344019)
                  ·
                    refine ⟨10895499452173420209516029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7263666301448946806344019 10895499452173420209516029)
                    ·
                      refine ⟨4085812294565032578568511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10895499452173420209516029 4085812294565032578568511)
                      ·
                        rfl

theorem cell23_7957091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_7957091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957091 prefixEnd_7957091 := by exact prefixLift 7957091
  have htrace : WordTrace (prefixWord ++ tailWord_7957091) baseStart_7957091 baseEnd_7957091 := by
    simpa [prefixWord, tailWord_7957091, baseEnd_7957091] using wordTrace_append hprefix tailTrace_7957091
  have hstable : (prefixWord ++ tailWord_7957091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957091).length < 2 ^ (prefixWord ++ tailWord_7957091).sum := by decide
  have hdescent : baseEnd_7957091 < baseStart_7957091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957100 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_7957100 : Nat := 118140960795 + 7957100 * 2 ^ 59
def prefixEnd_7957100 : Nat := 4983230072969 + 3 ^ 40 * 7957100 * 2
def baseEnd_7957100 : Nat := 4085816915890923043355969

theorem tailTrace_7957100 : CollatzResearch.WordTrace tailWord_7957100 prefixEnd_7957100 4085816915890923043355969 := by
  unfold tailWord_7957100
  simp only [CollatzResearch.WordTrace]
  refine ⟨145109639736396569666210377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193479519648528759554947169 145109639736396569666210377)
  ·
    refine ⟨108832229802297427249657783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145109639736396569666210377 108832229802297427249657783)
    ·
      refine ⟨163248344703446140874486675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108832229802297427249657783 163248344703446140874486675)
      ·
        refine ⟨244872517055169211311730013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163248344703446140874486675 244872517055169211311730013)
        ·
          refine ⟨91827193895688454241898755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244872517055169211311730013 91827193895688454241898755)
          ·
            refine ⟨137740790843532681362848133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91827193895688454241898755 137740790843532681362848133)
            ·
              refine ⟨25826398283162377755534025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137740790843532681362848133 25826398283162377755534025)
              ·
                refine ⟨19369798712371783316650519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25826398283162377755534025 19369798712371783316650519)
                ·
                  refine ⟨29054698068557674974975779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19369798712371783316650519 29054698068557674974975779)
                  ·
                    refine ⟨43582047102836512462463669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29054698068557674974975779 43582047102836512462463669)
                    ·
                      refine ⟨4085816915890923043355969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43582047102836512462463669 4085816915890923043355969)
                      ·
                        rfl

theorem cell23_7957100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_7957100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957100 prefixEnd_7957100 := by exact prefixLift 7957100
  have htrace : WordTrace (prefixWord ++ tailWord_7957100) baseStart_7957100 baseEnd_7957100 := by
    simpa [prefixWord, tailWord_7957100, baseEnd_7957100] using wordTrace_append hprefix tailTrace_7957100
  have hstable : (prefixWord ++ tailWord_7957100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957100).length < 2 ^ (prefixWord ++ tailWord_7957100).sum := by decide
  have hdescent : baseEnd_7957100 < baseStart_7957100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957103 : List Nat := [1, 1, 2, 1, 3, 2, 3, 10]
def baseStart_7957103 : Nat := 118140960795 + 7957103 * 2 ^ 59
def prefixEnd_7957103 : Nat := 4983230072969 + 3 ^ 40 * 7957103 * 2
def baseEnd_7957103 : Nat := 151326609493810612282165

theorem tailTrace_7957103 : CollatzResearch.WordTrace tailWord_7957103 prefixEnd_7957103 151326609493810612282165 := by
  unfold tailWord_7957103
  simp only [CollatzResearch.WordTrace]
  refine ⟨290219388891782270844779963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193479592594521513896519975 290219388891782270844779963)
  ·
    refine ⟨435329083337673406267169945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290219388891782270844779963 435329083337673406267169945)
    ·
      refine ⟨326496812503255054700377459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435329083337673406267169945 326496812503255054700377459)
      ·
        refine ⟨489745218754882582050566189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326496812503255054700377459 489745218754882582050566189)
        ·
          refine ⟨183654457033080968268962321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489745218754882582050566189 183654457033080968268962321)
          ·
            refine ⟨137740842774810726201721741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183654457033080968268962321 137740842774810726201721741)
            ·
              refine ⟨51652816040554022325645653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137740842774810726201721741 51652816040554022325645653)
              ·
                refine ⟨151326609493810612282165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51652816040554022325645653 151326609493810612282165)
                ·
                  rfl

theorem cell23_7957103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 10].length) (baseStart_7957103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957103 prefixEnd_7957103 := by exact prefixLift 7957103
  have htrace : WordTrace (prefixWord ++ tailWord_7957103) baseStart_7957103 baseEnd_7957103 := by
    simpa [prefixWord, tailWord_7957103, baseEnd_7957103] using wordTrace_append hprefix tailTrace_7957103
  have hstable : (prefixWord ++ tailWord_7957103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957103).length < 2 ^ (prefixWord ++ tailWord_7957103).sum := by decide
  have hdescent : baseEnd_7957103 < baseStart_7957103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957148 : List Nat := [2, 2, 3, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_7957148 : Nat := 118140960795 + 7957148 * 2 ^ 59
def prefixEnd_7957148 : Nat := 4983230072969 + 3 ^ 40 * 7957148 * 2
def baseEnd_7957148 : Nat := 4085841562962338855555749

theorem tailTrace_7957148 : CollatzResearch.WordTrace tailWord_7957148 prefixEnd_7957148 4085841562962338855555749 := by
  unfold tailWord_7957148
  simp only [CollatzResearch.WordTrace]
  refine ⟨145110515088309621765084049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193480686784412829020112065 145110515088309621765084049)
  ·
    refine ⟨108832886316232216323813037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145110515088309621765084049 108832886316232216323813037)
    ·
      refine ⟨40812332368587081121429889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108832886316232216323813037 40812332368587081121429889)
      ·
        refine ⟨30609249276440310841072417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40812332368587081121429889 30609249276440310841072417)
        ·
          refine ⟨22956936957330233130804313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30609249276440310841072417 22956936957330233130804313)
          ·
            refine ⟨17217702717997674848103235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22956936957330233130804313 17217702717997674848103235)
            ·
              refine ⟨25826554076996512272154853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17217702717997674848103235 25826554076996512272154853)
              ·
                refine ⟨4842478889436846051029035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25826554076996512272154853 4842478889436846051029035)
                ·
                  refine ⟨7263718334155269076543553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4842478889436846051029035 7263718334155269076543553)
                  ·
                    refine ⟨5447788750616451807407665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7263718334155269076543553 5447788750616451807407665)
                    ·
                      refine ⟨4085841562962338855555749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5447788750616451807407665 4085841562962338855555749)
                      ·
                        rfl

theorem cell23_7957148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_7957148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957148 prefixEnd_7957148 := by exact prefixLift 7957148
  have htrace : WordTrace (prefixWord ++ tailWord_7957148) baseStart_7957148 baseEnd_7957148 := by
    simpa [prefixWord, tailWord_7957148, baseEnd_7957148] using wordTrace_append hprefix tailTrace_7957148
  have hstable : (prefixWord ++ tailWord_7957148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957148).length < 2 ^ (prefixWord ++ tailWord_7957148).sum := by decide
  have hdescent : baseEnd_7957148 < baseStart_7957148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957170 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_7957170 : Nat := 118140960795 + 7957170 * 2 ^ 59
def prefixEnd_7957170 : Nat := 4983230072969 + 3 ^ 40 * 7957170 * 2
def baseEnd_7957170 : Nat := 4085852859536737769480647

theorem tailTrace_7957170 : CollatzResearch.WordTrace tailWord_7957170 prefixEnd_7957170 4085852859536737769480647 := by
  unfold tailWord_7957170
  simp only [CollatzResearch.WordTrace]
  refine ⟨72555458145634885321867241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193481221721693027524979309 72555458145634885321867241)
  ·
    refine ⟨54416593609226163991400431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72555458145634885321867241 54416593609226163991400431)
    ·
      refine ⟨81624890413839245987100647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54416593609226163991400431 81624890413839245987100647)
      ·
        refine ⟨122437335620758868980650971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81624890413839245987100647 122437335620758868980650971)
        ·
          refine ⟨183656003431138303470976457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122437335620758868980650971 183656003431138303470976457)
          ·
            refine ⟨137742002573353727603232343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183656003431138303470976457 137742002573353727603232343)
            ·
              refine ⟨206613003860030591404848515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137742002573353727603232343 206613003860030591404848515)
              ·
                refine ⟨309919505790045887107272773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206613003860030591404848515 309919505790045887107272773)
                ·
                  refine ⟨58109907335633603832613645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309919505790045887107272773 58109907335633603832613645)
                  ·
                    refine ⟨21791215250862601437230117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58109907335633603832613645 21791215250862601437230117)
                    ·
                      refine ⟨4085852859536737769480647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21791215250862601437230117 4085852859536737769480647)
                      ·
                        rfl

theorem cell23_7957170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_7957170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957170 prefixEnd_7957170 := by exact prefixLift 7957170
  have htrace : WordTrace (prefixWord ++ tailWord_7957170) baseStart_7957170 baseEnd_7957170 := by
    simpa [prefixWord, tailWord_7957170, baseEnd_7957170] using wordTrace_append hprefix tailTrace_7957170
  have hstable : (prefixWord ++ tailWord_7957170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957170).length < 2 ^ (prefixWord ++ tailWord_7957170).sum := by decide
  have hdescent : baseEnd_7957170 < baseStart_7957170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957180 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_7957180 : Nat := 118140960795 + 7957180 * 2 ^ 59
def prefixEnd_7957180 : Nat := 4983230072969 + 3 ^ 40 * 7957180 * 2
def baseEnd_7957180 : Nat := 1361952664781094243451867

theorem tailTrace_7957180 : CollatzResearch.WordTrace tailWord_7957180 prefixEnd_7957180 1361952664781094243451867 := by
  unfold tailWord_7957180
  simp only [CollatzResearch.WordTrace]
  refine ⟨145111098656251656497666497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193481464875002208663555329 145111098656251656497666497)
  ·
    refine ⟨108833323992188742373249873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145111098656251656497666497 108833323992188742373249873)
    ·
      refine ⟨81624992994141556779937405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108833323992188742373249873 81624992994141556779937405)
      ·
        refine ⟨30609372372803083792476527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81624992994141556779937405 30609372372803083792476527)
        ·
          refine ⟨45914058559204625688714791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30609372372803083792476527 45914058559204625688714791)
          ·
            refine ⟨68871087838806938533072187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45914058559204625688714791 68871087838806938533072187)
            ·
              refine ⟨103306631758210407799608281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68871087838806938533072187 103306631758210407799608281)
              ·
                refine ⟨77479973818657805849706211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103306631758210407799608281 77479973818657805849706211)
                ·
                  refine ⟨116219960727986708774559317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77479973818657805849706211 116219960727986708774559317)
                  ·
                    refine ⟨1361952664781094243451867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116219960727986708774559317 1361952664781094243451867)
                    ·
                      rfl

theorem cell23_7957180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_7957180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957180 prefixEnd_7957180 := by exact prefixLift 7957180
  have htrace : WordTrace (prefixWord ++ tailWord_7957180) baseStart_7957180 baseEnd_7957180 := by
    simpa [prefixWord, tailWord_7957180, baseEnd_7957180] using wordTrace_append hprefix tailTrace_7957180
  have hstable : (prefixWord ++ tailWord_7957180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957180).length < 2 ^ (prefixWord ++ tailWord_7957180).sum := by decide
  have hdescent : baseEnd_7957180 < baseStart_7957180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957185 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7957185 : Nat := 118140960795 + 7957185 * 2 ^ 59
def prefixEnd_7957185 : Nat := 4983230072969 + 3 ^ 40 * 7957185 * 2
def baseEnd_7957185 : Nat := 4085860561746555210793079

theorem tailTrace_7957185 : CollatzResearch.WordTrace tailWord_7957185 prefixEnd_7957185 4085860561746555210793079 := by
  unfold tailWord_7957185
  simp only [CollatzResearch.WordTrace]
  refine ⟨290222379677485198849265009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193481586451656799232843339 290222379677485198849265009)
  ·
    refine ⟨217666784758113899136948757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290222379677485198849265009 217666784758113899136948757)
    ·
      refine ⟨10203130535536589022044473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217666784758113899136948757 10203130535536589022044473)
      ·
        refine ⟨7652347901652441766533355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10203130535536589022044473 7652347901652441766533355)
        ·
          refine ⟨11478521852478662649800033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7652347901652441766533355 11478521852478662649800033)
          ·
            refine ⟨8608891389358996987350025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11478521852478662649800033 8608891389358996987350025)
            ·
              refine ⟨6456668542019247740512519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8608891389358996987350025 6456668542019247740512519)
              ·
                refine ⟨9685002813028871610768779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6456668542019247740512519 9685002813028871610768779)
                ·
                  refine ⟨14527504219543307416153169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9685002813028871610768779 14527504219543307416153169)
                  ·
                    refine ⟨10895628164657480562114877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14527504219543307416153169 10895628164657480562114877)
                    ·
                      refine ⟨4085860561746555210793079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10895628164657480562114877 4085860561746555210793079)
                      ·
                        rfl

theorem cell23_7957185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7957185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957185 prefixEnd_7957185 := by exact prefixLift 7957185
  have htrace : WordTrace (prefixWord ++ tailWord_7957185) baseStart_7957185 baseEnd_7957185 := by
    simpa [prefixWord, tailWord_7957185, baseEnd_7957185] using wordTrace_append hprefix tailTrace_7957185
  have hstable : (prefixWord ++ tailWord_7957185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957185).length < 2 ^ (prefixWord ++ tailWord_7957185).sum := by decide
  have hdescent : baseEnd_7957185 < baseStart_7957185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957217 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_7957217 : Nat := 118140960795 + 7957217 * 2 ^ 59
def prefixEnd_7957217 : Nat := 4983230072969 + 3 ^ 40 * 7957217 * 2
def baseEnd_7957217 : Nat := 4085876993127499085592931

theorem tailTrace_7957217 : CollatzResearch.WordTrace tailWord_7957217 prefixEnd_7957217 4085876993127499085592931 := by
  unfold tailWord_7957217
  simp only [CollatzResearch.WordTrace]
  refine ⟨290223546813369268314429905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193482364542246178876286603 290223546813369268314429905)
  ·
    refine ⟨217667660110026951235822429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290223546813369268314429905 217667660110026951235822429)
    ·
      refine ⟨81625372541260106713433411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217667660110026951235822429 81625372541260106713433411)
      ·
        refine ⟨122438058811890160070150117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81625372541260106713433411 122438058811890160070150117)
        ·
          refine ⟨22957136027229405013153147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122438058811890160070150117 22957136027229405013153147)
          ·
            refine ⟨34435704040844107519729721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22957136027229405013153147 34435704040844107519729721)
            ·
              refine ⟨25826778030633080639797291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34435704040844107519729721 25826778030633080639797291)
              ·
                refine ⟨38740167045949620959695937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25826778030633080639797291 38740167045949620959695937)
                ·
                  refine ⟨29055125284462215719771953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38740167045949620959695937 29055125284462215719771953)
                  ·
                    refine ⟨21791343963346661789828965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29055125284462215719771953 21791343963346661789828965)
                    ·
                      refine ⟨4085876993127499085592931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21791343963346661789828965 4085876993127499085592931)
                      ·
                        rfl

theorem cell23_7957217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_7957217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957217 prefixEnd_7957217 := by exact prefixLift 7957217
  have htrace : WordTrace (prefixWord ++ tailWord_7957217) baseStart_7957217 baseEnd_7957217 := by
    simpa [prefixWord, tailWord_7957217, baseEnd_7957217] using wordTrace_append hprefix tailTrace_7957217
  have hstable : (prefixWord ++ tailWord_7957217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957217).length < 2 ^ (prefixWord ++ tailWord_7957217).sum := by decide
  have hdescent : baseEnd_7957217 < baseStart_7957217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957221 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 1, 4, 2]
def baseStart_7957221 : Nat := 118140960795 + 7957221 * 2 ^ 59
def prefixEnd_7957221 : Nat := 4983230072969 + 3 ^ 40 * 7957221 * 2
def baseEnd_7957221 : Nat := 4085879047050117069942913

theorem tailTrace_7957221 : CollatzResearch.WordTrace tailWord_7957221 prefixEnd_7957221 4085879047050117069942913 := by
  unfold tailWord_7957221
  simp only [CollatzResearch.WordTrace]
  refine ⟨290223692705354776997575517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193482461803569851331717011 290223692705354776997575517)
  ·
    refine ⟨108833884764508041374090819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290223692705354776997575517 108833884764508041374090819)
    ·
      refine ⟨163250827146762062061136229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108833884764508041374090819 163250827146762062061136229)
      ·
        refine ⟨30609530090017886636463043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163250827146762062061136229 30609530090017886636463043)
        ·
          refine ⟨45914295135026829954694565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30609530090017886636463043 45914295135026829954694565)
          ·
            refine ⟨8608930337817530616505231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45914295135026829954694565 8608930337817530616505231)
            ·
              refine ⟨12913395506726295924757847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8608930337817530616505231 12913395506726295924757847)
              ·
                refine ⟨19370093260089443887136771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12913395506726295924757847 19370093260089443887136771)
                ·
                  refine ⟨29055139890134165830705157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19370093260089443887136771 29055139890134165830705157)
                  ·
                    refine ⟨5447838729400156093257217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29055139890134165830705157 5447838729400156093257217)
                    ·
                      refine ⟨4085879047050117069942913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5447838729400156093257217 4085879047050117069942913)
                      ·
                        rfl

theorem cell23_7957221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_7957221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957221 prefixEnd_7957221 := by exact prefixLift 7957221
  have htrace : WordTrace (prefixWord ++ tailWord_7957221) baseStart_7957221 baseEnd_7957221 := by
    simpa [prefixWord, tailWord_7957221, baseEnd_7957221] using wordTrace_append hprefix tailTrace_7957221
  have hstable : (prefixWord ++ tailWord_7957221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957221).length < 2 ^ (prefixWord ++ tailWord_7957221).sum := by decide
  have hdescent : baseEnd_7957221 < baseStart_7957221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957240 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 1, 7]
def baseStart_7957240 : Nat := 118140960795 + 7957240 * 2 ^ 59
def prefixEnd_7957240 : Nat := 4983230072969 + 3 ^ 40 * 7957240 * 2
def baseEnd_7957240 : Nat := 1361962934394184165201775

theorem tailTrace_7957240 : CollatzResearch.WordTrace tailWord_7957240 prefixEnd_7957240 1361962934394184165201775 := by
  unfold tailWord_7957240
  simp only [CollatzResearch.WordTrace]
  refine ⟨145112192846142971621258587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193482923794857295495011449 145112192846142971621258587)
  ·
    refine ⟨217668289269214457431887881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145112192846142971621258587 217668289269214457431887881)
    ·
      refine ⟨163251216951910843073915911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217668289269214457431887881 163251216951910843073915911)
      ·
        refine ⟨244876825427866264610873867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163251216951910843073915911 244876825427866264610873867)
        ·
          refine ⟨367315238141799396916310801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244876825427866264610873867 367315238141799396916310801)
          ·
            refine ⟨275486428606349547687233101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367315238141799396916310801 275486428606349547687233101)
            ·
              refine ⟨103307410727381080382712413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275486428606349547687233101 103307410727381080382712413)
              ·
                refine ⟨38740279022767905143517155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103307410727381080382712413 38740279022767905143517155)
                ·
                  refine ⟨58110418534151857715275733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38740279022767905143517155 58110418534151857715275733)
                  ·
                    refine ⟨1361962934394184165201775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58110418534151857715275733 1361962934394184165201775)
                    ·
                      rfl

theorem cell23_7957240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_7957240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957240 prefixEnd_7957240 := by exact prefixLift 7957240
  have htrace : WordTrace (prefixWord ++ tailWord_7957240) baseStart_7957240 baseEnd_7957240 := by
    simpa [prefixWord, tailWord_7957240, baseEnd_7957240] using wordTrace_append hprefix tailTrace_7957240
  have hstable : (prefixWord ++ tailWord_7957240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957240).length < 2 ^ (prefixWord ++ tailWord_7957240).sum := by decide
  have hdescent : baseEnd_7957240 < baseStart_7957240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957244 : List Nat := [2, 2, 2, 1, 3, 2, 3, 3, 5]
def baseStart_7957244 : Nat := 118140960795 + 7957244 * 2 ^ 59
def prefixEnd_7957244 : Nat := 4983230072969 + 3 ^ 40 * 7957244 * 2
def baseEnd_7957244 : Nat := 453987873011685608883923

theorem tailTrace_7957244 : CollatzResearch.WordTrace tailWord_7957244 prefixEnd_7957244 453987873011685608883923 := by
  unfold tailWord_7957244
  simp only [CollatzResearch.WordTrace]
  refine ⟨145112265792135725962831393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193483021056180967950441857 145112265792135725962831393)
  ·
    refine ⟨108834199344101794472123545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145112265792135725962831393 108834199344101794472123545)
    ·
      refine ⟨81625649508076345854092659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108834199344101794472123545 81625649508076345854092659)
      ·
        refine ⟨122438474262114518781138989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81625649508076345854092659 122438474262114518781138989)
        ·
          refine ⟨45914427848292944542927121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122438474262114518781138989 45914427848292944542927121)
          ·
            refine ⟨34435820886219708407195341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45914427848292944542927121 34435820886219708407195341)
            ·
              refine ⟨12913432832332390652698253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34435820886219708407195341 12913432832332390652698253)
              ·
                refine ⟨4842537312124646494761845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12913432832332390652698253 4842537312124646494761845)
                ·
                  refine ⟨453987873011685608883923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4842537312124646494761845 453987873011685608883923)
                  ·
                    rfl

theorem cell23_7957244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_7957244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957244 prefixEnd_7957244 := by exact prefixLift 7957244
  have htrace : WordTrace (prefixWord ++ tailWord_7957244) baseStart_7957244 baseEnd_7957244 := by
    simpa [prefixWord, tailWord_7957244, baseEnd_7957244] using wordTrace_append hprefix tailTrace_7957244
  have hstable : (prefixWord ++ tailWord_7957244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957244).length < 2 ^ (prefixWord ++ tailWord_7957244).sum := by decide
  have hdescent : baseEnd_7957244 < baseStart_7957244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957247 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 1, 7, 2]
def baseStart_7957247 : Nat := 118140960795 + 7957247 * 2 ^ 59
def prefixEnd_7957247 : Nat := 4983230072969 + 3 ^ 40 * 7957247 * 2
def baseEnd_7957247 : Nat := 4085892397547133968217793

theorem tailTrace_7957247 : CollatzResearch.WordTrace tailWord_7957247 prefixEnd_7957247 4085892397547133968217793 := by
  unfold tailWord_7957247
  simp only [CollatzResearch.WordTrace]
  refine ⟨290224641003260583438021995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193483094002173722292014663 290224641003260583438021995)
  ·
    refine ⟨435336961504890875157032993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290224641003260583438021995 435336961504890875157032993)
    ·
      refine ⟨326502721128668156367774745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435336961504890875157032993 326502721128668156367774745)
      ·
        refine ⟨244877040846501117275831059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326502721128668156367774745 244877040846501117275831059)
        ·
          refine ⟨367315561269751675913746589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244877040846501117275831059 367315561269751675913746589)
          ·
            refine ⟨137743335476156878467654971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367315561269751675913746589 137743335476156878467654971)
            ·
              refine ⟨206615003214235317701482457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137743335476156878467654971 206615003214235317701482457)
              ·
                refine ⟨154961252410676488276111843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206615003214235317701482457 154961252410676488276111843)
                ·
                  refine ⟨232441878616014732414167765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154961252410676488276111843 232441878616014732414167765)
                  ·
                    refine ⟨5447856530062845290957057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232441878616014732414167765 5447856530062845290957057)
                    ·
                      refine ⟨4085892397547133968217793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5447856530062845290957057 4085892397547133968217793)
                      ·
                        rfl

theorem cell23_7957247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_7957247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957247 prefixEnd_7957247 := by exact prefixLift 7957247
  have htrace : WordTrace (prefixWord ++ tailWord_7957247) baseStart_7957247 baseEnd_7957247 := by
    simpa [prefixWord, tailWord_7957247, baseEnd_7957247] using wordTrace_append hprefix tailTrace_7957247
  have hstable : (prefixWord ++ tailWord_7957247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957247).length < 2 ^ (prefixWord ++ tailWord_7957247).sum := by decide
  have hdescent : baseEnd_7957247 < baseStart_7957247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957321 : List Nat := [1, 2, 1, 1, 2, 6, 1, 4, 1, 4]
def baseStart_7957321 : Nat := 118140960795 + 7957321 * 2 ^ 59
def prefixEnd_7957321 : Nat := 4983230072969 + 3 ^ 40 * 7957321 * 2
def baseEnd_7957321 : Nat := 1361976798371855559564151

theorem tailTrace_7957321 : CollatzResearch.WordTrace tailWord_7957321 prefixEnd_7957321 1361976798371855559564151 := by
  unfold tailWord_7957321
  simp only [CollatzResearch.WordTrace]
  refine ⟨290227340004992494076215817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193484893336661662717477211 290227340004992494076215817)
  ·
    refine ⟨217670505003744370557161863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290227340004992494076215817 217670505003744370557161863)
    ·
      refine ⟨326505757505616555835742795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217670505003744370557161863 326505757505616555835742795)
      ·
        refine ⟨489758636258424833753614193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326505757505616555835742795 489758636258424833753614193)
        ·
          refine ⟨367318977193818625315210645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489758636258424833753614193 367318977193818625315210645)
          ·
            refine ⟨17218077055960248061650499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 367318977193818625315210645 17218077055960248061650499)
            ·
              refine ⟨25827115583940372092475749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17218077055960248061650499 25827115583940372092475749)
              ·
                refine ⟨4842584171988819767339203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25827115583940372092475749 4842584171988819767339203)
                ·
                  refine ⟨7263876257983229651008805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4842584171988819767339203 7263876257983229651008805)
                  ·
                    refine ⟨1361976798371855559564151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7263876257983229651008805 1361976798371855559564151)
                    ·
                      rfl

theorem cell23_7957321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 1, 4].length) (baseStart_7957321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957321 prefixEnd_7957321 := by exact prefixLift 7957321
  have htrace : WordTrace (prefixWord ++ tailWord_7957321) baseStart_7957321 baseEnd_7957321 := by
    simpa [prefixWord, tailWord_7957321, baseEnd_7957321] using wordTrace_append hprefix tailTrace_7957321
  have hstable : (prefixWord ++ tailWord_7957321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957321).length < 2 ^ (prefixWord ++ tailWord_7957321).sum := by decide
  have hdescent : baseEnd_7957321 < baseStart_7957321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957357 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_7957357 : Nat := 118140960795 + 7957357 * 2 ^ 59
def prefixEnd_7957357 : Nat := 4983230072969 + 3 ^ 40 * 7957357 * 2
def baseEnd_7957357 : Nat := 4085948880419128537842287

theorem tailTrace_7957357 : CollatzResearch.WordTrace tailWord_7957357 prefixEnd_7957357 4085948880419128537842287 := by
  unfold tailWord_7957357
  simp only [CollatzResearch.WordTrace]
  refine ⟨290228653032862072224526325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193485768688574714816350883 290228653032862072224526325)
  ·
    refine ⟨27208936221830819271049343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 290228653032862072224526325 27208936221830819271049343)
    ·
      refine ⟨40813404332746228906574015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27208936221830819271049343 40813404332746228906574015)
      ·
        refine ⟨61220106499119343359861023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40813404332746228906574015 61220106499119343359861023)
        ·
          refine ⟨91830159748679015039791535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61220106499119343359861023 91830159748679015039791535)
          ·
            refine ⟨137745239623018522559687303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91830159748679015039791535 137745239623018522559687303)
            ·
              refine ⟨206617859434527783839530955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137745239623018522559687303 206617859434527783839530955)
              ·
                refine ⟨309926789151791675759296433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206617859434527783839530955 309926789151791675759296433)
                ·
                  refine ⟨232445091863843756819472325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309926789151791675759296433 232445091863843756819472325)
                  ·
                    refine ⟨43583454724470704403651061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 232445091863843756819472325 43583454724470704403651061)
                    ·
                      refine ⟨4085948880419128537842287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43583454724470704403651061 4085948880419128537842287)
                      ·
                        rfl

theorem cell23_7957357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_7957357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957357 prefixEnd_7957357 := by exact prefixLift 7957357
  have htrace : WordTrace (prefixWord ++ tailWord_7957357) baseStart_7957357 baseEnd_7957357 := by
    simpa [prefixWord, tailWord_7957357, baseEnd_7957357] using wordTrace_append hprefix tailTrace_7957357
  have hstable : (prefixWord ++ tailWord_7957357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957357).length < 2 ^ (prefixWord ++ tailWord_7957357).sum := by decide
  have hdescent : baseEnd_7957357 < baseStart_7957357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957387 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 5]
def baseStart_7957387 : Nat := 118140960795 + 7957387 * 2 ^ 59
def prefixEnd_7957387 : Nat := 4983230072969 + 3 ^ 40 * 7957387 * 2
def baseEnd_7957387 : Nat := 4085964284838763420467149

theorem tailTrace_7957387 : CollatzResearch.WordTrace tailWord_7957387 prefixEnd_7957387 4085964284838763420467149 := by
  unfold tailWord_7957387
  simp only [CollatzResearch.WordTrace]
  refine ⟨290229747222753387348118415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193486498148502258232078943 290229747222753387348118415)
  ·
    refine ⟨435344620834130081022177623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290229747222753387348118415 435344620834130081022177623)
    ·
      refine ⟨653016931251195121533266435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435344620834130081022177623 653016931251195121533266435)
      ·
        refine ⟨979525396876792682299899653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653016931251195121533266435 979525396876792682299899653)
        ·
          refine ⟨183661011914398627931231185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 979525396876792682299899653 183661011914398627931231185)
          ·
            refine ⟨137745758935798970948423389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183661011914398627931231185 137745758935798970948423389)
            ·
              refine ⟨51654659600924614105658771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137745758935798970948423389 51654659600924614105658771)
              ·
                refine ⟨77481989401386921158488157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51654659600924614105658771 77481989401386921158488157)
                ·
                  refine ⟨29055746025520095434433059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77481989401386921158488157 29055746025520095434433059)
                  ·
                    refine ⟨43583619038280143151649589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29055746025520095434433059 43583619038280143151649589)
                    ·
                      refine ⟨4085964284838763420467149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43583619038280143151649589 4085964284838763420467149)
                      ·
                        rfl

theorem cell23_7957387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 5].length) (baseStart_7957387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957387 prefixEnd_7957387 := by exact prefixLift 7957387
  have htrace : WordTrace (prefixWord ++ tailWord_7957387) baseStart_7957387 baseEnd_7957387 := by
    simpa [prefixWord, tailWord_7957387, baseEnd_7957387] using wordTrace_append hprefix tailTrace_7957387
  have hstable : (prefixWord ++ tailWord_7957387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957387).length < 2 ^ (prefixWord ++ tailWord_7957387).sum := by decide
  have hdescent : baseEnd_7957387 < baseStart_7957387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957428 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_7957428 : Nat := 118140960795 + 7957428 * 2 ^ 59
def prefixEnd_7957428 : Nat := 4983230072969 + 3 ^ 40 * 7957428 * 2
def baseEnd_7957428 : Nat := 1361995112515199253351487

theorem tailTrace_7957428 : CollatzResearch.WordTrace tailWord_7957428 prefixEnd_7957428 1361995112515199253351487 := by
  unfold tailWord_7957428
  simp only [CollatzResearch.WordTrace]
  refine ⟨145115621307802425675180469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193487495077069900900240625 145115621307802425675180469)
  ·
    refine ⟨13604589497606477407048169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145115621307802425675180469 13604589497606477407048169)
    ·
      refine ⟨10203442123204858055286127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13604589497606477407048169 10203442123204858055286127)
      ·
        refine ⟨15305163184807287082929191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10203442123204858055286127 15305163184807287082929191)
        ·
          refine ⟨22957744777210930624393787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15305163184807287082929191 22957744777210930624393787)
          ·
            refine ⟨34436617165816395936590681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22957744777210930624393787 34436617165816395936590681)
            ·
              refine ⟨25827462874362296952443011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34436617165816395936590681 25827462874362296952443011)
              ·
                refine ⟨38741194311543445428664517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25827462874362296952443011 38741194311543445428664517)
                ·
                  refine ⟨7263973933414396017874597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38741194311543445428664517 7263973933414396017874597)
                  ·
                    refine ⟨1361995112515199253351487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7263973933414396017874597 1361995112515199253351487)
                    ·
                      rfl

theorem cell23_7957428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_7957428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957428 prefixEnd_7957428 := by exact prefixLift 7957428
  have htrace : WordTrace (prefixWord ++ tailWord_7957428) baseStart_7957428 baseEnd_7957428 := by
    simpa [prefixWord, tailWord_7957428, baseEnd_7957428] using wordTrace_append hprefix tailTrace_7957428
  have hstable : (prefixWord ++ tailWord_7957428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957428).length < 2 ^ (prefixWord ++ tailWord_7957428).sum := by decide
  have hdescent : baseEnd_7957428 < baseStart_7957428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957486 : List Nat := [4, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_7957486 : Nat := 118140960795 + 7957486 * 2 ^ 59
def prefixEnd_7957486 : Nat := 4983230072969 + 3 ^ 40 * 7957486 * 2
def baseEnd_7957486 : Nat := 4086015119423558533129195

theorem tailTrace_7957486 : CollatzResearch.WordTrace tailWord_7957486 prefixEnd_7957486 4086015119423558533129195 := by
  unfold tailWord_7957486
  simp only [CollatzResearch.WordTrace]
  refine ⟨36279169756174340906996539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193488905366263151503981541 36279169756174340906996539)
  ·
    refine ⟨54418754634261511360494809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36279169756174340906996539 54418754634261511360494809)
    ·
      refine ⟨40814065975696133520371107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54418754634261511360494809 40814065975696133520371107)
      ·
        refine ⟨61221098963544200280556661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40814065975696133520371107 61221098963544200280556661)
        ·
          refine ⟨5739478027832268776302187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61221098963544200280556661 5739478027832268776302187)
          ·
            refine ⟨8609217041748403164453281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739478027832268776302187 8609217041748403164453281)
            ·
              refine ⟨6456912781311302373339961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8609217041748403164453281 6456912781311302373339961)
              ·
                refine ⟨4842684585983476780004971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6456912781311302373339961 4842684585983476780004971)
                ·
                  refine ⟨7264026878975215170007457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4842684585983476780004971 7264026878975215170007457)
                  ·
                    refine ⟨5448020159231411377505593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7264026878975215170007457 5448020159231411377505593)
                    ·
                      refine ⟨4086015119423558533129195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448020159231411377505593 4086015119423558533129195)
                      ·
                        rfl

theorem cell23_7957486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_7957486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957486 prefixEnd_7957486 := by exact prefixLift 7957486
  have htrace : WordTrace (prefixWord ++ tailWord_7957486) baseStart_7957486 baseEnd_7957486 := by
    simpa [prefixWord, tailWord_7957486, baseEnd_7957486] using wordTrace_append hprefix tailTrace_7957486
  have hstable : (prefixWord ++ tailWord_7957486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957486).length < 2 ^ (prefixWord ++ tailWord_7957486).sum := by decide
  have hdescent : baseEnd_7957486 < baseStart_7957486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957492 : List Nat := [2, 6, 2, 1, 1, 2, 1, 8]
def baseStart_7957492 : Nat := 118140960795 + 7957492 * 2 ^ 59
def prefixEnd_7957492 : Nat := 4983230072969 + 3 ^ 40 * 7957492 * 2
def baseEnd_7957492 : Nat := 151334007418795759616821

theorem tailTrace_7957492 : CollatzResearch.WordTrace tailWord_7957492 prefixEnd_7957492 151334007418795759616821 := by
  unfold tailWord_7957492
  simp only [CollatzResearch.WordTrace]
  refine ⟨145116788443686495140345365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193489051258248660187127153 145116788443686495140345365)
  ·
    refine ⟨6802349458297804459703689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145116788443686495140345365 6802349458297804459703689)
    ·
      refine ⟨5101762093723353344777767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6802349458297804459703689 5101762093723353344777767)
      ·
        refine ⟨7652643140585030017166651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5101762093723353344777767 7652643140585030017166651)
        ·
          refine ⟨11478964710877545025749977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7652643140585030017166651 11478964710877545025749977)
          ·
            refine ⟨8609223533158158769312483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11478964710877545025749977 8609223533158158769312483)
            ·
              refine ⟨12913835299737238153968725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609223533158158769312483 12913835299737238153968725)
              ·
                refine ⟨151334007418795759616821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12913835299737238153968725 151334007418795759616821)
                ·
                  rfl

theorem cell23_7957492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 8].length) (baseStart_7957492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957492 prefixEnd_7957492 := by exact prefixLift 7957492
  have htrace : WordTrace (prefixWord ++ tailWord_7957492) baseStart_7957492 baseEnd_7957492 := by
    simpa [prefixWord, tailWord_7957492, baseEnd_7957492] using wordTrace_append hprefix tailTrace_7957492
  have hstable : (prefixWord ++ tailWord_7957492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957492).length < 2 ^ (prefixWord ++ tailWord_7957492).sum := by decide
  have hdescent : baseEnd_7957492 < baseStart_7957492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957514 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 9]
def baseStart_7957514 : Nat := 118140960795 + 7957514 * 2 ^ 59
def prefixEnd_7957514 : Nat := 4983230072969 + 3 ^ 40 * 7957514 * 2
def baseEnd_7957514 : Nat := 454003277431320491508785

theorem tailTrace_7957514 : CollatzResearch.WordTrace tailWord_7957514 prefixEnd_7957514 454003277431320491508785 := by
  unfold tailWord_7957514
  simp only [CollatzResearch.WordTrace]
  refine ⟨72558594823323322009497899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193489586195528858691994397 72558594823323322009497899)
  ·
    refine ⟨108837892234984983014246849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72558594823323322009497899 108837892234984983014246849)
    ·
      refine ⟨81628419176238737260685137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108837892234984983014246849 81628419176238737260685137)
      ·
        refine ⟨61221314382179052945513853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81628419176238737260685137 61221314382179052945513853)
        ·
          refine ⟨22957992893317144854567695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61221314382179052945513853 22957992893317144854567695)
          ·
            refine ⟨34436989339975717281851543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22957992893317144854567695 34436989339975717281851543)
            ·
              refine ⟨51655484009963575922777315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34436989339975717281851543 51655484009963575922777315)
              ·
                refine ⟨77483226014945363884165973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51655484009963575922777315 77483226014945363884165973)
                ·
                  refine ⟨454003277431320491508785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77483226014945363884165973 454003277431320491508785)
                  ·
                    rfl

theorem cell23_7957514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_7957514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957514 prefixEnd_7957514 := by exact prefixLift 7957514
  have htrace : WordTrace (prefixWord ++ tailWord_7957514) baseStart_7957514 baseEnd_7957514 := by
    simpa [prefixWord, tailWord_7957514, baseEnd_7957514] using wordTrace_append hprefix tailTrace_7957514
  have hstable : (prefixWord ++ tailWord_7957514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957514).length < 2 ^ (prefixWord ++ tailWord_7957514).sum := by decide
  have hdescent : baseEnd_7957514 < baseStart_7957514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957554 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_7957554 : Nat := 118140960795 + 7957554 * 2 ^ 59
def prefixEnd_7957554 : Nat := 4983230072969 + 3 ^ 40 * 7957554 * 2
def baseEnd_7957554 : Nat := 4086050036108064267078881

theorem tailTrace_7957554 : CollatzResearch.WordTrace tailWord_7957554 prefixEnd_7957554 4086050036108064267078881 := by
  unfold tailWord_7957554
  simp only [CollatzResearch.WordTrace]
  refine ⟨72558959553287093717361929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193490558808765583246298477 72558959553287093717361929)
  ·
    refine ⟨54419219664965320288021447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72558959553287093717361929 54419219664965320288021447)
    ·
      refine ⟨81628829497447980432032171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54419219664965320288021447 81628829497447980432032171)
      ·
        refine ⟨122443244246171970648048257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81628829497447980432032171 122443244246171970648048257)
        ·
          refine ⟨91832433184628977986036193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122443244246171970648048257 91832433184628977986036193)
          ·
            refine ⟨68874324888471733489527145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91832433184628977986036193 68874324888471733489527145)
            ·
              refine ⟨51655743666353800117145359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68874324888471733489527145 51655743666353800117145359)
              ·
                refine ⟨77483615499530700175718039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51655743666353800117145359 77483615499530700175718039)
                ·
                  refine ⟨116225423249296050263577059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77483615499530700175718039 116225423249296050263577059)
                  ·
                    refine ⟨174338134873944075395365589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116225423249296050263577059 174338134873944075395365589)
                    ·
                      refine ⟨4086050036108064267078881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174338134873944075395365589 4086050036108064267078881)
                      ·
                        rfl

theorem cell23_7957554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_7957554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957554 prefixEnd_7957554 := by exact prefixLift 7957554
  have htrace : WordTrace (prefixWord ++ tailWord_7957554) baseStart_7957554 baseEnd_7957554 := by
    simpa [prefixWord, tailWord_7957554, baseEnd_7957554] using wordTrace_append hprefix tailTrace_7957554
  have hstable : (prefixWord ++ tailWord_7957554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957554).length < 2 ^ (prefixWord ++ tailWord_7957554).sum := by decide
  have hdescent : baseEnd_7957554 < baseStart_7957554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957558 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_7957558 : Nat := 118140960795 + 7957558 * 2 ^ 59
def prefixEnd_7957558 : Nat := 4983230072969 + 3 ^ 40 * 7957558 * 2
def baseEnd_7957558 : Nat := 4086052090030682251428863

theorem tailTrace_7957558 : CollatzResearch.WordTrace tailWord_7957558 prefixEnd_7957558 4086052090030682251428863 := by
  unfold tailWord_7957558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18139749006570867722037083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193490656070089255701728885 18139749006570867722037083)
  ·
    refine ⟨27209623509856301583055625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18139749006570867722037083 27209623509856301583055625)
    ·
      refine ⟨20407217632392226187291719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27209623509856301583055625 20407217632392226187291719)
      ·
        refine ⟨30610826448588339280937579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20407217632392226187291719 30610826448588339280937579)
        ·
          refine ⟨45916239672882508921406369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30610826448588339280937579 45916239672882508921406369)
          ·
            refine ⟨34437179754661881691054777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45916239672882508921406369 34437179754661881691054777)
            ·
              refine ⟨25827884815996411268291083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34437179754661881691054777 25827884815996411268291083)
              ·
                refine ⟨38741827223994616902436625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25827884815996411268291083 38741827223994616902436625)
                ·
                  refine ⟨29056370417995962676827469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38741827223994616902436625 29056370417995962676827469)
                  ·
                    refine ⟨10896138906748486003810301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29056370417995962676827469 10896138906748486003810301)
                    ·
                      refine ⟨4086052090030682251428863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10896138906748486003810301 4086052090030682251428863)
                      ·
                        rfl

theorem cell23_7957558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_7957558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957558 prefixEnd_7957558 := by exact prefixLift 7957558
  have htrace : WordTrace (prefixWord ++ tailWord_7957558) baseStart_7957558 baseEnd_7957558 := by
    simpa [prefixWord, tailWord_7957558, baseEnd_7957558] using wordTrace_append hprefix tailTrace_7957558
  have hstable : (prefixWord ++ tailWord_7957558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957558).length < 2 ^ (prefixWord ++ tailWord_7957558).sum := by decide
  have hdescent : baseEnd_7957558 < baseStart_7957558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957594 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_7957594 : Nat := 118140960795 + 7957594 * 2 ^ 59
def prefixEnd_7957594 : Nat := 4983230072969 + 3 ^ 40 * 7957594 * 2
def baseEnd_7957594 : Nat := 4086070575334244110578697

theorem tailTrace_7957594 : CollatzResearch.WordTrace tailWord_7957594 prefixEnd_7957594 4086070575334244110578697 := by
  unfold tailWord_7957594
  simp only [CollatzResearch.WordTrace]
  refine ⟨72559324283250865425225959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193491531422002307800602557 72559324283250865425225959)
  ·
    refine ⟨108838986424876298137838939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72559324283250865425225959 108838986424876298137838939)
    ·
      refine ⟨163258479637314447206758409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108838986424876298137838939 163258479637314447206758409)
      ·
        refine ⟨122443859727985835405068807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163258479637314447206758409 122443859727985835405068807)
        ·
          refine ⟨183665789591978753107603211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122443859727985835405068807 183665789591978753107603211)
          ·
            refine ⟨275498684387968129661404817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183665789591978753107603211 275498684387968129661404817)
            ·
              refine ⟨206624013290976097246053613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275498684387968129661404817 206624013290976097246053613)
              ·
                refine ⟨77484004984116036467270105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206624013290976097246053613 77484004984116036467270105)
                ·
                  refine ⟨58113003738087027350452579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77484004984116036467270105 58113003738087027350452579)
                  ·
                    refine ⟨87169505607130541025678869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58113003738087027350452579 87169505607130541025678869)
                    ·
                      refine ⟨4086070575334244110578697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87169505607130541025678869 4086070575334244110578697)
                      ·
                        rfl

theorem cell23_7957594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_7957594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957594 prefixEnd_7957594 := by exact prefixLift 7957594
  have htrace : WordTrace (prefixWord ++ tailWord_7957594) baseStart_7957594 baseEnd_7957594 := by
    simpa [prefixWord, tailWord_7957594, baseEnd_7957594] using wordTrace_append hprefix tailTrace_7957594
  have hstable : (prefixWord ++ tailWord_7957594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957594).length < 2 ^ (prefixWord ++ tailWord_7957594).sum := by decide
  have hdescent : baseEnd_7957594 < baseStart_7957594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957601 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_7957601 : Nat := 118140960795 + 7957601 * 2 ^ 59
def prefixEnd_7957601 : Nat := 4983230072969 + 3 ^ 40 * 7957601 * 2
def baseEnd_7957601 : Nat := 4086074169698825583191165

theorem tailTrace_7957601 : CollatzResearch.WordTrace tailWord_7957601 prefixEnd_7957601 4086074169698825583191165 := by
  unfold tailWord_7957601
  simp only [CollatzResearch.WordTrace]
  refine ⟨290237552443978101896408657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193491701629318734597605771 290237552443978101896408657)
  ·
    refine ⟨217678164332983576422306493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290237552443978101896408657 217678164332983576422306493)
    ·
      refine ⟨81629311624868841158364935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217678164332983576422306493 81629311624868841158364935)
      ·
        refine ⟨122443967437303261737547403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81629311624868841158364935 122443967437303261737547403)
        ·
          refine ⟨183665951155954892606321105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122443967437303261737547403 183665951155954892606321105)
          ·
            refine ⟨137749463366966169454740829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183665951155954892606321105 137749463366966169454740829)
            ·
              refine ⟨51656048762612313545527811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137749463366966169454740829 51656048762612313545527811)
              ·
                refine ⟨77484073143918470318291717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51656048762612313545527811 77484073143918470318291717)
                ·
                  refine ⟨14528263714484713184679697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77484073143918470318291717 14528263714484713184679697)
                  ·
                    refine ⟨10896197785863534888509773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14528263714484713184679697 10896197785863534888509773)
                    ·
                      refine ⟨4086074169698825583191165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10896197785863534888509773 4086074169698825583191165)
                      ·
                        rfl

theorem cell23_7957601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_7957601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957601 prefixEnd_7957601 := by exact prefixLift 7957601
  have htrace : WordTrace (prefixWord ++ tailWord_7957601) baseStart_7957601 baseEnd_7957601 := by
    simpa [prefixWord, tailWord_7957601, baseEnd_7957601] using wordTrace_append hprefix tailTrace_7957601
  have hstable : (prefixWord ++ tailWord_7957601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957601).length < 2 ^ (prefixWord ++ tailWord_7957601).sum := by decide
  have hdescent : baseEnd_7957601 < baseStart_7957601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957624 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_7957624 : Nat := 118140960795 + 7957624 * 2 ^ 59
def prefixEnd_7957624 : Nat := 4983230072969 + 3 ^ 40 * 7957624 * 2
def baseEnd_7957624 : Nat := 4086085979753878993203559

theorem tailTrace_7957624 : CollatzResearch.WordTrace tailWord_7957624 prefixEnd_7957624 4086085979753878993203559 := by
  unfold tailWord_7957624
  simp only [CollatzResearch.WordTrace]
  refine ⟨145119195661447388412247963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193492260881929851216330617 145119195661447388412247963)
  ·
    refine ⟨217678793492171082618371945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145119195661447388412247963 217678793492171082618371945)
    ·
      refine ⟨163259095119128311963778959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217678793492171082618371945 163259095119128311963778959)
      ·
        refine ⟨244888642678692467945668439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163259095119128311963778959 244888642678692467945668439)
        ·
          refine ⟨367332964018038701918502659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244888642678692467945668439 367332964018038701918502659)
          ·
            refine ⟨550999446027058052877753989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367332964018038701918502659 550999446027058052877753989)
            ·
              refine ⟨103312396130073384914578873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 550999446027058052877753989 103312396130073384914578873)
              ·
                refine ⟨77484297097555038685934155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103312396130073384914578873 77484297097555038685934155)
                ·
                  refine ⟨116226445646332558028901233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77484297097555038685934155 116226445646332558028901233)
                  ·
                    refine ⟨87169834234749418521675925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116226445646332558028901233 87169834234749418521675925)
                    ·
                      refine ⟨4086085979753878993203559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87169834234749418521675925 4086085979753878993203559)
                      ·
                        rfl

theorem cell23_7957624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_7957624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957624 prefixEnd_7957624 := by exact prefixLift 7957624
  have htrace : WordTrace (prefixWord ++ tailWord_7957624) baseStart_7957624 baseEnd_7957624 := by
    simpa [prefixWord, tailWord_7957624, baseEnd_7957624] using wordTrace_append hprefix tailTrace_7957624
  have hstable : (prefixWord ++ tailWord_7957624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957624).length < 2 ^ (prefixWord ++ tailWord_7957624).sum := by decide
  have hdescent : baseEnd_7957624 < baseStart_7957624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957644 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_7957644 : Nat := 118140960795 + 7957644 * 2 ^ 59
def prefixEnd_7957644 : Nat := 4983230072969 + 3 ^ 40 * 7957644 * 2
def baseEnd_7957644 : Nat := 4086096249366968914953467

theorem tailTrace_7957644 : CollatzResearch.WordTrace tailWord_7957644 prefixEnd_7957644 4086096249366968914953467 := by
  unfold tailWord_7957644
  simp only [CollatzResearch.WordTrace]
  refine ⟨145119560391411160120111993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193492747188548213493482657 145119560391411160120111993)
  ·
    refine ⟨108839670293558370090083995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145119560391411160120111993 108839670293558370090083995)
    ·
      refine ⟨163259505440337555135125993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108839670293558370090083995 163259505440337555135125993)
      ·
        refine ⟨122444629080253166351344495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163259505440337555135125993 122444629080253166351344495)
        ·
          refine ⟨183666943620379749527016743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122444629080253166351344495 183666943620379749527016743)
          ·
            refine ⟨275500415430569624290525115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183666943620379749527016743 275500415430569624290525115)
            ·
              refine ⟨413250623145854436435787673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275500415430569624290525115 413250623145854436435787673)
              ·
                refine ⟨309937967359390827326840755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413250623145854436435787673 309937967359390827326840755)
                ·
                  refine ⟨464906951039086240990261133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309937967359390827326840755 464906951039086240990261133)
                  ·
                    refine ⟨174340106639657340371347925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 464906951039086240990261133 174340106639657340371347925)
                    ·
                      refine ⟨4086096249366968914953467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174340106639657340371347925 4086096249366968914953467)
                      ·
                        rfl

theorem cell23_7957644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_7957644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957644 prefixEnd_7957644 := by exact prefixLift 7957644
  have htrace : WordTrace (prefixWord ++ tailWord_7957644) baseStart_7957644 baseEnd_7957644 := by
    simpa [prefixWord, tailWord_7957644, baseEnd_7957644] using wordTrace_append hprefix tailTrace_7957644
  have hstable : (prefixWord ++ tailWord_7957644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957644).length < 2 ^ (prefixWord ++ tailWord_7957644).sum := by decide
  have hdescent : baseEnd_7957644 < baseStart_7957644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957651 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 1, 5]
def baseStart_7957651 : Nat := 118140960795 + 7957651 * 2 ^ 59
def prefixEnd_7957651 : Nat := 4983230072969 + 3 ^ 40 * 7957651 * 2
def baseEnd_7957651 : Nat := 1362033281243850129188645

theorem tailTrace_7957651 : CollatzResearch.WordTrace tailWord_7957651 prefixEnd_7957651 1362033281243850129188645 := by
  unfold tailWord_7957651
  simp only [CollatzResearch.WordTrace]
  refine ⟨290239376093796960435728807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193492917395864640290485871 290239376093796960435728807)
  ·
    refine ⟨435359064140695440653593211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290239376093796960435728807 435359064140695440653593211)
    ·
      refine ⟨653038596211043160980389817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435359064140695440653593211 653038596211043160980389817)
      ·
        refine ⟨489778947158282370735292363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653038596211043160980389817 489778947158282370735292363)
        ·
          refine ⟨734668420737423556102938545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489778947158282370735292363 734668420737423556102938545)
          ·
            refine ⟨551001315553067667077203909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734668420737423556102938545 551001315553067667077203909)
            ·
              refine ⟨103312746666200187576975733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 551001315553067667077203909 103312746666200187576975733)
              ·
                refine ⟨9685569999956267585341475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103312746666200187576975733 9685569999956267585341475)
                ·
                  refine ⟨14528354999934401378012213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9685569999956267585341475 14528354999934401378012213)
                  ·
                    refine ⟨1362033281243850129188645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14528354999934401378012213 1362033281243850129188645)
                    ·
                      rfl

theorem cell23_7957651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 5].length) (baseStart_7957651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957651 prefixEnd_7957651 := by exact prefixLift 7957651
  have htrace : WordTrace (prefixWord ++ tailWord_7957651) baseStart_7957651 baseEnd_7957651 := by
    simpa [prefixWord, tailWord_7957651, baseEnd_7957651] using wordTrace_append hprefix tailTrace_7957651
  have hstable : (prefixWord ++ tailWord_7957651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957651).length < 2 ^ (prefixWord ++ tailWord_7957651).sum := by decide
  have hdescent : baseEnd_7957651 < baseStart_7957651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957686 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7957686 : Nat := 118140960795 + 7957686 * 2 ^ 59
def prefixEnd_7957686 : Nat := 4983230072969 + 3 ^ 40 * 7957686 * 2
def baseEnd_7957686 : Nat := 4086117815554457750628275

theorem tailTrace_7957686 : CollatzResearch.WordTrace tailWord_7957686 prefixEnd_7957686 4086117815554457750628275 := by
  unfold tailWord_7957686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18140040790541885088328307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193493768432446774275501941 18140040790541885088328307)
  ·
    refine ⟨27210061185812827632492461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18140040790541885088328307 27210061185812827632492461)
    ·
      refine ⟨10203772944679810362184673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27210061185812827632492461 10203772944679810362184673)
      ·
        refine ⟨7652829708509857771638505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10203772944679810362184673 7652829708509857771638505)
        ·
          refine ⟨5739622281382393328728879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7652829708509857771638505 5739622281382393328728879)
          ·
            refine ⟨8609433422073589993093319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739622281382393328728879 8609433422073589993093319)
            ·
              refine ⟨12914150133110384989639979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609433422073589993093319 12914150133110384989639979)
              ·
                refine ⟨19371225199665577484459969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12914150133110384989639979 19371225199665577484459969)
                ·
                  refine ⟨14528418899749183113344977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19371225199665577484459969 14528418899749183113344977)
                  ·
                    refine ⟨10896314174811887335008733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14528418899749183113344977 10896314174811887335008733)
                    ·
                      refine ⟨4086117815554457750628275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10896314174811887335008733 4086117815554457750628275)
                      ·
                        rfl

theorem cell23_7957686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7957686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957686 prefixEnd_7957686 := by exact prefixLift 7957686
  have htrace : WordTrace (prefixWord ++ tailWord_7957686) baseStart_7957686 baseEnd_7957686 := by
    simpa [prefixWord, tailWord_7957686, baseEnd_7957686] using wordTrace_append hprefix tailTrace_7957686
  have hstable : (prefixWord ++ tailWord_7957686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957686).length < 2 ^ (prefixWord ++ tailWord_7957686).sum := by decide
  have hdescent : baseEnd_7957686 < baseStart_7957686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957692 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 2, 3, 2]
def baseStart_7957692 : Nat := 118140960795 + 7957692 * 2 ^ 59
def prefixEnd_7957692 : Nat := 4983230072969 + 3 ^ 40 * 7957692 * 2
def baseEnd_7957692 : Nat := 4086120896438384727153247

theorem tailTrace_7957692 : CollatzResearch.WordTrace tailWord_7957692 prefixEnd_7957692 4086120896438384727153247 := by
  unfold tailWord_7957692
  simp only [CollatzResearch.WordTrace]
  refine ⟨145120435743324212218985665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193493914324432282958647553 145120435743324212218985665)
  ·
    refine ⟨108840326807493159164239249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145120435743324212218985665 108840326807493159164239249)
    ·
      refine ⟨81630245105619869373179437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108840326807493159164239249 81630245105619869373179437)
      ·
        refine ⟨30611341914607451014942289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81630245105619869373179437 30611341914607451014942289)
        ·
          refine ⟨22958506435955588261206717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30611341914607451014942289 22958506435955588261206717)
          ·
            refine ⟨8609439913483345597952519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22958506435955588261206717 8609439913483345597952519)
            ·
              refine ⟨12914159870225018396928779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609439913483345597952519 12914159870225018396928779)
              ·
                refine ⟨19371239805337527595393169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12914159870225018396928779 19371239805337527595393169)
                ·
                  refine ⟨14528429854003145696544877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19371239805337527595393169 14528429854003145696544877)
                  ·
                    refine ⟨5448161195251179636204329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14528429854003145696544877 5448161195251179636204329)
                    ·
                      refine ⟨4086120896438384727153247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448161195251179636204329 4086120896438384727153247)
                      ·
                        rfl

theorem cell23_7957692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_7957692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957692 prefixEnd_7957692 := by exact prefixLift 7957692
  have htrace : WordTrace (prefixWord ++ tailWord_7957692) baseStart_7957692 baseEnd_7957692 := by
    simpa [prefixWord, tailWord_7957692, baseEnd_7957692] using wordTrace_append hprefix tailTrace_7957692
  have hstable : (prefixWord ++ tailWord_7957692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957692).length < 2 ^ (prefixWord ++ tailWord_7957692).sum := by decide
  have hdescent : baseEnd_7957692 < baseStart_7957692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957725 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7957725 : Nat := 118140960795 + 7957725 * 2 ^ 59
def prefixEnd_7957725 : Nat := 4983230072969 + 3 ^ 40 * 7957725 * 2
def baseEnd_7957725 : Nat := 4086137841299983098040595

theorem tailTrace_7957725 : CollatzResearch.WordTrace tailWord_7957725 prefixEnd_7957725 4086137841299983098040595 := by
  unfold tailWord_7957725
  simp only [CollatzResearch.WordTrace]
  refine ⟨290242075095528871073922629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193494716730352580715948419 290242075095528871073922629)
  ·
    refine ⟨54420389080411663326360493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290242075095528871073922629 54420389080411663326360493)
    ·
      refine ⟨20407645905154373747385185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54420389080411663326360493 20407645905154373747385185)
      ·
        refine ⟨15305734428865780310538889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20407645905154373747385185 15305734428865780310538889)
        ·
          refine ⟨11479300821649335232904167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15305734428865780310538889 11479300821649335232904167)
          ·
            refine ⟨17218951232474002849356251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11479300821649335232904167 17218951232474002849356251)
            ·
              refine ⟨25828426848711004274034377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17218951232474002849356251 25828426848711004274034377)
              ·
                refine ⟨19371320136533253205525783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25828426848711004274034377 19371320136533253205525783)
                ·
                  refine ⟨29056980204799879808288675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19371320136533253205525783 29056980204799879808288675)
                  ·
                    refine ⟨43585470307199819712433013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29056980204799879808288675 43585470307199819712433013)
                    ·
                      refine ⟨4086137841299983098040595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43585470307199819712433013 4086137841299983098040595)
                      ·
                        rfl

theorem cell23_7957725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7957725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957725 prefixEnd_7957725 := by exact prefixLift 7957725
  have htrace : WordTrace (prefixWord ++ tailWord_7957725) baseStart_7957725 baseEnd_7957725 := by
    simpa [prefixWord, tailWord_7957725, baseEnd_7957725] using wordTrace_append hprefix tailTrace_7957725
  have hstable : (prefixWord ++ tailWord_7957725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957725).length < 2 ^ (prefixWord ++ tailWord_7957725).sum := by decide
  have hdescent : baseEnd_7957725 < baseStart_7957725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957756 : List Nat := [2, 2, 2, 1, 5, 2, 1, 3, 1, 2, 2]
def baseStart_7957756 : Nat := 118140960795 + 7957756 * 2 ^ 59
def prefixEnd_7957756 : Nat := 4983230072969 + 3 ^ 40 * 7957756 * 2
def baseEnd_7957756 : Nat := 4086153759200272476752953

theorem tailTrace_7957756 : CollatzResearch.WordTrace tailWord_7957756 prefixEnd_7957756 4086153759200272476752953 := by
  unfold tailWord_7957756
  simp only [CollatzResearch.WordTrace]
  refine ⟨145121602879208281684150561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193495470505611042245534081 145121602879208281684150561)
  ·
    refine ⟨108841202159406211263112921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145121602879208281684150561 108841202159406211263112921)
    ·
      refine ⟨81630901619554658447334691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108841202159406211263112921 81630901619554658447334691)
      ·
        refine ⟨122446352429331987671002037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81630901619554658447334691 122446352429331987671002037)
        ·
          refine ⟨11479345540249873844156441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122446352429331987671002037 11479345540249873844156441)
          ·
            refine ⟨8609509155187405383117331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11479345540249873844156441 8609509155187405383117331)
            ·
              refine ⟨12914263732781108074675997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609509155187405383117331 12914263732781108074675997)
              ·
                refine ⟨4842848899792915528003499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12914263732781108074675997 4842848899792915528003499)
                ·
                  refine ⟨7264273349689373292005249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4842848899792915528003499 7264273349689373292005249)
                  ·
                    refine ⟨5448205012267029969003937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7264273349689373292005249 5448205012267029969003937)
                    ·
                      refine ⟨4086153759200272476752953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448205012267029969003937 4086153759200272476752953)
                      ·
                        rfl

theorem cell23_7957756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_7957756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957756 prefixEnd_7957756 := by exact prefixLift 7957756
  have htrace : WordTrace (prefixWord ++ tailWord_7957756) baseStart_7957756 baseEnd_7957756 := by
    simpa [prefixWord, tailWord_7957756, baseEnd_7957756] using wordTrace_append hprefix tailTrace_7957756
  have hstable : (prefixWord ++ tailWord_7957756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957756).length < 2 ^ (prefixWord ++ tailWord_7957756).sum := by decide
  have hdescent : baseEnd_7957756 < baseStart_7957756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957765 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 1, 3, 2]
def baseStart_7957765 : Nat := 118140960795 + 7957765 * 2 ^ 59
def prefixEnd_7957765 : Nat := 4983230072969 + 3 ^ 40 * 7957765 * 2
def baseEnd_7957765 : Nat := 4086158380526162941540411

theorem tailTrace_7957765 : CollatzResearch.WordTrace tailWord_7957765 prefixEnd_7957765 4086158380526162941540411 := by
  unfold tailWord_7957765
  simp only [CollatzResearch.WordTrace]
  refine ⟨290243534015383957905378749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193495689343589305270252499 290243534015383957905378749)
  ·
    refine ⟨108841325255768984214517031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290243534015383957905378749 108841325255768984214517031)
    ·
      refine ⟨163261987883653476321775547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108841325255768984214517031 163261987883653476321775547)
      ·
        refine ⟨244892981825480214482663321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163261987883653476321775547 244892981825480214482663321)
        ·
          refine ⟨183669736369110160861997491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244892981825480214482663321 183669736369110160861997491)
          ·
            refine ⟨275504604553665241292996237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183669736369110160861997491 275504604553665241292996237)
            ·
              refine ⟨103314226707624465484873589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275504604553665241292996237 103314226707624465484873589)
              ·
                refine ⟨9685708753839793639206899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103314226707624465484873589 9685708753839793639206899)
                ·
                  refine ⟨14528563130759690458810349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9685708753839793639206899 14528563130759690458810349)
                  ·
                    refine ⟨5448211174034883922053881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14528563130759690458810349 5448211174034883922053881)
                    ·
                      refine ⟨4086158380526162941540411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448211174034883922053881 4086158380526162941540411)
                      ·
                        rfl

theorem cell23_7957765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_7957765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957765 prefixEnd_7957765 := by exact prefixLift 7957765
  have htrace : WordTrace (prefixWord ++ tailWord_7957765) baseStart_7957765 baseEnd_7957765 := by
    simpa [prefixWord, tailWord_7957765, baseEnd_7957765] using wordTrace_append hprefix tailTrace_7957765
  have hstable : (prefixWord ++ tailWord_7957765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957765).length < 2 ^ (prefixWord ++ tailWord_7957765).sum := by decide
  have hdescent : baseEnd_7957765 < baseStart_7957765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957781 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_7957781 : Nat := 118140960795 + 7957781 * 2 ^ 59
def prefixEnd_7957781 : Nat := 4983230072969 + 3 ^ 40 * 7957781 * 2
def baseEnd_7957781 : Nat := 4086166596216634878940337

theorem tailTrace_7957781 : CollatzResearch.WordTrace tailWord_7957781 prefixEnd_7957781 4086166596216634878940337 := by
  unfold tailWord_7957781
  simp only [CollatzResearch.WordTrace]
  refine ⟨290244117583325992637961197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193496078388883995091974131 290244117583325992637961197)
  ·
    refine ⟨108841544093747247239235449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290244117583325992637961197 108841544093747247239235449)
    ·
      refine ⟨81631158070310435429426587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108841544093747247239235449 81631158070310435429426587)
      ·
        refine ⟨122446737105465653144139881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81631158070310435429426587 122446737105465653144139881)
        ·
          refine ⟨91835052829099239858104911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122446737105465653144139881 91835052829099239858104911)
          ·
            refine ⟨137752579243648859787157367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91835052829099239858104911 137752579243648859787157367)
            ·
              refine ⟨206628868865473289680736051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137752579243648859787157367 206628868865473289680736051)
              ·
                refine ⟨309943303298209934521104077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206628868865473289680736051 309943303298209934521104077)
                ·
                  refine ⟨116228738736828725445414029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309943303298209934521104077 116228738736828725445414029)
                  ·
                    refine ⟨43585777026310772042030261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116228738736828725445414029 43585777026310772042030261)
                    ·
                      refine ⟨4086166596216634878940337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43585777026310772042030261 4086166596216634878940337)
                      ·
                        rfl

theorem cell23_7957781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_7957781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957781 prefixEnd_7957781 := by exact prefixLift 7957781
  have htrace : WordTrace (prefixWord ++ tailWord_7957781) baseStart_7957781 baseEnd_7957781 := by
    simpa [prefixWord, tailWord_7957781, baseEnd_7957781] using wordTrace_append hprefix tailTrace_7957781
  have hstable : (prefixWord ++ tailWord_7957781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957781).length < 2 ^ (prefixWord ++ tailWord_7957781).sum := by decide
  have hdescent : baseEnd_7957781 < baseStart_7957781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957789 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_7957789 : Nat := 118140960795 + 7957789 * 2 ^ 59
def prefixEnd_7957789 : Nat := 4983230072969 + 3 ^ 40 * 7957789 * 2
def baseEnd_7957789 : Nat := 4086170704061870847640301

theorem tailTrace_7957789 : CollatzResearch.WordTrace tailWord_7957789 prefixEnd_7957789 4086170704061870847640301 := by
  unfold tailWord_7957789
  simp only [CollatzResearch.WordTrace]
  refine ⟨290244409367297010004252421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193496272911531340002834947 290244409367297010004252421)
  ·
    refine ⟨54420826756368189375797329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290244409367297010004252421 54420826756368189375797329)
    ·
      refine ⟨40815620067276142031847997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54420826756368189375797329 40815620067276142031847997)
      ·
        refine ⟨15305857525228553261942999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40815620067276142031847997 15305857525228553261942999)
        ·
          refine ⟨22958786287842829892914499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15305857525228553261942999 22958786287842829892914499)
          ·
            refine ⟨34438179431764244839371749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22958786287842829892914499 34438179431764244839371749)
            ·
              refine ⟨6457158643455795907382203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34438179431764244839371749 6457158643455795907382203)
              ·
                refine ⟨9685737965183693861073305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457158643455795907382203 9685737965183693861073305)
                ·
                  refine ⟨7264303473887770395804979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9685737965183693861073305 7264303473887770395804979)
                  ·
                    refine ⟨10896455210831655593707469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7264303473887770395804979 10896455210831655593707469)
                    ·
                      refine ⟨4086170704061870847640301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10896455210831655593707469 4086170704061870847640301)
                      ·
                        rfl

theorem cell23_7957789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_7957789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957789 prefixEnd_7957789 := by exact prefixLift 7957789
  have htrace : WordTrace (prefixWord ++ tailWord_7957789) baseStart_7957789 baseEnd_7957789 := by
    simpa [prefixWord, tailWord_7957789, baseEnd_7957789] using wordTrace_append hprefix tailTrace_7957789
  have hstable : (prefixWord ++ tailWord_7957789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957789).length < 2 ^ (prefixWord ++ tailWord_7957789).sum := by decide
  have hdescent : baseEnd_7957789 < baseStart_7957789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957812 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_7957812 : Nat := 118140960795 + 7957812 * 2 ^ 59
def prefixEnd_7957812 : Nat := 4983230072969 + 3 ^ 40 * 7957812 * 2
def baseEnd_7957812 : Nat := 4086182514116924257652695

theorem tailTrace_7957812 : CollatzResearch.WordTrace tailWord_7957812 prefixEnd_7957812 4086182514116924257652695 := by
  unfold tailWord_7957812
  simp only [CollatzResearch.WordTrace]
  refine ⟨145122624123106842466169845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193496832164142456621559793 145122624123106842466169845)
  ·
    refine ⟨13605246011541266481203423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145122624123106842466169845 13605246011541266481203423)
    ·
      refine ⟨20407869017311899721805135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13605246011541266481203423 20407869017311899721805135)
      ·
        refine ⟨30611803525967849582707703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20407869017311899721805135 30611803525967849582707703)
        ·
          refine ⟨45917705288951774374061555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30611803525967849582707703 45917705288951774374061555)
          ·
            refine ⟨68876557933427661561092333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45917705288951774374061555 68876557933427661561092333)
            ·
              refine ⟨25828709225035373085409625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68876557933427661561092333 25828709225035373085409625)
              ·
                refine ⟨19371531918776529814057219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25828709225035373085409625 19371531918776529814057219)
                ·
                  refine ⟨29057297878164794721085829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19371531918776529814057219 29057297878164794721085829)
                  ·
                    refine ⟨5448243352155899010203593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29057297878164794721085829 5448243352155899010203593)
                    ·
                      refine ⟨4086182514116924257652695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448243352155899010203593 4086182514116924257652695)
                      ·
                        rfl

theorem cell23_7957812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_7957812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957812 prefixEnd_7957812 := by exact prefixLift 7957812
  have htrace : WordTrace (prefixWord ++ tailWord_7957812) baseStart_7957812 baseEnd_7957812 := by
    simpa [prefixWord, tailWord_7957812, baseEnd_7957812] using wordTrace_append hprefix tailTrace_7957812
  have hstable : (prefixWord ++ tailWord_7957812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957812).length < 2 ^ (prefixWord ++ tailWord_7957812).sum := by decide
  have hdescent : baseEnd_7957812 < baseStart_7957812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957845 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_7957845 : Nat := 118140960795 + 7957845 * 2 ^ 59
def prefixEnd_7957845 : Nat := 4983230072969 + 3 ^ 40 * 7957845 * 2
def baseEnd_7957845 : Nat := 4086199458978522628540043

theorem tailTrace_7957845 : CollatzResearch.WordTrace tailWord_7957845 prefixEnd_7957845 4086199458978522628540043 := by
  unfold tailWord_7957845
  simp only [CollatzResearch.WordTrace]
  refine ⟨290246451855094131568290989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193497634570062754378860659 290246451855094131568290989)
  ·
    refine ⟨108842419445660299338109121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290246451855094131568290989 108842419445660299338109121)
    ·
      refine ⟨81631814584245224503581841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108842419445660299338109121 81631814584245224503581841)
      ·
        refine ⟨61223860938183918377686381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81631814584245224503581841 61223860938183918377686381)
        ·
          refine ⟨22958947851818969391632393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61223860938183918377686381 22958947851818969391632393)
          ·
            refine ⟨17219210888864227043724295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22958947851818969391632393 17219210888864227043724295)
            ·
              refine ⟨25828816333296340565586443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17219210888864227043724295 25828816333296340565586443)
              ·
                refine ⟨38743224499944510848379665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25828816333296340565586443 38743224499944510848379665)
                ·
                  refine ⟨29057418374958383136284749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38743224499944510848379665 29057418374958383136284749)
                  ·
                    refine ⟨10896531890609393676106781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29057418374958383136284749 10896531890609393676106781)
                    ·
                      refine ⟨4086199458978522628540043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10896531890609393676106781 4086199458978522628540043)
                      ·
                        rfl

theorem cell23_7957845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_7957845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957845 prefixEnd_7957845 := by exact prefixLift 7957845
  have htrace : WordTrace (prefixWord ++ tailWord_7957845) baseStart_7957845 baseEnd_7957845 := by
    simpa [prefixWord, tailWord_7957845, baseEnd_7957845] using wordTrace_append hprefix tailTrace_7957845
  have hstable : (prefixWord ++ tailWord_7957845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957845).length < 2 ^ (prefixWord ++ tailWord_7957845).sum := by decide
  have hdescent : baseEnd_7957845 < baseStart_7957845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957885 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 4, 4, 2]
def baseStart_7957885 : Nat := 118140960795 + 7957885 * 2 ^ 59
def prefixEnd_7957885 : Nat := 4983230072969 + 3 ^ 40 * 7957885 * 2
def baseEnd_7957885 : Nat := 4086219998204702472039859

theorem tailTrace_7957885 : CollatzResearch.WordTrace tailWord_7957885 prefixEnd_7957885 4086219998204702472039859 := by
  unfold tailWord_7957885
  simp only [CollatzResearch.WordTrace]
  refine ⟨290247910774949218399747109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193498607183299478933164739 290247910774949218399747109)
  ·
    refine ⟨54421483270302978449952583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290247910774949218399747109 54421483270302978449952583)
    ·
      refine ⟨81632224905454467674928875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54421483270302978449952583 81632224905454467674928875)
      ·
        refine ⟨122448337358181701512393313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81632224905454467674928875 122448337358181701512393313)
        ·
          refine ⟨91836253018636276134294985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122448337358181701512393313 91836253018636276134294985)
          ·
            refine ⟨68877189763977207100721239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91836253018636276134294985 68877189763977207100721239)
            ·
              refine ⟨103315784645965810651081859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68877189763977207100721239 103315784645965810651081859)
              ·
                refine ⟨154973676968948715976622789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103315784645965810651081859 154973676968948715976622789)
                ·
                  refine ⟨29057564431677884245616773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154973676968948715976622789 29057564431677884245616773)
                  ·
                    refine ⟨5448293330939603296053145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29057564431677884245616773 5448293330939603296053145)
                    ·
                      refine ⟨4086219998204702472039859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448293330939603296053145 4086219998204702472039859)
                      ·
                        rfl

theorem cell23_7957885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_7957885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957885 prefixEnd_7957885 := by exact prefixLift 7957885
  have htrace : WordTrace (prefixWord ++ tailWord_7957885) baseStart_7957885 baseEnd_7957885 := by
    simpa [prefixWord, tailWord_7957885, baseEnd_7957885] using wordTrace_append hprefix tailTrace_7957885
  have hstable : (prefixWord ++ tailWord_7957885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957885).length < 2 ^ (prefixWord ++ tailWord_7957885).sum := by decide
  have hdescent : baseEnd_7957885 < baseStart_7957885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957895 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 3, 4]
def baseStart_7957895 : Nat := 118140960795 + 7957895 * 2 ^ 59
def prefixEnd_7957895 : Nat := 4983230072969 + 3 ^ 40 * 7957895 * 2
def baseEnd_7957895 : Nat := 1362075044337082477638271

theorem tailTrace_7957895 : CollatzResearch.WordTrace tailWord_7957895 prefixEnd_7957895 1362075044337082477638271 := by
  unfold tailWord_7957895
  simp only [CollatzResearch.WordTrace]
  refine ⟨290248275504912990107611139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193498850336608660071740759 290248275504912990107611139)
  ·
    refine ⟨435372413257369485161416709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290248275504912990107611139 435372413257369485161416709)
    ·
      refine ⟨81632327485756778467765633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435372413257369485161416709 81632327485756778467765633)
      ·
        refine ⟨61224245614317583850824225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81632327485756778467765633 61224245614317583850824225)
        ·
          refine ⟨45918184210738187888118169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61224245614317583850824225 45918184210738187888118169)
          ·
            refine ⟨34438638158053640916088627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45918184210738187888118169 34438638158053640916088627)
            ·
              refine ⟨51657957237080461374132941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34438638158053640916088627 51657957237080461374132941)
              ·
                refine ⟨19371733963905173015299853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51657957237080461374132941 19371733963905173015299853)
                ·
                  refine ⟨7264400236464439880737445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19371733963905173015299853 7264400236464439880737445)
                  ·
                    refine ⟨1362075044337082477638271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7264400236464439880737445 1362075044337082477638271)
                    ·
                      rfl

theorem cell23_7957895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_7957895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957895 prefixEnd_7957895 := by exact prefixLift 7957895
  have htrace : WordTrace (prefixWord ++ tailWord_7957895) baseStart_7957895 baseEnd_7957895 := by
    simpa [prefixWord, tailWord_7957895, baseEnd_7957895] using wordTrace_append hprefix tailTrace_7957895
  have hstable : (prefixWord ++ tailWord_7957895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957895).length < 2 ^ (prefixWord ++ tailWord_7957895).sum := by decide
  have hdescent : baseEnd_7957895 < baseStart_7957895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957935 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 5, 1, 3]
def baseStart_7957935 : Nat := 118140960795 + 7957935 * 2 ^ 59
def prefixEnd_7957935 : Nat := 4983230072969 + 3 ^ 40 * 7957935 * 2
def baseEnd_7957935 : Nat := 4086245672237427276414629

theorem tailTrace_7957935 : CollatzResearch.WordTrace tailWord_7957935 prefixEnd_7957935 4086245672237427276414629 := by
  unfold tailWord_7957935
  simp only [CollatzResearch.WordTrace]
  refine ⟨290249734424768076939067259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193499822949845384626044839 290249734424768076939067259)
  ·
    refine ⟨435374601637152115408600889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290249734424768076939067259 435374601637152115408600889)
    ·
      refine ⟨326530951227864086556450667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435374601637152115408600889 326530951227864086556450667)
      ·
        refine ⟨489796426841796129834676001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326530951227864086556450667 489796426841796129834676001)
        ·
          refine ⟨367347320131347097376007001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489796426841796129834676001 367347320131347097376007001)
          ·
            refine ⟨275510490098510323032005251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367347320131347097376007001 275510490098510323032005251)
            ·
              refine ⟨413265735147765484548007877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275510490098510323032005251 413265735147765484548007877)
              ·
                refine ⟨77487325340206028352751477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413265735147765484548007877 77487325340206028352751477)
                ·
                  refine ⟨7264436750644315158070451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77487325340206028352751477 7264436750644315158070451)
                  ·
                    refine ⟨10896655125966472737105677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7264436750644315158070451 10896655125966472737105677)
                    ·
                      refine ⟨4086245672237427276414629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10896655125966472737105677 4086245672237427276414629)
                      ·
                        rfl

theorem cell23_7957935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 1, 3].length) (baseStart_7957935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957935 prefixEnd_7957935 := by exact prefixLift 7957935
  have htrace : WordTrace (prefixWord ++ tailWord_7957935) baseStart_7957935 baseEnd_7957935 := by
    simpa [prefixWord, tailWord_7957935, baseEnd_7957935] using wordTrace_append hprefix tailTrace_7957935
  have hstable : (prefixWord ++ tailWord_7957935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957935).length < 2 ^ (prefixWord ++ tailWord_7957935).sum := by decide
  have hdescent : baseEnd_7957935 < baseStart_7957935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957952 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 3, 1, 3]
def baseStart_7957952 : Nat := 118140960795 + 7957952 * 2 ^ 59
def prefixEnd_7957952 : Nat := 4983230072969 + 3 ^ 40 * 7957952 * 2
def baseEnd_7957952 : Nat := 4086254401408553709902051

theorem tailTrace_7957952 : CollatzResearch.WordTrace tailWord_7957952 prefixEnd_7957952 4086254401408553709902051 := by
  unfold tailWord_7957952
  simp only [CollatzResearch.WordTrace]
  refine ⟨145125177232853244421218055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193500236310470992561624073 145125177232853244421218055)
  ·
    refine ⟨217687765849279866631827083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145125177232853244421218055 217687765849279866631827083)
    ·
      refine ⟨326531648773919799947740625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217687765849279866631827083 326531648773919799947740625)
      ·
        refine ⟨244898736580439849960805469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326531648773919799947740625 244898736580439849960805469)
        ·
          refine ⟨91837026217664943735302051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244898736580439849960805469 91837026217664943735302051)
          ·
            refine ⟨137755539326497415602953077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91837026217664943735302051 137755539326497415602953077)
            ·
              refine ⟨12914581811859132712776851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137755539326497415602953077 12914581811859132712776851)
              ·
                refine ⟨19371872717788699069165277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12914581811859132712776851 19371872717788699069165277)
                ·
                  refine ⟨7264452269170762150936979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19371872717788699069165277 7264452269170762150936979)
                  ·
                    refine ⟨10896678403756143226405469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7264452269170762150936979 10896678403756143226405469)
                    ·
                      refine ⟨4086254401408553709902051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10896678403756143226405469 4086254401408553709902051)
                      ·
                        rfl

theorem cell23_7957952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_7957952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957952 prefixEnd_7957952 := by exact prefixLift 7957952
  have htrace : WordTrace (prefixWord ++ tailWord_7957952) baseStart_7957952 baseEnd_7957952 := by
    simpa [prefixWord, tailWord_7957952, baseEnd_7957952] using wordTrace_append hprefix tailTrace_7957952
  have hstable : (prefixWord ++ tailWord_7957952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957952).length < 2 ^ (prefixWord ++ tailWord_7957952).sum := by decide
  have hdescent : baseEnd_7957952 < baseStart_7957952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957972 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_7957972 : Nat := 118140960795 + 7957972 * 2 ^ 59
def prefixEnd_7957972 : Nat := 4983230072969 + 3 ^ 40 * 7957972 * 2
def baseEnd_7957972 : Nat := 1362088223673881210550653

theorem tailTrace_7957972 : CollatzResearch.WordTrace tailWord_7957972 prefixEnd_7957972 1362088223673881210550653 := by
  unfold tailWord_7957972
  simp only [CollatzResearch.WordTrace]
  refine ⟨145125541962817016129082085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193500722617089354838776113 145125541962817016129082085)
  ·
    refine ⟨27211039118028190524202891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145125541962817016129082085 27211039118028190524202891)
    ·
      refine ⟨40816558677042285786304337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27211039118028190524202891 40816558677042285786304337)
      ·
        refine ⟨30612419007781714339728253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40816558677042285786304337 30612419007781714339728253)
        ·
          refine ⟨11479657127918142877398095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30612419007781714339728253 11479657127918142877398095)
          ·
            refine ⟨17219485691877214316097143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11479657127918142877398095 17219485691877214316097143)
            ·
              refine ⟨25829228537815821474145715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17219485691877214316097143 25829228537815821474145715)
              ·
                refine ⟨38743842806723732211218573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25829228537815821474145715 38743842806723732211218573)
                ·
                  refine ⟨14528941052521399579206965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38743842806723732211218573 14528941052521399579206965)
                  ·
                    refine ⟨1362088223673881210550653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14528941052521399579206965 1362088223673881210550653)
                    ·
                      rfl

theorem cell23_7957972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_7957972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957972 prefixEnd_7957972 := by exact prefixLift 7957972
  have htrace : WordTrace (prefixWord ++ tailWord_7957972) baseStart_7957972 baseEnd_7957972 := by
    simpa [prefixWord, tailWord_7957972, baseEnd_7957972] using wordTrace_append hprefix tailTrace_7957972
  have hstable : (prefixWord ++ tailWord_7957972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957972).length < 2 ^ (prefixWord ++ tailWord_7957972).sum := by decide
  have hdescent : baseEnd_7957972 < baseStart_7957972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957975 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 2, 6, 2]
def baseStart_7957975 : Nat := 118140960795 + 7957975 * 2 ^ 59
def prefixEnd_7957975 : Nat := 4983230072969 + 3 ^ 40 * 7957975 * 2
def baseEnd_7957975 : Nat := 4086266211463607119914445

theorem tailTrace_7957975 : CollatzResearch.WordTrace tailWord_7957975 prefixEnd_7957975 4086266211463607119914445 := by
  unfold tailWord_7957975
  simp only [CollatzResearch.WordTrace]
  refine ⟨290251193344623163770523379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193500795563082109180348919 290251193344623163770523379)
  ·
    refine ⟨435376790016934745655785069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290251193344623163770523379 435376790016934745655785069)
    ·
      refine ⟨163266296256350529620919401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435376790016934745655785069 163266296256350529620919401)
      ·
        refine ⟨122449722192262897215689551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163266296256350529620919401 122449722192262897215689551)
        ·
          refine ⟨183674583288394345823534327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122449722192262897215689551 183674583288394345823534327)
          ·
            refine ⟨275511874932591518735301491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183674583288394345823534327 275511874932591518735301491)
            ·
              refine ⟨413267812398887278102952237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275511874932591518735301491 413267812398887278102952237)
              ·
                refine ⟨154975429649582729288607089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413267812398887278102952237 154975429649582729288607089)
                ·
                  refine ⟨116231572237187046966455317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154975429649582729288607089 116231572237187046966455317)
                  ·
                    refine ⟨5448354948618142826552593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116231572237187046966455317 5448354948618142826552593)
                    ·
                      refine ⟨4086266211463607119914445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448354948618142826552593 4086266211463607119914445)
                      ·
                        rfl

theorem cell23_7957975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_7957975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957975 prefixEnd_7957975 := by exact prefixLift 7957975
  have htrace : WordTrace (prefixWord ++ tailWord_7957975) baseStart_7957975 baseEnd_7957975 := by
    simpa [prefixWord, tailWord_7957975, baseEnd_7957975] using wordTrace_append hprefix tailTrace_7957975
  have hstable : (prefixWord ++ tailWord_7957975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957975).length < 2 ^ (prefixWord ++ tailWord_7957975).sum := by decide
  have hdescent : baseEnd_7957975 < baseStart_7957975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957985 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 1, 6]
def baseStart_7957985 : Nat := 118140960795 + 7957985 * 2 ^ 59
def prefixEnd_7957985 : Nat := 4983230072969 + 3 ^ 40 * 7957985 * 2
def baseEnd_7957985 : Nat := 1362090448756717360263133

theorem tailTrace_7957985 : CollatzResearch.WordTrace tailWord_7957985 prefixEnd_7957985 1362090448756717360263133 := by
  unfold tailWord_7957985
  simp only [CollatzResearch.WordTrace]
  refine ⟨290251558074586935478387409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193501038716391290318924939 290251558074586935478387409)
  ·
    refine ⟨217688668555940201608790557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290251558074586935478387409 217688668555940201608790557)
    ·
      refine ⟨81633250708477575603296459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217688668555940201608790557 81633250708477575603296459)
      ·
        refine ⟨122449876062716363404944689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81633250708477575603296459 122449876062716363404944689)
        ·
          refine ⟨91837407047037272553708517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122449876062716363404944689 91837407047037272553708517)
          ·
            refine ⟨17219513821319488603820347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91837407047037272553708517 17219513821319488603820347)
            ·
              refine ⟨25829270731979232905730521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17219513821319488603820347 25829270731979232905730521)
              ·
                refine ⟨19371953048984424679297891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25829270731979232905730521 19371953048984424679297891)
                ·
                  refine ⟨29057929573476637018946837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19371953048984424679297891 29057929573476637018946837)
                  ·
                    refine ⟨1362090448756717360263133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29057929573476637018946837 1362090448756717360263133)
                    ·
                      rfl

theorem cell23_7957985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_7957985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957985 prefixEnd_7957985 := by exact prefixLift 7957985
  have htrace : WordTrace (prefixWord ++ tailWord_7957985) baseStart_7957985 baseEnd_7957985 := by
    simpa [prefixWord, tailWord_7957985, baseEnd_7957985] using wordTrace_append hprefix tailTrace_7957985
  have hstable : (prefixWord ++ tailWord_7957985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957985).length < 2 ^ (prefixWord ++ tailWord_7957985).sum := by decide
  have hdescent : baseEnd_7957985 < baseStart_7957985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957989 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 1, 5]
def baseStart_7957989 : Nat := 118140960795 + 7957989 * 2 ^ 59
def prefixEnd_7957989 : Nat := 4983230072969 + 3 ^ 40 * 7957989 * 2
def baseEnd_7957989 : Nat := 1362091133397590021713127

theorem tailTrace_7957989 : CollatzResearch.WordTrace tailWord_7957989 prefixEnd_7957989 1362091133397590021713127 := by
  unfold tailWord_7957989
  simp only [CollatzResearch.WordTrace]
  refine ⟨290251703966572444161533021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193501135977714962774355347 290251703966572444161533021)
  ·
    refine ⟨108844388987464666560574883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290251703966572444161533021 108844388987464666560574883)
    ·
      refine ⟨163266583481196999840862325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108844388987464666560574883 163266583481196999840862325)
      ·
        refine ⟨15306242201362218735080843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163266583481196999840862325 15306242201362218735080843)
        ·
          refine ⟨22959363302043328102621265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15306242201362218735080843 22959363302043328102621265)
          ·
            refine ⟨17219522476532496076965949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22959363302043328102621265 17219522476532496076965949)
            ·
              refine ⟨6457320928699686028862231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17219522476532496076965949 6457320928699686028862231)
              ·
                refine ⟨9685981393049529043293347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457320928699686028862231 9685981393049529043293347)
                ·
                  refine ⟨14528972089574293564940021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9685981393049529043293347 14528972089574293564940021)
                  ·
                    refine ⟨1362091133397590021713127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14528972089574293564940021 1362091133397590021713127)
                    ·
                      rfl

theorem cell23_7957989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_7957989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7957989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7957989 prefixEnd_7957989 := by exact prefixLift 7957989
  have htrace : WordTrace (prefixWord ++ tailWord_7957989) baseStart_7957989 baseEnd_7957989 := by
    simpa [prefixWord, tailWord_7957989, baseEnd_7957989] using wordTrace_append hprefix tailTrace_7957989
  have hstable : (prefixWord ++ tailWord_7957989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957989).length < 2 ^ (prefixWord ++ tailWord_7957989).sum := by decide
  have hdescent : baseEnd_7957989 < baseStart_7957989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958042 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3]
def baseStart_7958042 : Nat := 118140960795 + 7958042 * 2 ^ 59
def prefixEnd_7958042 : Nat := 4983230072969 + 3 ^ 40 * 7958042 * 2
def baseEnd_7958042 : Nat := 4086300614667458357776637

theorem tailTrace_7958042 : CollatzResearch.WordTrace tailWord_7958042 prefixEnd_7958042 4086300614667458357776637 := by
  unfold tailWord_7958042
  simp only [CollatzResearch.WordTrace]
  refine ⟨72563409258845108553303095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193502424690253622808808253 72563409258845108553303095)
  ·
    refine ⟨108845113888267662829954643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72563409258845108553303095 108845113888267662829954643)
    ·
      refine ⟨163267670832401494244931965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108845113888267662829954643 163267670832401494244931965)
      ·
        refine ⟨61225376562150560341849487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163267670832401494244931965 61225376562150560341849487)
        ·
          refine ⟨91838064843225840512774231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61225376562150560341849487 91838064843225840512774231)
          ·
            refine ⟨137757097264838760769161347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91838064843225840512774231 137757097264838760769161347)
            ·
              refine ⟨206635645897258141153742021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137757097264838760769161347 206635645897258141153742021)
              ·
                refine ⟨38744183605735901466326629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206635645897258141153742021 38744183605735901466326629)
                ·
                  refine ⟨7264534426075481524936243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38744183605735901466326629 7264534426075481524936243)
                  ·
                    refine ⟨10896801639113222287404365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7264534426075481524936243 10896801639113222287404365)
                    ·
                      refine ⟨4086300614667458357776637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10896801639113222287404365 4086300614667458357776637)
                      ·
                        rfl

theorem cell23_7958042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_7958042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958042 prefixEnd_7958042 := by exact prefixLift 7958042
  have htrace : WordTrace (prefixWord ++ tailWord_7958042) baseStart_7958042 baseEnd_7958042 := by
    simpa [prefixWord, tailWord_7958042, baseEnd_7958042] using wordTrace_append hprefix tailTrace_7958042
  have hstable : (prefixWord ++ tailWord_7958042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958042).length < 2 ^ (prefixWord ++ tailWord_7958042).sum := by decide
  have hdescent : baseEnd_7958042 < baseStart_7958042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958076 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 1, 3, 3]
def baseStart_7958076 : Nat := 118140960795 + 7958076 * 2 ^ 59
def prefixEnd_7958076 : Nat := 4983230072969 + 3 ^ 40 * 7958076 * 2
def baseEnd_7958076 : Nat := 4086318073009711224751481

theorem tailTrace_7958076 : CollatzResearch.WordTrace tailWord_7958076 prefixEnd_7958076 4086318073009711224751481 := by
  unfold tailWord_7958076
  simp only [CollatzResearch.WordTrace]
  refine ⟨145127438558628629009975041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193503251411504838679966721 145127438558628629009975041)
  ·
    refine ⟨108845578918971471757481281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145127438558628629009975041 108845578918971471757481281)
    ·
      refine ⟨81634184189228603818110961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108845578918971471757481281 81634184189228603818110961)
      ·
        refine ⟨61225638141921452863583221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81634184189228603818110961 61225638141921452863583221)
        ·
          refine ⟨5739903575805136205960927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61225638141921452863583221 5739903575805136205960927)
          ·
            refine ⟨8609855363707704308941391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739903575805136205960927 8609855363707704308941391)
            ·
              refine ⟨12914783045561556463412087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609855363707704308941391 12914783045561556463412087)
              ·
                refine ⟨19372174568342334695118131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12914783045561556463412087 19372174568342334695118131)
                ·
                  refine ⟨29058261852513502042677197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19372174568342334695118131 29058261852513502042677197)
                  ·
                    refine ⟨10896848194692563266003949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29058261852513502042677197 10896848194692563266003949)
                    ·
                      refine ⟨4086318073009711224751481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10896848194692563266003949 4086318073009711224751481)
                      ·
                        rfl

theorem cell23_7958076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_7958076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958076 prefixEnd_7958076 := by exact prefixLift 7958076
  have htrace : WordTrace (prefixWord ++ tailWord_7958076) baseStart_7958076 baseEnd_7958076 := by
    simpa [prefixWord, tailWord_7958076, baseEnd_7958076] using wordTrace_append hprefix tailTrace_7958076
  have hstable : (prefixWord ++ tailWord_7958076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958076).length < 2 ^ (prefixWord ++ tailWord_7958076).sum := by decide
  have hdescent : baseEnd_7958076 < baseStart_7958076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958085 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_7958085 : Nat := 118140960795 + 7958085 * 2 ^ 59
def prefixEnd_7958085 : Nat := 4983230072969 + 3 ^ 40 * 7958085 * 2
def baseEnd_7958085 : Nat := 4086322694335601689538939

theorem tailTrace_7958085 : CollatzResearch.WordTrace tailWord_7958085 prefixEnd_7958085 4086322694335601689538939 := by
  unfold tailWord_7958085
  simp only [CollatzResearch.WordTrace]
  refine ⟨290255205374224652557027709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193503470249483101704685139 290255205374224652557027709)
  ·
    refine ⟨108845702015334244708885391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290255205374224652557027709 108845702015334244708885391)
    ·
      refine ⟨163268553023001367063328087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108845702015334244708885391 163268553023001367063328087)
      ·
        refine ⟨244902829534502050594992131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163268553023001367063328087 244902829534502050594992131)
        ·
          refine ⟨367354244301753075892488197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244902829534502050594992131 367354244301753075892488197)
          ·
            refine ⟨68878920806578701729841537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367354244301753075892488197 68878920806578701729841537)
            ·
              refine ⟨51659190604934026297381153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68878920806578701729841537 51659190604934026297381153)
              ·
                refine ⟨38744392953700519723035865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51659190604934026297381153 38744392953700519723035865)
                ·
                  refine ⟨29058294715275389792276899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38744392953700519723035865 29058294715275389792276899)
                  ·
                    refine ⟨43587442072913084688415349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29058294715275389792276899 43587442072913084688415349)
                    ·
                      refine ⟨4086322694335601689538939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43587442072913084688415349 4086322694335601689538939)
                      ·
                        rfl

theorem cell23_7958085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_7958085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958085 prefixEnd_7958085 := by exact prefixLift 7958085
  have htrace : WordTrace (prefixWord ++ tailWord_7958085) baseStart_7958085 baseEnd_7958085 := by
    simpa [prefixWord, tailWord_7958085, baseEnd_7958085] using wordTrace_append hprefix tailTrace_7958085
  have hstable : (prefixWord ++ tailWord_7958085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958085).length < 2 ^ (prefixWord ++ tailWord_7958085).sum := by decide
  have hdescent : baseEnd_7958085 < baseStart_7958085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958122 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 7]
def baseStart_7958122 : Nat := 118140960795 + 7958122 * 2 ^ 59
def prefixEnd_7958122 : Nat := 4983230072969 + 3 ^ 40 * 7958122 * 2
def baseEnd_7958122 : Nat := 454037965902202004975141

theorem tailTrace_7958122 : CollatzResearch.WordTrace tailWord_7958122 prefixEnd_7958122 454037965902202004975141 := by
  unfold tailWord_7958122
  simp only [CollatzResearch.WordTrace]
  refine ⟨72564138718772651969031155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193504369916727071917416413 72564138718772651969031155)
  ·
    refine ⟨108846208078158977953546733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72564138718772651969031155 108846208078158977953546733)
    ·
      refine ⟨40817328029309616732580025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108846208078158977953546733 40817328029309616732580025)
      ·
        refine ⟨30612996021982212549435019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40817328029309616732580025 30612996021982212549435019)
        ·
          refine ⟨45919494032973318824152529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30612996021982212549435019 45919494032973318824152529)
          ·
            refine ⟨34439620524729989118114397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45919494032973318824152529 34439620524729989118114397)
            ·
              refine ⟨12914857696773745919292899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34439620524729989118114397 12914857696773745919292899)
              ·
                refine ⟨19372286545160618878939349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12914857696773745919292899 19372286545160618878939349)
                ·
                  refine ⟨454037965902202004975141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19372286545160618878939349 454037965902202004975141)
                  ·
                    rfl

theorem cell23_7958122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_7958122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958122 prefixEnd_7958122 := by exact prefixLift 7958122
  have htrace : WordTrace (prefixWord ++ tailWord_7958122) baseStart_7958122 baseEnd_7958122 := by
    simpa [prefixWord, tailWord_7958122, baseEnd_7958122] using wordTrace_append hprefix tailTrace_7958122
  have hstable : (prefixWord ++ tailWord_7958122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958122).length < 2 ^ (prefixWord ++ tailWord_7958122).sum := by decide
  have hdescent : baseEnd_7958122 < baseStart_7958122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958133 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7958133 : Nat := 118140960795 + 7958133 * 2 ^ 59
def prefixEnd_7958133 : Nat := 4983230072969 + 3 ^ 40 * 7958133 * 2
def baseEnd_7958133 : Nat := 4086347341407017501738719

theorem tailTrace_7958133 : CollatzResearch.WordTrace tailWord_7958133 prefixEnd_7958133 4086347341407017501738719 := by
  unfold tailWord_7958133
  simp only [CollatzResearch.WordTrace]
  refine ⟨290256956078050756754775053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193504637385367171169850035 290256956078050756754775053)
  ·
    refine ⟨108846358529269033783040645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290256956078050756754775053 108846358529269033783040645)
    ·
      refine ⟨20408692224237943834320121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108846358529269033783040645 20408692224237943834320121)
      ·
        refine ⟨15306519168178457875740091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20408692224237943834320121 15306519168178457875740091)
        ·
          refine ⟨22959778752267686813610137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15306519168178457875740091 22959778752267686813610137)
          ·
            refine ⟨17219834064200765110207603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22959778752267686813610137 17219834064200765110207603)
            ·
              refine ⟨25829751096301147665311405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17219834064200765110207603 25829751096301147665311405)
              ·
                refine ⟨9686156661112930374491777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25829751096301147665311405 9686156661112930374491777)
                ·
                  refine ⟨7264617495834697780868833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9686156661112930374491777 7264617495834697780868833)
                  ·
                    refine ⟨5448463121876023335651625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7264617495834697780868833 5448463121876023335651625)
                    ·
                      refine ⟨4086347341407017501738719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448463121876023335651625 4086347341407017501738719)
                      ·
                        rfl

theorem cell23_7958133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7958133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958133 prefixEnd_7958133 := by exact prefixLift 7958133
  have htrace : WordTrace (prefixWord ++ tailWord_7958133) baseStart_7958133 baseEnd_7958133 := by
    simpa [prefixWord, tailWord_7958133, baseEnd_7958133] using wordTrace_append hprefix tailTrace_7958133
  have hstable : (prefixWord ++ tailWord_7958133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958133).length < 2 ^ (prefixWord ++ tailWord_7958133).sum := by decide
  have hdescent : baseEnd_7958133 < baseStart_7958133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958135 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 6, 5]
def baseStart_7958135 : Nat := 118140960795 + 7958135 * 2 ^ 59
def prefixEnd_7958135 : Nat := 4983230072969 + 3 ^ 40 * 7958135 * 2
def baseEnd_7958135 : Nat := 1362116122789442164637903

theorem tailTrace_7958135 : CollatzResearch.WordTrace tailWord_7958135 prefixEnd_7958135 1362116122789442164637903 := by
  unfold tailWord_7958135
  simp only [CollatzResearch.WordTrace]
  refine ⟨290257029024043511096347859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193504686016029007397565239 290257029024043511096347859)
  ·
    refine ⟨435385543536065266644521789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290257029024043511096347859 435385543536065266644521789)
    ·
      refine ⟨163269578826024474991695671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435385543536065266644521789 163269578826024474991695671)
      ·
        refine ⟨244904368239036712487543507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163269578826024474991695671 244904368239036712487543507)
        ·
          refine ⟨367356552358555068731315261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244904368239036712487543507 367356552358555068731315261)
          ·
            refine ⟨137758707134458150774243223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367356552358555068731315261 137758707134458150774243223)
            ·
              refine ⟨206638060701687226161364835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137758707134458150774243223 206638060701687226161364835)
              ·
                refine ⟨309957091052530839242047253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206638060701687226161364835 309957091052530839242047253)
                ·
                  refine ⟨14529238643087383089470965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 309957091052530839242047253 14529238643087383089470965)
                  ·
                    refine ⟨1362116122789442164637903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14529238643087383089470965 1362116122789442164637903)
                    ·
                      rfl

theorem cell23_7958135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_7958135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958135 prefixEnd_7958135 := by exact prefixLift 7958135
  have htrace : WordTrace (prefixWord ++ tailWord_7958135) baseStart_7958135 baseEnd_7958135 := by
    simpa [prefixWord, tailWord_7958135, baseEnd_7958135] using wordTrace_append hprefix tailTrace_7958135
  have hstable : (prefixWord ++ tailWord_7958135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958135).length < 2 ^ (prefixWord ++ tailWord_7958135).sum := by decide
  have hdescent : baseEnd_7958135 < baseStart_7958135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958192 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 3]
def baseStart_7958192 : Nat := 118140960795 + 7958192 * 2 ^ 59
def prefixEnd_7958192 : Nat := 4983230072969 + 3 ^ 40 * 7958192 * 2
def baseEnd_7958192 : Nat := 4086377636765632770900947

theorem tailTrace_7958192 : CollatzResearch.WordTrace tailWord_7958192 prefixEnd_7958192 4086377636765632770900947 := by
  unfold tailWord_7958192
  simp only [CollatzResearch.WordTrace]
  refine ⟨145129553992418504915586415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193506071989891339887448553 145129553992418504915586415)
  ·
    refine ⟨217694330988627757373379623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145129553992418504915586415 217694330988627757373379623)
    ·
      refine ⟨326541496482941636060069435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217694330988627757373379623 326541496482941636060069435)
      ·
        refine ⟨489812244724412454090104153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326541496482941636060069435 489812244724412454090104153)
        ·
          refine ⟨367359183543309340567578115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489812244724412454090104153 367359183543309340567578115)
          ·
            refine ⟨551038775314964010851367173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367359183543309340567578115 551038775314964010851367173)
            ·
              refine ⟨103319770371555752034631345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 551038775314964010851367173 103319770371555752034631345)
              ·
                refine ⟨77489827778666814025973509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103319770371555752034631345 77489827778666814025973509)
                ·
                  refine ⟨14529342708500027629870033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77489827778666814025973509 14529342708500027629870033)
                  ·
                    refine ⟨10897007031375020722402525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14529342708500027629870033 10897007031375020722402525)
                    ·
                      refine ⟨4086377636765632770900947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10897007031375020722402525 4086377636765632770900947)
                      ·
                        rfl

theorem cell23_7958192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 3].length) (baseStart_7958192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958192 prefixEnd_7958192 := by exact prefixLift 7958192
  have htrace : WordTrace (prefixWord ++ tailWord_7958192) baseStart_7958192 baseEnd_7958192 := by
    simpa [prefixWord, tailWord_7958192, baseEnd_7958192] using wordTrace_append hprefix tailTrace_7958192
  have hstable : (prefixWord ++ tailWord_7958192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958192).length < 2 ^ (prefixWord ++ tailWord_7958192).sum := by decide
  have hdescent : baseEnd_7958192 < baseStart_7958192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958199 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 3, 4]
def baseStart_7958199 : Nat := 118140960795 + 7958199 * 2 ^ 59
def prefixEnd_7958199 : Nat := 4983230072969 + 3 ^ 40 * 7958199 * 2
def baseEnd_7958199 : Nat := 1362127077043404747837805

theorem tailTrace_7958199 : CollatzResearch.WordTrace tailWord_7958199 prefixEnd_7958199 1362127077043404747837805 := by
  unfold tailWord_7958199
  simp only [CollatzResearch.WordTrace]
  refine ⟨290259363295811650026677651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193506242197207766684451767 290259363295811650026677651)
  ·
    refine ⟨435389044943717475040016477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290259363295811650026677651 435389044943717475040016477)
    ·
      refine ⟨163270891853894053140006179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435389044943717475040016477 163270891853894053140006179)
      ·
        refine ⟨244906337780841079710009269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163270891853894053140006179 244906337780841079710009269)
        ·
          refine ⟨22959969166953851222813369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244906337780841079710009269 22959969166953851222813369)
          ·
            refine ⟨17219976875215388417110027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22959969166953851222813369 17219976875215388417110027)
            ·
              refine ⟨25829965312823082625665041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17219976875215388417110027 25829965312823082625665041)
              ·
                refine ⟨19372473984617311969248781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25829965312823082625665041 19372473984617311969248781)
                ·
                  refine ⟨7264677744231491988468293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19372473984617311969248781 7264677744231491988468293)
                  ·
                    refine ⟨1362127077043404747837805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7264677744231491988468293 1362127077043404747837805)
                    ·
                      rfl

theorem cell23_7958199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_7958199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958199 prefixEnd_7958199 := by exact prefixLift 7958199
  have htrace : WordTrace (prefixWord ++ tailWord_7958199) baseStart_7958199 baseEnd_7958199 := by
    simpa [prefixWord, tailWord_7958199, baseEnd_7958199] using wordTrace_append hprefix tailTrace_7958199
  have hstable : (prefixWord ++ tailWord_7958199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958199).length < 2 ^ (prefixWord ++ tailWord_7958199).sum := by decide
  have hdescent : baseEnd_7958199 < baseStart_7958199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958206 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_7958206 : Nat := 118140960795 + 7958206 * 2 ^ 59
def prefixEnd_7958206 : Nat := 4983230072969 + 3 ^ 40 * 7958206 * 2
def baseEnd_7958206 : Nat := 4086384825494795716125883

theorem tailTrace_7958206 : CollatzResearch.WordTrace tailWord_7958206 prefixEnd_7958206 4086384825494795716125883 := by
  unfold tailWord_7958206
  simp only [CollatzResearch.WordTrace]
  refine ⟨36282452325848286277772809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193506412404524193481454981 36282452325848286277772809)
  ·
    refine ⟨27211839244386214708329607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36282452325848286277772809 27211839244386214708329607)
    ·
      refine ⟨40817758866579322062494411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27211839244386214708329607 40817758866579322062494411)
      ·
        refine ⟨61226638299868983093741617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40817758866579322062494411 61226638299868983093741617)
        ·
          refine ⟨45919978724901737320306213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61226638299868983093741617 45919978724901737320306213)
          ·
            refine ⟨8609996010919075747557415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45919978724901737320306213 8609996010919075747557415)
            ·
              refine ⟨12914994016378613621336123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609996010919075747557415 12914994016378613621336123)
              ·
                refine ⟨19372491024567920432004185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12914994016378613621336123 19372491024567920432004185)
                ·
                  refine ⟨14529368268425940324003139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19372491024567920432004185 14529368268425940324003139)
                  ·
                    refine ⟨21794052402638910486004709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14529368268425940324003139 21794052402638910486004709)
                    ·
                      refine ⟨4086384825494795716125883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21794052402638910486004709 4086384825494795716125883)
                      ·
                        rfl

theorem cell23_7958206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_7958206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958206 prefixEnd_7958206 := by exact prefixLift 7958206
  have htrace : WordTrace (prefixWord ++ tailWord_7958206) baseStart_7958206 baseEnd_7958206 := by
    simpa [prefixWord, tailWord_7958206, baseEnd_7958206] using wordTrace_append hprefix tailTrace_7958206
  have hstable : (prefixWord ++ tailWord_7958206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958206).length < 2 ^ (prefixWord ++ tailWord_7958206).sum := by decide
  have hdescent : baseEnd_7958206 < baseStart_7958206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958212 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 8]
def baseStart_7958212 : Nat := 118140960795 + 7958212 * 2 ^ 59
def prefixEnd_7958212 : Nat := 4983230072969 + 3 ^ 40 * 7958212 * 2
def baseEnd_7958212 : Nat := 454043100708746965850095

theorem tailTrace_7958212 : CollatzResearch.WordTrace tailWord_7958212 prefixEnd_7958212 454043100708746965850095 := by
  unfold tailWord_7958212
  simp only [CollatzResearch.WordTrace]
  refine ⟨145129918722382276623450445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193506558296509702164600593 145129918722382276623450445)
  ·
    refine ⟨54423719520893353733793917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145129918722382276623450445 54423719520893353733793917)
    ·
      refine ⟨20408894820335007650172719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54423719520893353733793917 20408894820335007650172719)
      ·
        refine ⟨30613342230502511475259079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20408894820335007650172719 30613342230502511475259079)
        ·
          refine ⟨45920013345753767212888619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30613342230502511475259079 45920013345753767212888619)
          ·
            refine ⟨68880020018630650819332929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45920013345753767212888619 68880020018630650819332929)
            ·
              refine ⟨51660015013972988114499697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68880020018630650819332929 51660015013972988114499697)
              ·
                refine ⟨38745011260479741085874773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51660015013972988114499697 38745011260479741085874773)
                ·
                  refine ⟨454043100708746965850095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38745011260479741085874773 454043100708746965850095)
                  ·
                    rfl

theorem cell23_7958212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_7958212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958212 prefixEnd_7958212 := by exact prefixLift 7958212
  have htrace : WordTrace (prefixWord ++ tailWord_7958212) baseStart_7958212 baseEnd_7958212 := by
    simpa [prefixWord, tailWord_7958212, baseEnd_7958212] using wordTrace_append hprefix tailTrace_7958212
  have hstable : (prefixWord ++ tailWord_7958212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958212).length < 2 ^ (prefixWord ++ tailWord_7958212).sum := by decide
  have hdescent : baseEnd_7958212 < baseStart_7958212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958216 : List Nat := [2, 1, 3, 1, 2, 2, 4, 3, 1, 4]
def baseStart_7958216 : Nat := 118140960795 + 7958216 * 2 ^ 59
def prefixEnd_7958216 : Nat := 4983230072969 + 3 ^ 40 * 7958216 * 2
def baseEnd_7958216 : Nat := 1362129986767113559000279

theorem tailTrace_7958216 : CollatzResearch.WordTrace tailWord_7958216 prefixEnd_7958216 1362129986767113559000279 := by
  unfold tailWord_7958216
  simp only [CollatzResearch.WordTrace]
  refine ⟨145129991668375030965023251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193506655557833374620031001 145129991668375030965023251)
  ·
    refine ⟨217694987502562546447534877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145129991668375030965023251 217694987502562546447534877)
    ·
      refine ⟨81635620313460954917825579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217694987502562546447534877 81635620313460954917825579)
      ·
        refine ⟨122453430470191432376738369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81635620313460954917825579 122453430470191432376738369)
        ·
          refine ⟨91840072852643574282553777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122453430470191432376738369 91840072852643574282553777)
          ·
            refine ⟨68880054639482680711915333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91840072852643574282553777 68880054639482680711915333)
            ·
              refine ⟨12915010244903002633484125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68880054639482680711915333 12915010244903002633484125)
              ·
                refine ⟨4843128841838625987556547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12915010244903002633484125 4843128841838625987556547)
                ·
                  refine ⟨7264693262757938981334821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4843128841838625987556547 7264693262757938981334821)
                  ·
                    refine ⟨1362129986767113559000279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7264693262757938981334821 1362129986767113559000279)
                    ·
                      rfl

theorem cell23_7958216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_7958216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958216 prefixEnd_7958216 := by exact prefixLift 7958216
  have htrace : WordTrace (prefixWord ++ tailWord_7958216) baseStart_7958216 baseEnd_7958216 := by
    simpa [prefixWord, tailWord_7958216, baseEnd_7958216] using wordTrace_append hprefix tailTrace_7958216
  have hstable : (prefixWord ++ tailWord_7958216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958216).length < 2 ^ (prefixWord ++ tailWord_7958216).sum := by decide
  have hdescent : baseEnd_7958216 < baseStart_7958216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958273 : List Nat := [1, 2, 4, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_7958273 : Nat := 118140960795 + 7958273 * 2 ^ 59
def prefixEnd_7958273 : Nat := 4983230072969 + 3 ^ 40 * 7958273 * 2
def baseEnd_7958273 : Nat := 4086419228698646953988075

theorem tailTrace_7958273 : CollatzResearch.WordTrace tailWord_7958273 prefixEnd_7958273 4086419228698646953988075 := by
  unfold tailWord_7958273
  simp only [CollatzResearch.WordTrace]
  refine ⟨290262062297543560664871473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193508041531695707109914315 290262062297543560664871473)
  ·
    refine ⟨217696546723157670498653605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290262062297543560664871473 217696546723157670498653605)
    ·
      refine ⟨40818102510592063218497551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217696546723157670498653605 40818102510592063218497551)
      ·
        refine ⟨61227153765888094827746327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40818102510592063218497551 61227153765888094827746327)
        ·
          refine ⟨91840730648832142241619491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61227153765888094827746327 91840730648832142241619491)
          ·
            refine ⟨137761095973248213362429237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91840730648832142241619491 137761095973248213362429237)
            ·
              refine ⟨12915102747492020002727741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137761095973248213362429237 12915102747492020002727741)
              ·
                refine ⟨4843163530309507501022903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12915102747492020002727741 4843163530309507501022903)
                ·
                  refine ⟨7264745295464261251534355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4843163530309507501022903 7264745295464261251534355)
                  ·
                    refine ⟨10897117943196391877301533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7264745295464261251534355 10897117943196391877301533)
                    ·
                      refine ⟨4086419228698646953988075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10897117943196391877301533 4086419228698646953988075)
                      ·
                        rfl

theorem cell23_7958273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_7958273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958273 prefixEnd_7958273 := by exact prefixLift 7958273
  have htrace : WordTrace (prefixWord ++ tailWord_7958273) baseStart_7958273 baseEnd_7958273 := by
    simpa [prefixWord, tailWord_7958273, baseEnd_7958273] using wordTrace_append hprefix tailTrace_7958273
  have hstable : (prefixWord ++ tailWord_7958273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958273).length < 2 ^ (prefixWord ++ tailWord_7958273).sum := by decide
  have hdescent : baseEnd_7958273 < baseStart_7958273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958289 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 2, 4]
def baseStart_7958289 : Nat := 118140960795 + 7958289 * 2 ^ 59
def prefixEnd_7958289 : Nat := 4983230072969 + 3 ^ 40 * 7958289 * 2
def baseEnd_7958289 : Nat := 1362142481463039630462667

theorem tailTrace_7958289 : CollatzResearch.WordTrace tailWord_7958289 prefixEnd_7958289 1362142481463039630462667 := by
  unfold tailWord_7958289
  simp only [CollatzResearch.WordTrace]
  refine ⟨290262645865485595397453921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193508430576990396931635947 290262645865485595397453921)
  ·
    refine ⟨217696984399114196548090441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290262645865485595397453921 217696984399114196548090441)
    ·
      refine ⟨163272738299335647411067831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217696984399114196548090441 163272738299335647411067831)
      ·
        refine ⟨244909107449003471116601747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163272738299335647411067831 244909107449003471116601747)
        ·
          refine ⟨367363661173505206674902621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244909107449003471116601747 367363661173505206674902621)
          ·
            refine ⟨137761372940064452503088483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367363661173505206674902621 137761372940064452503088483)
            ·
              refine ⟨206642059410096678754632725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137761372940064452503088483 206642059410096678754632725)
              ·
                refine ⟨9686346534848281816623409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206642059410096678754632725 9686346534848281816623409)
                ·
                  refine ⟨7264759901136211362467557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9686346534848281816623409 7264759901136211362467557)
                  ·
                    refine ⟨1362142481463039630462667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7264759901136211362467557 1362142481463039630462667)
                    ·
                      rfl

theorem cell23_7958289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_7958289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958289 prefixEnd_7958289 := by exact prefixLift 7958289
  have htrace : WordTrace (prefixWord ++ tailWord_7958289) baseStart_7958289 baseEnd_7958289 := by
    simpa [prefixWord, tailWord_7958289, baseEnd_7958289] using wordTrace_append hprefix tailTrace_7958289
  have hstable : (prefixWord ++ tailWord_7958289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958289).length < 2 ^ (prefixWord ++ tailWord_7958289).sum := by decide
  have hdescent : baseEnd_7958289 < baseStart_7958289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958290 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7958290 : Nat := 118140960795 + 7958290 * 2 ^ 59
def prefixEnd_7958290 : Nat := 4983230072969 + 3 ^ 40 * 7958290 * 2
def baseEnd_7958290 : Nat := 4086427957869773387475497

theorem tailTrace_7958290 : CollatzResearch.WordTrace tailWord_7958290 prefixEnd_7958290 4086427957869773387475497 := by
  unfold tailWord_7958290
  simp only [CollatzResearch.WordTrace]
  refine ⟨72565670584620493142060081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193508454892321315045493549 72565670584620493142060081)
  ·
    refine ⟨54424252938465369856545061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72565670584620493142060081 54424252938465369856545061)
    ·
      refine ⟨10204547425962256848102199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54424252938465369856545061 10204547425962256848102199)
      ·
        refine ⟨15306821138943385272153299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10204547425962256848102199 15306821138943385272153299)
        ·
          refine ⟨22960231708415077908229949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15306821138943385272153299 22960231708415077908229949)
          ·
            refine ⟨8610086890655654215586231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22960231708415077908229949 8610086890655654215586231)
            ·
              refine ⟨12915130335983481323379347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610086890655654215586231 12915130335983481323379347)
              ·
                refine ⟨19372695503975221985069021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915130335983481323379347 19372695503975221985069021)
                ·
                  refine ⟨7264760813990708244400883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19372695503975221985069021 7264760813990708244400883)
                  ·
                    refine ⟨10897141220986062366601325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7264760813990708244400883 10897141220986062366601325)
                    ·
                      refine ⟨4086427957869773387475497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10897141220986062366601325 4086427957869773387475497)
                      ·
                        rfl

theorem cell23_7958290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7958290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958290 prefixEnd_7958290 := by exact prefixLift 7958290
  have htrace : WordTrace (prefixWord ++ tailWord_7958290) baseStart_7958290 baseEnd_7958290 := by
    simpa [prefixWord, tailWord_7958290, baseEnd_7958290] using wordTrace_append hprefix tailTrace_7958290
  have hstable : (prefixWord ++ tailWord_7958290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958290).length < 2 ^ (prefixWord ++ tailWord_7958290).sum := by decide
  have hdescent : baseEnd_7958290 < baseStart_7958290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958306 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_7958306 : Nat := 118140960795 + 7958306 * 2 ^ 59
def prefixEnd_7958306 : Nat := 4983230072969 + 3 ^ 40 * 7958306 * 2
def baseEnd_7958306 : Nat := 1362145391186748441625141

theorem tailTrace_7958306 : CollatzResearch.WordTrace tailWord_7958306 prefixEnd_7958306 1362145391186748441625141 := by
  unfold tailWord_7958306
  simp only [CollatzResearch.WordTrace]
  refine ⟨72565816476606001825205693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193508843937616004867215181 72565816476606001825205693)
  ·
    refine ⟨27212181178727250684452135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72565816476606001825205693 27212181178727250684452135)
    ·
      refine ⟨40818271768090876026678203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27212181178727250684452135 40818271768090876026678203)
      ·
        refine ⟨61227407652136314040017305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40818271768090876026678203 61227407652136314040017305)
        ·
          refine ⟨45920555739102235530012979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61227407652136314040017305 45920555739102235530012979)
          ·
            refine ⟨68880833608653353295019469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45920555739102235530012979 68880833608653353295019469)
            ·
              refine ⟨25830312603245007485632301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68880833608653353295019469 25830312603245007485632301)
              ·
                refine ⟨9686367226216877807112113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25830312603245007485632301 9686367226216877807112113)
                ·
                  refine ⟨7264775419662658355334085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9686367226216877807112113 7264775419662658355334085)
                  ·
                    refine ⟨1362145391186748441625141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7264775419662658355334085 1362145391186748441625141)
                    ·
                      rfl

theorem cell23_7958306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_7958306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958306 prefixEnd_7958306 := by exact prefixLift 7958306
  have htrace : WordTrace (prefixWord ++ tailWord_7958306) baseStart_7958306 baseEnd_7958306 := by
    simpa [prefixWord, tailWord_7958306, baseEnd_7958306] using wordTrace_append hprefix tailTrace_7958306
  have hstable : (prefixWord ++ tailWord_7958306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958306).length < 2 ^ (prefixWord ++ tailWord_7958306).sum := by decide
  have hdescent : baseEnd_7958306 < baseStart_7958306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958316 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 3]
def baseStart_7958316 : Nat := 118140960795 + 7958316 * 2 ^ 59
def prefixEnd_7958316 : Nat := 4983230072969 + 3 ^ 40 * 7958316 * 2
def baseEnd_7958316 : Nat := 4086441308366790285750377

theorem tailTrace_7958316 : CollatzResearch.WordTrace tailWord_7958316 prefixEnd_7958316 4086441308366790285750377 := by
  unfold tailWord_7958316
  simp only [CollatzResearch.WordTrace]
  refine ⟨145131815318193889504343401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193509087090925186005791201 145131815318193889504343401)
  ·
    refine ⟨108848861488645417128257551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145131815318193889504343401 108848861488645417128257551)
    ·
      refine ⟨163273292232968125692386327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108848861488645417128257551 163273292232968125692386327)
      ·
        refine ⟨244909938349452188538579491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163273292232968125692386327 244909938349452188538579491)
        ·
          refine ⟨367364907524178282807869237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244909938349452188538579491 367364907524178282807869237)
          ·
            refine ⟨34440460080391714013237741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367364907524178282807869237 34440460080391714013237741)
            ·
              refine ⟨12915172530146892754964153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34440460080391714013237741 12915172530146892754964153)
              ·
                refine ⟨9686379397610169566223115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12915172530146892754964153 9686379397610169566223115)
                ·
                  refine ⟨14529569096415254349334673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9686379397610169566223115 14529569096415254349334673)
                  ·
                    refine ⟨10897176822311440762001005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14529569096415254349334673 10897176822311440762001005)
                    ·
                      refine ⟨4086441308366790285750377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10897176822311440762001005 4086441308366790285750377)
                      ·
                        rfl

theorem cell23_7958316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_7958316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958316 prefixEnd_7958316 := by exact prefixLift 7958316
  have htrace : WordTrace (prefixWord ++ tailWord_7958316) baseStart_7958316 baseEnd_7958316 := by
    simpa [prefixWord, tailWord_7958316, baseEnd_7958316] using wordTrace_append hprefix tailTrace_7958316
  have hstable : (prefixWord ++ tailWord_7958316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958316).length < 2 ^ (prefixWord ++ tailWord_7958316).sum := by decide
  have hdescent : baseEnd_7958316 < baseStart_7958316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958326 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7958326 : Nat := 118140960795 + 7958326 * 2 ^ 59
def prefixEnd_7958326 : Nat := 4983230072969 + 3 ^ 40 * 7958326 * 2
def baseEnd_7958326 : Nat := 4086446443173335246625331

theorem tailTrace_7958326 : CollatzResearch.WordTrace tailWord_7958326 prefixEnd_7958326 4086446443173335246625331 := by
  unfold tailWord_7958326
  simp only [CollatzResearch.WordTrace]
  refine ⟨18141499710396971919784427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193509330244234367144367221 18141499710396971919784427)
  ·
    refine ⟨27212249565595457879676641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18141499710396971919784427 27212249565595457879676641)
    ·
      refine ⟨20409187174196593409757481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27212249565595457879676641 20409187174196593409757481)
      ·
        refine ⟨15306890380647445057318111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20409187174196593409757481 15306890380647445057318111)
        ·
          refine ⟨22960335570971167585977167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15306890380647445057318111 22960335570971167585977167)
          ·
            refine ⟨34440503356456751378965751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22960335570971167585977167 34440503356456751378965751)
            ·
              refine ⟨51660755034685127068448627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34440503356456751378965751 51660755034685127068448627)
              ·
                refine ⟨77491132552027690602672941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51660755034685127068448627 77491132552027690602672941)
                ·
                  refine ⟨29059174707010383976002353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77491132552027690602672941 29059174707010383976002353)
                  ·
                    refine ⟨21794381030257787982001765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29059174707010383976002353 21794381030257787982001765)
                    ·
                      refine ⟨4086446443173335246625331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21794381030257787982001765 4086446443173335246625331)
                      ·
                        rfl

theorem cell23_7958326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7958326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958326 prefixEnd_7958326 := by exact prefixLift 7958326
  have htrace : WordTrace (prefixWord ++ tailWord_7958326) baseStart_7958326 baseEnd_7958326 := by
    simpa [prefixWord, tailWord_7958326, baseEnd_7958326] using wordTrace_append hprefix tailTrace_7958326
  have hstable : (prefixWord ++ tailWord_7958326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958326).length < 2 ^ (prefixWord ++ tailWord_7958326).sum := by decide
  have hdescent : baseEnd_7958326 < baseStart_7958326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958389 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_7958389 : Nat := 118140960795 + 7958389 * 2 ^ 59
def prefixEnd_7958389 : Nat := 4983230072969 + 3 ^ 40 * 7958389 * 2
def baseEnd_7958389 : Nat := 4086478792454568500137541

theorem tailTrace_7958389 : CollatzResearch.WordTrace tailWord_7958389 prefixEnd_7958389 4086478792454568500137541 := by
  unfold tailWord_7958389
  simp only [CollatzResearch.WordTrace]
  refine ⟨290266293165123312476094221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193510862110082208317396147 290266293165123312476094221)
  ·
    refine ⟨108849859936921242178535333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290266293165123312476094221 108849859936921242178535333)
    ·
      refine ⟨20409348738172732908475375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108849859936921242178535333 20409348738172732908475375)
      ·
        refine ⟨30614023107259099362713063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20409348738172732908475375 30614023107259099362713063)
        ·
          refine ⟨45921034660888649044069595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30614023107259099362713063 45921034660888649044069595)
          ·
            refine ⟨68881551991332973566104393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45921034660888649044069595 68881551991332973566104393)
            ·
              refine ⟨51661163993499730174578295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68881551991332973566104393 51661163993499730174578295)
              ·
                refine ⟨77491745990249595261867443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51661163993499730174578295 77491745990249595261867443)
                ·
                  refine ⟨116237618985374392892801165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77491745990249595261867443 116237618985374392892801165)
                  ·
                    refine ⟨43589107119515397334800437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116237618985374392892801165 43589107119515397334800437)
                    ·
                      refine ⟨4086478792454568500137541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43589107119515397334800437 4086478792454568500137541)
                      ·
                        rfl

theorem cell23_7958389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_7958389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958389 prefixEnd_7958389 := by exact prefixLift 7958389
  have htrace : WordTrace (prefixWord ++ tailWord_7958389) baseStart_7958389 baseEnd_7958389 := by
    simpa [prefixWord, tailWord_7958389, baseEnd_7958389] using wordTrace_append hprefix tailTrace_7958389
  have hstable : (prefixWord ++ tailWord_7958389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958389).length < 2 ^ (prefixWord ++ tailWord_7958389).sum := by decide
  have hdescent : baseEnd_7958389 < baseStart_7958389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958403 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 4, 2, 2]
def baseStart_7958403 : Nat := 118140960795 + 7958403 * 2 ^ 59
def prefixEnd_7958403 : Nat := 4983230072969 + 3 ^ 40 * 7958403 * 2
def baseEnd_7958403 : Nat := 4086485981183731445362477

theorem tailTrace_7958403 : CollatzResearch.WordTrace tailWord_7958403 prefixEnd_7958403 4086485981183731445362477 := by
  unfold tailWord_7958403
  simp only [CollatzResearch.WordTrace]
  refine ⟨290266803787072592867103863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193511202524715061911402575 290266803787072592867103863)
  ·
    refine ⟨435400205680608889300655795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290266803787072592867103863 435400205680608889300655795)
    ·
      refine ⟨653100308520913333950983693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435400205680608889300655795 653100308520913333950983693)
      ·
        refine ⟨244912615695342500231618885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653100308520913333950983693 244912615695342500231618885)
        ·
          refine ⟨45921115442876718793428541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244912615695342500231618885 45921115442876718793428541)
          ·
            refine ⟨17220418291078769547535703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45921115442876718793428541 17220418291078769547535703)
            ·
              refine ⟨25830627436618154321303555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17220418291078769547535703 25830627436618154321303555)
              ·
                refine ⟨38745941154927231481955333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25830627436618154321303555 38745941154927231481955333)
                ·
                  refine ⟨7264863966548855902866625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38745941154927231481955333 7264863966548855902866625)
                  ·
                    refine ⟨5448647974911641927149969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7264863966548855902866625 5448647974911641927149969)
                    ·
                      refine ⟨4086485981183731445362477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448647974911641927149969 4086485981183731445362477)
                      ·
                        rfl

theorem cell23_7958403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_7958403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958403 prefixEnd_7958403 := by exact prefixLift 7958403
  have htrace : WordTrace (prefixWord ++ tailWord_7958403) baseStart_7958403 baseEnd_7958403 := by
    simpa [prefixWord, tailWord_7958403, baseEnd_7958403] using wordTrace_append hprefix tailTrace_7958403
  have hstable : (prefixWord ++ tailWord_7958403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958403).length < 2 ^ (prefixWord ++ tailWord_7958403).sum := by decide
  have hdescent : baseEnd_7958403 < baseStart_7958403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958409 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 7]
def baseStart_7958409 : Nat := 118140960795 + 7958409 * 2 ^ 59
def prefixEnd_7958409 : Nat := 4983230072969 + 3 ^ 40 * 7958409 * 2
def baseEnd_7958409 : Nat := 454054340229739824654161

theorem tailTrace_7958409 : CollatzResearch.WordTrace tailWord_7958409 prefixEnd_7958409 454054340229739824654161 := by
  unfold tailWord_7958409
  simp only [CollatzResearch.WordTrace]
  refine ⟨290267022625050855891822281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193511348416700570594548187 290267022625050855891822281)
  ·
    refine ⟨217700266968788141918866711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290267022625050855891822281 217700266968788141918866711)
    ·
      refine ⟨326550400453182212878300067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217700266968788141918866711 326550400453182212878300067)
      ·
        refine ⟨489825600679773319317450101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326550400453182212878300067 489825600679773319317450101)
        ·
          refine ⟨45921150063728748686010947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 489825600679773319317450101 45921150063728748686010947)
          ·
            refine ⟨68881725095593123029016421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45921150063728748686010947 68881725095593123029016421)
            ·
              refine ⟨12915323455423710567940579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68881725095593123029016421 12915323455423710567940579)
              ·
                refine ⟨19372985183135565851910869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915323455423710567940579 19372985183135565851910869)
                ·
                  refine ⟨454054340229739824654161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19372985183135565851910869 454054340229739824654161)
                  ·
                    rfl

theorem cell23_7958409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 7].length) (baseStart_7958409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958409 prefixEnd_7958409 := by exact prefixLift 7958409
  have htrace : WordTrace (prefixWord ++ tailWord_7958409) baseStart_7958409 baseEnd_7958409 := by
    simpa [prefixWord, tailWord_7958409, baseEnd_7958409] using wordTrace_append hprefix tailTrace_7958409
  have hstable : (prefixWord ++ tailWord_7958409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958409).length < 2 ^ (prefixWord ++ tailWord_7958409).sum := by decide
  have hdescent : baseEnd_7958409 < baseStart_7958409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958420 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_7958420 : Nat := 118140960795 + 7958420 * 2 ^ 59
def prefixEnd_7958420 : Nat := 4983230072969 + 3 ^ 40 * 7958420 * 2
def baseEnd_7958420 : Nat := 4086494710354857878849899

theorem tailTrace_7958420 : CollatzResearch.WordTrace tailWord_7958420 prefixEnd_7958420 4086494710354857878849899 := by
  unfold tailWord_7958420
  simp only [CollatzResearch.WordTrace]
  refine ⟨145133711914005502385236357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193511615885340669846981809 145133711914005502385236357)
  ·
    refine ⟨27212570983876031697231817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145133711914005502385236357 27212570983876031697231817)
    ·
      refine ⟨20409428237907023772923863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27212570983876031697231817 20409428237907023772923863)
      ·
        refine ⟨30614142356860535659385795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20409428237907023772923863 30614142356860535659385795)
        ·
          refine ⟨45921213535290803489078693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30614142356860535659385795 45921213535290803489078693)
          ·
            refine ⟨8610227537867025654202255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45921213535290803489078693 8610227537867025654202255)
            ·
              refine ⟨12915341306800538481303383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610227537867025654202255 12915341306800538481303383)
              ·
                refine ⟨19373011960200807721955075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915341306800538481303383 19373011960200807721955075)
                ·
                  refine ⟨29059517940301211582932613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19373011960200807721955075 29059517940301211582932613)
                  ·
                    refine ⟨5448659613806477171799865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29059517940301211582932613 5448659613806477171799865)
                    ·
                      refine ⟨4086494710354857878849899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448659613806477171799865 4086494710354857878849899)
                      ·
                        rfl

theorem cell23_7958420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_7958420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958420 prefixEnd_7958420 := by exact prefixLift 7958420
  have htrace : WordTrace (prefixWord ++ tailWord_7958420) baseStart_7958420 baseEnd_7958420 := by
    simpa [prefixWord, tailWord_7958420, baseEnd_7958420] using wordTrace_append hprefix tailTrace_7958420
  have hstable : (prefixWord ++ tailWord_7958420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958420).length < 2 ^ (prefixWord ++ tailWord_7958420).sum := by decide
  have hdescent : baseEnd_7958420 < baseStart_7958420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958459 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 4]
def baseStart_7958459 : Nat := 118140960795 + 7958459 * 2 ^ 59
def prefixEnd_7958459 : Nat := 4983230072969 + 3 ^ 40 * 7958459 * 2
def baseEnd_7958459 : Nat := 4086514736100383226262219

theorem tailTrace_7958459 : CollatzResearch.WordTrace tailWord_7958459 prefixEnd_7958459 4086514736100383226262219 := by
  unfold tailWord_7958459
  simp only [CollatzResearch.WordTrace]
  refine ⟨290268846274869714431142431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193512564183246476287428287 290268846274869714431142431)
  ·
    refine ⟨435403269412304571646713647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290268846274869714431142431 435403269412304571646713647)
    ·
      refine ⟨653104904118456857470070471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435403269412304571646713647 653104904118456857470070471)
      ·
        refine ⟨979657356177685286205105707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653104904118456857470070471 979657356177685286205105707)
        ·
          refine ⟨1469486034266527929307658561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979657356177685286205105707 1469486034266527929307658561)
          ·
            refine ⟨1102114525699895946980743921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1469486034266527929307658561 1102114525699895946980743921)
            ·
              refine ⟨826585894274921960235557941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102114525699895946980743921 826585894274921960235557941)
              ·
                refine ⟨77492427588273933772083557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 826585894274921960235557941 77492427588273933772083557)
                ·
                  refine ⟨14529830172801362582265667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77492427588273933772083557 14529830172801362582265667)
                  ·
                    refine ⟨21794745259202043873398501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14529830172801362582265667 21794745259202043873398501)
                    ·
                      refine ⟨4086514736100383226262219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21794745259202043873398501 4086514736100383226262219)
                      ·
                        rfl

theorem cell23_7958459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 4].length) (baseStart_7958459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958459 prefixEnd_7958459 := by exact prefixLift 7958459
  have htrace : WordTrace (prefixWord ++ tailWord_7958459) baseStart_7958459 baseEnd_7958459 := by
    simpa [prefixWord, tailWord_7958459, baseEnd_7958459] using wordTrace_append hprefix tailTrace_7958459
  have hstable : (prefixWord ++ tailWord_7958459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958459).length < 2 ^ (prefixWord ++ tailWord_7958459).sum := by decide
  have hdescent : baseEnd_7958459 < baseStart_7958459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958460 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 7]
def baseStart_7958460 : Nat := 118140960795 + 7958460 * 2 ^ 59
def prefixEnd_7958460 : Nat := 4983230072969 + 3 ^ 40 * 7958460 * 2
def baseEnd_7958460 : Nat := 454057249953448635816635

theorem tailTrace_7958460 : CollatzResearch.WordTrace tailWord_7958460 prefixEnd_7958460 454057249953448635816635 := by
  unfold tailWord_7958460
  simp only [CollatzResearch.WordTrace]
  refine ⟨145134441373933045800964417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193512588498577394401285889 145134441373933045800964417)
  ·
    refine ⟨108850831030449784350723313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145134441373933045800964417 108850831030449784350723313)
    ·
      refine ⟨81638123272837338263042485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108850831030449784350723313 81638123272837338263042485)
      ·
        refine ⟨7653574056828500462160233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81638123272837338263042485 7653574056828500462160233)
        ·
          refine ⟨5740180542621375346620175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7653574056828500462160233 5740180542621375346620175)
          ·
            refine ⟨8610270813932063019930263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740180542621375346620175 8610270813932063019930263)
            ·
              refine ⟨12915406220898094529895395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610270813932063019930263 12915406220898094529895395)
              ·
                refine ⟨19373109331347141794843093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915406220898094529895395 19373109331347141794843093)
                ·
                  refine ⟨454057249953448635816635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19373109331347141794843093 454057249953448635816635)
                  ·
                    rfl

theorem cell23_7958460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_7958460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958460 prefixEnd_7958460 := by exact prefixLift 7958460
  have htrace : WordTrace (prefixWord ++ tailWord_7958460) baseStart_7958460 baseEnd_7958460 := by
    simpa [prefixWord, tailWord_7958460, baseEnd_7958460] using wordTrace_append hprefix tailTrace_7958460
  have hstable : (prefixWord ++ tailWord_7958460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958460).length < 2 ^ (prefixWord ++ tailWord_7958460).sum := by decide
  have hdescent : baseEnd_7958460 < baseStart_7958460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958520 : List Nat := [2, 1, 2, 1, 1, 3, 6, 2, 1, 4]
def baseStart_7958520 : Nat := 118140960795 + 7958520 * 2 ^ 59
def prefixEnd_7958520 : Nat := 4983230072969 + 3 ^ 40 * 7958520 * 2
def baseEnd_7958520 : Nat := 1362182019473435829199813

theorem tailTrace_7958520 : CollatzResearch.WordTrace tailWord_7958520 prefixEnd_7958520 1362182019473435829199813 := by
  unfold tailWord_7958520
  simp only [CollatzResearch.WordTrace]
  refine ⟨145135535563824360924556507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193514047418432481232742009 145135535563824360924556507)
  ·
    refine ⟨217703303345736541386834761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145135535563824360924556507 217703303345736541386834761)
    ·
      refine ⟨163277477509302406040126071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217703303345736541386834761 163277477509302406040126071)
      ·
        refine ⟨244916216263953609060189107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163277477509302406040126071 244916216263953609060189107)
        ·
          refine ⟨367374324395930413590283661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244916216263953609060189107 367374324395930413590283661)
          ·
            refine ⟨137765371648473905096356373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367374324395930413590283661 137765371648473905096356373)
            ·
              refine ⟨6457751796022214301391705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137765371648473905096356373 6457751796022214301391705)
              ·
                refine ⟨4843313847016660726043779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6457751796022214301391705 4843313847016660726043779)
                ·
                  refine ⟨7264970770524991089065669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4843313847016660726043779 7264970770524991089065669)
                  ·
                    refine ⟨1362182019473435829199813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7264970770524991089065669 1362182019473435829199813)
                    ·
                      rfl

theorem cell23_7958520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_7958520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958520 prefixEnd_7958520 := by exact prefixLift 7958520
  have htrace : WordTrace (prefixWord ++ tailWord_7958520) baseStart_7958520 baseEnd_7958520 := by
    simpa [prefixWord, tailWord_7958520, baseEnd_7958520] using wordTrace_append hprefix tailTrace_7958520
  have hstable : (prefixWord ++ tailWord_7958520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958520).length < 2 ^ (prefixWord ++ tailWord_7958520).sum := by decide
  have hdescent : baseEnd_7958520 < baseStart_7958520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958539 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 7]
def baseStart_7958539 : Nat := 118140960795 + 7958539 * 2 ^ 59
def prefixEnd_7958539 : Nat := 4983230072969 + 3 ^ 40 * 7958539 * 2
def baseEnd_7958539 : Nat := 4086555814552742913261851

theorem tailTrace_7958539 : CollatzResearch.WordTrace tailWord_7958539 prefixEnd_7958539 4086555814552742913261851 := by
  unfold tailWord_7958539
  simp only [CollatzResearch.WordTrace]
  refine ⟨290271764114579888094054671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193514509409719925396036447 290271764114579888094054671)
  ·
    refine ⟨435407646171869832141082007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290271764114579888094054671 435407646171869832141082007)
    ·
      refine ⟨653111469257804748211623011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435407646171869832141082007 653111469257804748211623011)
      ·
        refine ⟨979667203886707122317434517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653111469257804748211623011 979667203886707122317434517)
        ·
          refine ⟨45921900182189396358629743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 979667203886707122317434517 45921900182189396358629743)
          ·
            refine ⟨68882850273284094537944615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45921900182189396358629743 68882850273284094537944615)
            ·
              refine ⟨103324275409926141806916923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68882850273284094537944615 103324275409926141806916923)
              ·
                refine ⟨154986413114889212710375385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103324275409926141806916923 154986413114889212710375385)
                ·
                  refine ⟨116239809836166909532781539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154986413114889212710375385 116239809836166909532781539)
                  ·
                    refine ⟨174359714754250364299172309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116239809836166909532781539 174359714754250364299172309)
                    ·
                      refine ⟨4086555814552742913261851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174359714754250364299172309 4086555814552742913261851)
                      ·
                        rfl

theorem cell23_7958539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_7958539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958539 prefixEnd_7958539 := by exact prefixLift 7958539
  have htrace : WordTrace (prefixWord ++ tailWord_7958539) baseStart_7958539 baseEnd_7958539 := by
    simpa [prefixWord, tailWord_7958539, baseEnd_7958539] using wordTrace_append hprefix tailTrace_7958539
  have hstable : (prefixWord ++ tailWord_7958539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958539).length < 2 ^ (prefixWord ++ tailWord_7958539).sum := by decide
  have hdescent : baseEnd_7958539 < baseStart_7958539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958567 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 6]
def baseStart_7958567 : Nat := 118140960795 + 7958567 * 2 ^ 59
def prefixEnd_7958567 : Nat := 4983230072969 + 3 ^ 40 * 7958567 * 2
def baseEnd_7958567 : Nat := 454063354667896533745747

theorem tailTrace_7958567 : CollatzResearch.WordTrace tailWord_7958567 prefixEnd_7958567 454063354667896533745747 := by
  unfold tailWord_7958567
  simp only [CollatzResearch.WordTrace]
  refine ⟨290272785358478448876073955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193515190238985632584049303 290272785358478448876073955)
  ·
    refine ⟨435409178037717673314110933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290272785358478448876073955 435409178037717673314110933)
    ·
      refine ⟨10204902610259007968299475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 435409178037717673314110933 10204902610259007968299475)
      ·
        refine ⟨15307353915388511952449213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10204902610259007968299475 15307353915388511952449213)
        ·
          refine ⟨5740257718270691982168455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15307353915388511952449213 5740257718270691982168455)
          ·
            refine ⟨8610386577406037973252683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740257718270691982168455 8610386577406037973252683)
            ·
              refine ⟨12915579866109056959879025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610386577406037973252683 12915579866109056959879025)
              ·
                refine ⟨9686684899581792719909269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12915579866109056959879025 9686684899581792719909269)
                ·
                  refine ⟨454063354667896533745747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9686684899581792719909269 454063354667896533745747)
                  ·
                    rfl

theorem cell23_7958567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 6].length) (baseStart_7958567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958567 prefixEnd_7958567 := by exact prefixLift 7958567
  have htrace : WordTrace (prefixWord ++ tailWord_7958567) baseStart_7958567 baseEnd_7958567 := by
    simpa [prefixWord, tailWord_7958567, baseEnd_7958567] using wordTrace_append hprefix tailTrace_7958567
  have hstable : (prefixWord ++ tailWord_7958567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958567).length < 2 ^ (prefixWord ++ tailWord_7958567).sum := by decide
  have hdescent : baseEnd_7958567 < baseStart_7958567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958593 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 1, 6]
def baseStart_7958593 : Nat := 118140960795 + 7958593 * 2 ^ 59
def prefixEnd_7958593 : Nat := 4983230072969 + 3 ^ 40 * 7958593 * 2
def baseEnd_7958593 : Nat := 1362194514169361900662201

theorem tailTrace_7958593 : CollatzResearch.WordTrace tailWord_7958593 prefixEnd_7958593 1362194514169361900662201 := by
  unfold tailWord_7958593
  simp only [CollatzResearch.WordTrace]
  refine ⟨290273733656384255316520433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193515822437589503544346955 290273733656384255316520433)
  ·
    refine ⟨217705300242288191487390325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290273733656384255316520433 217705300242288191487390325)
    ·
      refine ⟨20409871897714517951942843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217705300242288191487390325 20409871897714517951942843)
      ·
        refine ⟨30614807846571776927914265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20409871897714517951942843 30614807846571776927914265)
        ·
          refine ⟨22961105884928832695935699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30614807846571776927914265 22961105884928832695935699)
          ·
            refine ⟨34441658827393249043903549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22961105884928832695935699 34441658827393249043903549)
            ·
              refine ⟨12915622060272468391463831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34441658827393249043903549 12915622060272468391463831)
              ·
                refine ⟨19373433090408702587195747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915622060272468391463831 19373433090408702587195747)
                ·
                  refine ⟨29060149635613053880793621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19373433090408702587195747 29060149635613053880793621)
                  ·
                    refine ⟨1362194514169361900662201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29060149635613053880793621 1362194514169361900662201)
                    ·
                      rfl

theorem cell23_7958593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_7958593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958593 prefixEnd_7958593 := by exact prefixLift 7958593
  have htrace : WordTrace (prefixWord ++ tailWord_7958593) baseStart_7958593 baseEnd_7958593 := by
    simpa [prefixWord, tailWord_7958593, baseEnd_7958593] using wordTrace_append hprefix tailTrace_7958593
  have hstable : (prefixWord ++ tailWord_7958593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958593).length < 2 ^ (prefixWord ++ tailWord_7958593).sum := by decide
  have hdescent : baseEnd_7958593 < baseStart_7958593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958606 : List Nat := [4, 1, 1, 1, 1, 5, 1, 9]
def baseStart_7958606 : Nat := 118140960795 + 7958606 * 2 ^ 59
def prefixEnd_7958606 : Nat := 4983230072969 + 3 ^ 40 * 7958606 * 2
def baseEnd_7958606 : Nat := 151355193250244227819409

theorem tailTrace_7958606 : CollatzResearch.WordTrace tailWord_7958606 prefixEnd_7958606 151355193250244227819409 := by
  unfold tailWord_7958606
  simp only [CollatzResearch.WordTrace]
  refine ⟨36284275975667144817092959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193516138536891439024495781 36284275975667144817092959)
  ·
    refine ⟨54426413963500717225639439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36284275975667144817092959 54426413963500717225639439)
    ·
      refine ⟨81639620945251075838459159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54426413963500717225639439 81639620945251075838459159)
      ·
        refine ⟨122459431417876613757688739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81639620945251075838459159 122459431417876613757688739)
        ·
          refine ⟨183689147126814920636533109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122459431417876613757688739 183689147126814920636533109)
          ·
            refine ⟨17220857543138898809674979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183689147126814920636533109 17220857543138898809674979)
            ·
              refine ⟨25831286314708348214512469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17220857543138898809674979 25831286314708348214512469)
              ·
                refine ⟨151355193250244227819409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25831286314708348214512469 151355193250244227819409)
                ·
                  rfl

theorem cell23_7958606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_7958606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958606 prefixEnd_7958606 := by exact prefixLift 7958606
  have htrace : WordTrace (prefixWord ++ tailWord_7958606) baseStart_7958606 baseEnd_7958606 := by
    simpa [prefixWord, tailWord_7958606, baseEnd_7958606] using wordTrace_append hprefix tailTrace_7958606
  have hstable : (prefixWord ++ tailWord_7958606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958606).length < 2 ^ (prefixWord ++ tailWord_7958606).sum := by decide
  have hdescent : baseEnd_7958606 < baseStart_7958606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958620 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_7958620 : Nat := 118140960795 + 7958620 * 2 ^ 59
def prefixEnd_7958620 : Nat := 4983230072969 + 3 ^ 40 * 7958620 * 2
def baseEnd_7958620 : Nat := 4086597406485757096348979

theorem tailTrace_7958620 : CollatzResearch.WordTrace tailWord_7958620 prefixEnd_7958620 4086597406485757096348979 := by
  unfold tailWord_7958620
  simp only [CollatzResearch.WordTrace]
  refine ⟨145137359213643219463876657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193516478951524292618502209 145137359213643219463876657)
  ·
    refine ⟨108853019410232414597907493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145137359213643219463876657 108853019410232414597907493)
    ·
      refine ⟨20409941139418577737107655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108853019410232414597907493 20409941139418577737107655)
      ·
        refine ⟨30614911709127866605661483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20409941139418577737107655 30614911709127866605661483)
        ·
          refine ⟨45922367563691799908492225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30614911709127866605661483 45922367563691799908492225)
          ·
            refine ⟨34441775672768849931369169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45922367563691799908492225 34441775672768849931369169)
            ·
              refine ⟨25831331754576637448526877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34441775672768849931369169 25831331754576637448526877)
              ·
                refine ⟨9686749407966239043197579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25831331754576637448526877 9686749407966239043197579)
                ·
                  refine ⟨14530124111949358564796369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9686749407966239043197579 14530124111949358564796369)
                  ·
                    refine ⟨10897593083962018923597277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14530124111949358564796369 10897593083962018923597277)
                    ·
                      refine ⟨4086597406485757096348979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10897593083962018923597277 4086597406485757096348979)
                      ·
                        rfl

theorem cell23_7958620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_7958620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958620 prefixEnd_7958620 := by exact prefixLift 7958620
  have htrace : WordTrace (prefixWord ++ tailWord_7958620) baseStart_7958620 baseEnd_7958620 := by
    simpa [prefixWord, tailWord_7958620, baseEnd_7958620] using wordTrace_append hprefix tailTrace_7958620
  have hstable : (prefixWord ++ tailWord_7958620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958620).length < 2 ^ (prefixWord ++ tailWord_7958620).sum := by decide
  have hdescent : baseEnd_7958620 < baseStart_7958620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958633 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 4, 1, 3]
def baseStart_7958633 : Nat := 118140960795 + 7958633 * 2 ^ 59
def prefixEnd_7958633 : Nat := 4983230072969 + 3 ^ 40 * 7958633 * 2
def baseEnd_7958633 : Nat := 4086604081734265545486419

theorem tailTrace_7958633 : CollatzResearch.WordTrace tailWord_7958633 prefixEnd_7958633 4086604081734265545486419 := by
  unfold tailWord_7958633
  simp only [CollatzResearch.WordTrace]
  refine ⟨290275192576239342147976553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193516795050826228098651035 290275192576239342147976553)
  ·
    refine ⟨217706394432179506610982415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290275192576239342147976553 217706394432179506610982415)
    ·
      refine ⟨326559591648269259916473623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217706394432179506610982415 326559591648269259916473623)
      ·
        refine ⟨489839387472403889874710435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326559591648269259916473623 489839387472403889874710435)
        ·
          refine ⟨734759081208605834812065653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489839387472403889874710435 734759081208605834812065653)
          ·
            refine ⟨68883663863306797013631155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 734759081208605834812065653 68883663863306797013631155)
            ·
              refine ⟨103325495794960195520446733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68883663863306797013631155 103325495794960195520446733)
              ·
                refine ⟨38747060923110073320167525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103325495794960195520446733 38747060923110073320167525)
                ·
                  refine ⟨7265073923083138747531411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38747060923110073320167525 7265073923083138747531411)
                  ·
                    refine ⟨10897610884624708121297117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7265073923083138747531411 10897610884624708121297117)
                    ·
                      refine ⟨4086604081734265545486419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10897610884624708121297117 4086604081734265545486419)
                      ·
                        rfl

theorem cell23_7958633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 1, 3].length) (baseStart_7958633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958633 prefixEnd_7958633 := by exact prefixLift 7958633
  have htrace : WordTrace (prefixWord ++ tailWord_7958633) baseStart_7958633 baseEnd_7958633 := by
    simpa [prefixWord, tailWord_7958633, baseEnd_7958633] using wordTrace_append hprefix tailTrace_7958633
  have hstable : (prefixWord ++ tailWord_7958633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958633).length < 2 ^ (prefixWord ++ tailWord_7958633).sum := by decide
  have hdescent : baseEnd_7958633 < baseStart_7958633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958634 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_7958634 : Nat := 118140960795 + 7958634 * 2 ^ 59
def prefixEnd_7958634 : Nat := 4983230072969 + 3 ^ 40 * 7958634 * 2
def baseEnd_7958634 : Nat := 4086604595214920041573915

theorem tailTrace_7958634 : CollatzResearch.WordTrace tailWord_7958634 prefixEnd_7958634 4086604595214920041573915 := by
  unfold tailWord_7958634
  simp only [CollatzResearch.WordTrace]
  refine ⟨72568807262308929829690739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193516819366157146212508637 72568807262308929829690739)
  ·
    refine ⟨108853210893463394744536109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72568807262308929829690739 108853210893463394744536109)
    ·
      refine ⟨40819954085048773029201041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108853210893463394744536109 40819954085048773029201041)
      ·
        refine ⟨30614965563786579771900781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40819954085048773029201041 30614965563786579771900781)
        ·
          refine ⟨11480612086419967414462793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30614965563786579771900781 11480612086419967414462793)
          ·
            refine ⟨8610459064814975560847095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11480612086419967414462793 8610459064814975560847095)
            ·
              refine ⟨12915688597222463341270643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610459064814975560847095 12915688597222463341270643)
              ·
                refine ⟨19373532895833695011905965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915688597222463341270643 19373532895833695011905965)
                ·
                  refine ⟨7265074835937635629464737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19373532895833695011905965 7265074835937635629464737)
                  ·
                    refine ⟨5448806126953226722098553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7265074835937635629464737 5448806126953226722098553)
                    ·
                      refine ⟨4086604595214920041573915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448806126953226722098553 4086604595214920041573915)
                      ·
                        rfl

theorem cell23_7958634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_7958634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958634 prefixEnd_7958634 := by exact prefixLift 7958634
  have htrace : WordTrace (prefixWord ++ tailWord_7958634) baseStart_7958634 baseEnd_7958634 := by
    simpa [prefixWord, tailWord_7958634, baseEnd_7958634] using wordTrace_append hprefix tailTrace_7958634
  have hstable : (prefixWord ++ tailWord_7958634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958634).length < 2 ^ (prefixWord ++ tailWord_7958634).sum := by decide
  have hdescent : baseEnd_7958634 < baseStart_7958634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958660 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_7958660 : Nat := 118140960795 + 7958660 * 2 ^ 59
def prefixEnd_7958660 : Nat := 4983230072969 + 3 ^ 40 * 7958660 * 2
def baseEnd_7958660 : Nat := 4086617945711936939848795

theorem tailTrace_7958660 : CollatzResearch.WordTrace tailWord_7958660 prefixEnd_7958660 4086617945711936939848795 := by
  unfold tailWord_7958660
  simp only [CollatzResearch.WordTrace]
  refine ⟨145138088673570762879604717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193517451564761017172806289 145138088673570762879604717)
  ·
    refine ⟨54426783252589036079851769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145138088673570762879604717 54426783252589036079851769)
    ·
      refine ⟨40820087439441777059888827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54426783252589036079851769 40820087439441777059888827)
      ·
        refine ⟨61230131159162665589833241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40820087439441777059888827 61230131159162665589833241)
        ·
          refine ⟨45922598369371999192374931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61230131159162665589833241 45922598369371999192374931)
          ·
            refine ⟨68883897554057998788562397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45922598369371999192374931 68883897554057998788562397)
            ·
              refine ⟨25831461582771749545710899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68883897554057998788562397 25831461582771749545710899)
              ·
                refine ⟨38747192374157624318566349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25831461582771749545710899 38747192374157624318566349)
                ·
                  refine ⟨14530197140309109119462381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38747192374157624318566349 14530197140309109119462381)
                  ·
                    refine ⟨5448823927615915919798393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14530197140309109119462381 5448823927615915919798393)
                    ·
                      refine ⟨4086617945711936939848795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448823927615915919798393 4086617945711936939848795)
                      ·
                        rfl

theorem cell23_7958660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_7958660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958660 prefixEnd_7958660 := by exact prefixLift 7958660
  have htrace : WordTrace (prefixWord ++ tailWord_7958660) baseStart_7958660 baseEnd_7958660 := by
    simpa [prefixWord, tailWord_7958660, baseEnd_7958660] using wordTrace_append hprefix tailTrace_7958660
  have hstable : (prefixWord ++ tailWord_7958660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958660).length < 2 ^ (prefixWord ++ tailWord_7958660).sum := by decide
  have hdescent : baseEnd_7958660 < baseStart_7958660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958677 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 1, 3, 2]
def baseStart_7958677 : Nat := 118140960795 + 7958677 * 2 ^ 59
def prefixEnd_7958677 : Nat := 4983230072969 + 3 ^ 40 * 7958677 * 2
def baseEnd_7958677 : Nat := 4086626674883063373336217

theorem tailTrace_7958677 : CollatzResearch.WordTrace tailWord_7958677 prefixEnd_7958677 4086626674883063373336217 := by
  unfold tailWord_7958677
  simp only [CollatzResearch.WordTrace]
  refine ⟨290276797388079937662578285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193517864925386625108385523 290276797388079937662578285)
  ·
    refine ⟨108853799020529976623466857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290276797388079937662578285 108853799020529976623466857)
    ·
      refine ⟨81640349265397482467600143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108853799020529976623466857 81640349265397482467600143)
      ·
        refine ⟨122460523898096223701400215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81640349265397482467600143 122460523898096223701400215)
        ·
          refine ⟨183690785847144335552100323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122460523898096223701400215 183690785847144335552100323)
          ·
            refine ⟨275536178770716503328150485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183690785847144335552100323 275536178770716503328150485)
            ·
              refine ⟨6457879189938668046753527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 275536178770716503328150485 6457879189938668046753527)
              ·
                refine ⟨9686818784908002070130291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457879189938668046753527 9686818784908002070130291)
                ·
                  refine ⟨14530228177362003105195437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9686818784908002070130291 14530228177362003105195437)
                  ·
                    refine ⟨5448835566510751164448289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14530228177362003105195437 5448835566510751164448289)
                    ·
                      refine ⟨4086626674883063373336217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448835566510751164448289 4086626674883063373336217)
                      ·
                        rfl

theorem cell23_7958677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_7958677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958677 prefixEnd_7958677 := by exact prefixLift 7958677
  have htrace : WordTrace (prefixWord ++ tailWord_7958677) baseStart_7958677 baseEnd_7958677 := by
    simpa [prefixWord, tailWord_7958677, baseEnd_7958677] using wordTrace_append hprefix tailTrace_7958677
  have hstable : (prefixWord ++ tailWord_7958677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958677).length < 2 ^ (prefixWord ++ tailWord_7958677).sum := by decide
  have hdescent : baseEnd_7958677 < baseStart_7958677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958678 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7958678 : Nat := 118140960795 + 7958678 * 2 ^ 59
def prefixEnd_7958678 : Nat := 4983230072969 + 3 ^ 40 * 7958678 * 2
def baseEnd_7958678 : Nat := 1362209062787905956474571

theorem tailTrace_7958678 : CollatzResearch.WordTrace tailWord_7958678 prefixEnd_7958678 1362209062787905956474571 := by
  unfold tailWord_7958678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18142302116317269677085293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193517889240717543222243125 18142302116317269677085293)
  ·
    refine ⟨6803363293618976128906985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18142302116317269677085293 6803363293618976128906985)
    ·
      refine ⟨5102522470214232096680239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6803363293618976128906985 5102522470214232096680239)
      ·
        refine ⟨7653783705321348145020359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5102522470214232096680239 7653783705321348145020359)
        ·
          refine ⟨11480675557982022217530539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7653783705321348145020359 11480675557982022217530539)
          ·
            refine ⟨17221013336973033326295809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11480675557982022217530539 17221013336973033326295809)
            ·
              refine ⟨12915760002729774994721857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17221013336973033326295809 12915760002729774994721857)
              ·
                refine ⟨9686820002047331246041393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12915760002729774994721857 9686820002047331246041393)
                ·
                  refine ⟨7265115001535498434531045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9686820002047331246041393 7265115001535498434531045)
                  ·
                    refine ⟨1362209062787905956474571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7265115001535498434531045 1362209062787905956474571)
                    ·
                      rfl

theorem cell23_7958678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7958678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958678 prefixEnd_7958678 := by exact prefixLift 7958678
  have htrace : WordTrace (prefixWord ++ tailWord_7958678) baseStart_7958678 baseEnd_7958678 := by
    simpa [prefixWord, tailWord_7958678, baseEnd_7958678] using wordTrace_append hprefix tailTrace_7958678
  have hstable : (prefixWord ++ tailWord_7958678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958678).length < 2 ^ (prefixWord ++ tailWord_7958678).sum := by decide
  have hdescent : baseEnd_7958678 < baseStart_7958678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958730 : List Nat := [3, 1, 2, 1, 3, 1, 4, 3, 5]
def baseStart_7958730 : Nat := 118140960795 + 7958730 * 2 ^ 59
def prefixEnd_7958730 : Nat := 4983230072969 + 3 ^ 40 * 7958730 * 2
def baseEnd_7958730 : Nat := 454072654373083518441497

theorem tailTrace_7958730 : CollatzResearch.WordTrace tailWord_7958730 prefixEnd_7958730 454072654373083518441497 := by
  unfold tailWord_7958730
  simp only [CollatzResearch.WordTrace]
  refine ⟨72569682614221981928564411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193519153637925285142838429 72569682614221981928564411)
  ·
    refine ⟨108854523921332972892846617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72569682614221981928564411 108854523921332972892846617)
    ·
      refine ⟨81640892940999729669634963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108854523921332972892846617 81640892940999729669634963)
      ·
        refine ⟨122461339411499594504452445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81640892940999729669634963 122461339411499594504452445)
        ·
          refine ⟨45923002279312347939169667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122461339411499594504452445 45923002279312347939169667)
          ·
            refine ⟨68884503418968521908754501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45923002279312347939169667 68884503418968521908754501)
            ·
              refine ⟨12915844391056597857891469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68884503418968521908754501 12915844391056597857891469)
              ·
                refine ⟨4843441646646224196709301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12915844391056597857891469 4843441646646224196709301)
                ·
                  refine ⟨454072654373083518441497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4843441646646224196709301 454072654373083518441497)
                  ·
                    rfl

theorem cell23_7958730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_7958730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958730 prefixEnd_7958730 := by exact prefixLift 7958730
  have htrace : WordTrace (prefixWord ++ tailWord_7958730) baseStart_7958730 baseEnd_7958730 := by
    simpa [prefixWord, tailWord_7958730, baseEnd_7958730] using wordTrace_append hprefix tailTrace_7958730
  have hstable : (prefixWord ++ tailWord_7958730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958730).length < 2 ^ (prefixWord ++ tailWord_7958730).sum := by decide
  have hdescent : baseEnd_7958730 < baseStart_7958730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958741 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7958741 : Nat := 118140960795 + 7958741 * 2 ^ 59
def prefixEnd_7958741 : Nat := 4983230072969 + 3 ^ 40 * 7958741 * 2
def baseEnd_7958741 : Nat := 4086659537644951122935923

theorem tailTrace_7958741 : CollatzResearch.WordTrace tailWord_7958741 prefixEnd_7958741 4086659537644951122935923 := by
  unfold tailWord_7958741
  simp only [CollatzResearch.WordTrace]
  refine ⟨290279131659848076592908077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193519421106565384395272051 290279131659848076592908077)
  ·
    refine ⟨108854674372443028722340529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290279131659848076592908077 108854674372443028722340529)
    ·
      refine ⟨81641005779332271541755397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108854674372443028722340529 81641005779332271541755397)
      ·
        refine ⟨15307688583624800914079137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81641005779332271541755397 15307688583624800914079137)
        ·
          refine ⟨11480766437718600685559353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15307688583624800914079137 11480766437718600685559353)
          ·
            refine ⟨8610574828288950514169515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11480766437718600685559353 8610574828288950514169515)
            ·
              refine ⟨12915862242433425771254273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610574828288950514169515 12915862242433425771254273)
              ·
                refine ⟨9686896681825069328440705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12915862242433425771254273 9686896681825069328440705)
                ·
                  refine ⟨7265172511368801996330529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9686896681825069328440705 7265172511368801996330529)
                  ·
                    refine ⟨5448879383526601497247897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7265172511368801996330529 5448879383526601497247897)
                    ·
                      refine ⟨4086659537644951122935923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448879383526601497247897 4086659537644951122935923)
                      ·
                        rfl

theorem cell23_7958741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7958741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958741 prefixEnd_7958741 := by exact prefixLift 7958741
  have htrace : WordTrace (prefixWord ++ tailWord_7958741) baseStart_7958741 baseEnd_7958741 := by
    simpa [prefixWord, tailWord_7958741, baseEnd_7958741] using wordTrace_append hprefix tailTrace_7958741
  have hstable : (prefixWord ++ tailWord_7958741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958741).length < 2 ^ (prefixWord ++ tailWord_7958741).sum := by decide
  have hdescent : baseEnd_7958741 < baseStart_7958741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958783 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 3]
def baseStart_7958783 : Nat := 118140960795 + 7958783 * 2 ^ 59
def prefixEnd_7958783 : Nat := 4983230072969 + 3 ^ 40 * 7958783 * 2
def baseEnd_7958783 : Nat := 4086681103832439958610729

theorem tailTrace_7958783 : CollatzResearch.WordTrace tailWord_7958783 prefixEnd_7958783 4086681103832439958610729 := by
  unfold tailWord_7958783
  simp only [CollatzResearch.WordTrace]
  refine ⟨290280663525695917765937003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193520442350463945177291335 290280663525695917765937003)
  ·
    refine ⟨435420995288543876648905505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290280663525695917765937003 435420995288543876648905505)
    ·
      refine ⟨326565746466407907486679129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435420995288543876648905505 326565746466407907486679129)
      ·
        refine ⟨244924309849805930615009347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326565746466407907486679129 244924309849805930615009347)
        ·
          refine ⟨367386464774708895922514021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244924309849805930615009347 367386464774708895922514021)
          ·
            refine ⟨68884962145257917985471379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367386464774708895922514021 68884962145257917985471379)
            ·
              refine ⟨103327443217886876978207069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68884962145257917985471379 103327443217886876978207069)
              ·
                refine ⟨38747791206707578866827651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103327443217886876978207069 38747791206707578866827651)
                ·
                  refine ⟨58121686810061368300241477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38747791206707578866827651 58121686810061368300241477)
                  ·
                    refine ⟨10897816276886506556295277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58121686810061368300241477 10897816276886506556295277)
                    ·
                      refine ⟨4086681103832439958610729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10897816276886506556295277 4086681103832439958610729)
                      ·
                        rfl

theorem cell23_7958783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_7958783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958783 prefixEnd_7958783 := by exact prefixLift 7958783
  have htrace : WordTrace (prefixWord ++ tailWord_7958783) baseStart_7958783 baseEnd_7958783 := by
    simpa [prefixWord, tailWord_7958783, baseEnd_7958783] using wordTrace_append hprefix tailTrace_7958783
  have hstable : (prefixWord ++ tailWord_7958783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958783).length < 2 ^ (prefixWord ++ tailWord_7958783).sum := by decide
  have hdescent : baseEnd_7958783 < baseStart_7958783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958807 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 3, 4]
def baseStart_7958807 : Nat := 118140960795 + 7958807 * 2 ^ 59
def prefixEnd_7958807 : Nat := 4983230072969 + 3 ^ 40 * 7958807 * 2
def baseEnd_7958807 : Nat := 1362231142456049288236873

theorem tailTrace_7958807 : CollatzResearch.WordTrace tailWord_7958807 prefixEnd_7958807 1362231142456049288236873 := by
  unfold tailWord_7958807
  simp only [CollatzResearch.WordTrace]
  refine ⟨290281538877608969864810675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193521025918405979909873783 290281538877608969864810675)
  ·
    refine ⟨435422308316413454797216013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290281538877608969864810675 435422308316413454797216013)
    ·
      refine ⟨163283365618655045548956005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435422308316413454797216013 163283365618655045548956005)
      ·
        refine ⟨30615631053497821040429251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163283365618655045548956005 30615631053497821040429251)
        ·
          refine ⟨45923446580246731560643877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30615631053497821040429251 45923446580246731560643877)
          ·
            refine ⟨8610646233796262167620727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45923446580246731560643877 8610646233796262167620727)
            ·
              refine ⟨12915969350694393251431091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610646233796262167620727 12915969350694393251431091)
              ·
                refine ⟨19373954026041589877146637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915969350694393251431091 19373954026041589877146637)
                ·
                  refine ⟨7265232759765596203929989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19373954026041589877146637 7265232759765596203929989)
                  ·
                    refine ⟨1362231142456049288236873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7265232759765596203929989 1362231142456049288236873)
                    ·
                      rfl

theorem cell23_7958807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_7958807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958807 prefixEnd_7958807 := by exact prefixLift 7958807
  have htrace : WordTrace (prefixWord ++ tailWord_7958807) baseStart_7958807 baseEnd_7958807 := by
    simpa [prefixWord, tailWord_7958807, baseEnd_7958807] using wordTrace_append hprefix tailTrace_7958807
  have hstable : (prefixWord ++ tailWord_7958807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958807).length < 2 ^ (prefixWord ++ tailWord_7958807).sum := by decide
  have hdescent : baseEnd_7958807 < baseStart_7958807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958820 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 6]
def baseStart_7958820 : Nat := 118140960795 + 7958820 * 2 ^ 59
def prefixEnd_7958820 : Nat := 4983230072969 + 3 ^ 40 * 7958820 * 2
def baseEnd_7958820 : Nat := 454077789179628479316451

theorem tailTrace_7958820 : CollatzResearch.WordTrace tailWord_7958820 prefixEnd_7958820 454077789179628479316451 := by
  unfold tailWord_7958820
  simp only [CollatzResearch.WordTrace]
  refine ⟨145141006513280936542516957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193521342017707915390022609 145141006513280936542516957)
  ·
    refine ⟨54427877442480351203443859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145141006513280936542516957 54427877442480351203443859)
    ·
      refine ⟨81641816163720526805165789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54427877442480351203443859 81641816163720526805165789)
      ·
        refine ⟨30615681061395197551937171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81641816163720526805165789 30615681061395197551937171)
        ·
          refine ⟨45923521592092796327905757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30615681061395197551937171 45923521592092796327905757)
          ·
            refine ⟨17221320597034798622964659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45923521592092796327905757 17221320597034798622964659)
            ·
              refine ⟨25831980895552197934446989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17221320597034798622964659 25831980895552197934446989)
              ·
                refine ⟨9686992835832074225417621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25831980895552197934446989 9686992835832074225417621)
                ·
                  refine ⟨454077789179628479316451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9686992835832074225417621 454077789179628479316451)
                  ·
                    rfl

theorem cell23_7958820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_7958820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958820 prefixEnd_7958820 := by exact prefixLift 7958820
  have htrace : WordTrace (prefixWord ++ tailWord_7958820) baseStart_7958820 baseEnd_7958820 := by
    simpa [prefixWord, tailWord_7958820, baseEnd_7958820] using wordTrace_append hprefix tailTrace_7958820
  have hstable : (prefixWord ++ tailWord_7958820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958820).length < 2 ^ (prefixWord ++ tailWord_7958820).sum := by decide
  have hdescent : baseEnd_7958820 < baseStart_7958820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958840 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 1, 5, 2]
def baseStart_7958840 : Nat := 118140960795 + 7958840 * 2 ^ 59
def prefixEnd_7958840 : Nat := 4983230072969 + 3 ^ 40 * 7958840 * 2
def baseEnd_7958840 : Nat := 4086710372229746235597967

theorem tailTrace_7958840 : CollatzResearch.WordTrace tailWord_7958840 prefixEnd_7958840 4086710372229746235597967 := by
  unfold tailWord_7958840
  simp only [CollatzResearch.WordTrace]
  refine ⟨145141371243244708250380987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193521828324326277667174649 145141371243244708250380987)
  ·
    refine ⟨217712056864867062375571481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145141371243244708250380987 217712056864867062375571481)
    ·
      refine ⟨163284042648650296781678611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217712056864867062375571481 163284042648650296781678611)
      ·
        refine ⟨244926063972975445172517917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163284042648650296781678611 244926063972975445172517917)
        ·
          refine ⟨91847273989865791939694219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244926063972975445172517917 91847273989865791939694219)
          ·
            refine ⟨137770910984798687909541329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91847273989865791939694219 137770910984798687909541329)
            ·
              refine ⟨103328183238599015932155997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137770910984798687909541329 103328183238599015932155997)
              ·
                refine ⟨38748068714474630974558499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103328183238599015932155997 38748068714474630974558499)
                ·
                  refine ⟨58122103071711946461837749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38748068714474630974558499 58122103071711946461837749)
                  ·
                    refine ⟨5448947162972994980797289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58122103071711946461837749 5448947162972994980797289)
                    ·
                      refine ⟨4086710372229746235597967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5448947162972994980797289 4086710372229746235597967)
                      ·
                        rfl

theorem cell23_7958840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_7958840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958840 prefixEnd_7958840 := by exact prefixLift 7958840
  have htrace : WordTrace (prefixWord ++ tailWord_7958840) baseStart_7958840 baseEnd_7958840 := by
    simpa [prefixWord, tailWord_7958840, baseEnd_7958840] using wordTrace_append hprefix tailTrace_7958840
  have hstable : (prefixWord ++ tailWord_7958840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958840).length < 2 ^ (prefixWord ++ tailWord_7958840).sum := by decide
  have hdescent : baseEnd_7958840 < baseStart_7958840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958864 : List Nat := [2, 1, 1, 1, 1, 7, 1, 4, 1, 1, 3]
def baseStart_7958864 : Nat := 118140960795 + 7958864 * 2 ^ 59
def prefixEnd_7958864 : Nat := 4983230072969 + 3 ^ 40 * 7958864 * 2
def baseEnd_7958864 : Nat := 4086722695765454141697857

theorem tailTrace_7958864 : CollatzResearch.WordTrace tailWord_7958864 prefixEnd_7958864 4086722695765454141697857 := by
  unfold tailWord_7958864
  simp only [CollatzResearch.WordTrace]
  refine ⟨145141808919201234299817823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193522411892268312399757097 145141808919201234299817823)
  ·
    refine ⟨217712713378801851449726735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145141808919201234299817823 217712713378801851449726735)
    ·
      refine ⟨326569070068202777174590103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217712713378801851449726735 326569070068202777174590103)
      ·
        refine ⟨489853605102304165761885155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326569070068202777174590103 489853605102304165761885155)
        ·
          refine ⟨734780407653456248642827733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489853605102304165761885155 734780407653456248642827733)
          ·
            refine ⟨17221415804377880827566275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 734780407653456248642827733 17221415804377880827566275)
            ·
              refine ⟨25832123706566821241349413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17221415804377880827566275 25832123706566821241349413)
              ·
                refine ⟨4843523194981278982753015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25832123706566821241349413 4843523194981278982753015)
                ·
                  refine ⟨7265284792471918474129523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4843523194981278982753015 7265284792471918474129523)
                  ·
                    refine ⟨10897927188707877711194285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7265284792471918474129523 10897927188707877711194285)
                    ·
                      refine ⟨4086722695765454141697857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10897927188707877711194285 4086722695765454141697857)
                      ·
                        rfl

theorem cell23_7958864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 1, 1, 3].length) (baseStart_7958864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958864 prefixEnd_7958864 := by exact prefixLift 7958864
  have htrace : WordTrace (prefixWord ++ tailWord_7958864) baseStart_7958864 baseEnd_7958864 := by
    simpa [prefixWord, tailWord_7958864, baseEnd_7958864] using wordTrace_append hprefix tailTrace_7958864
  have hstable : (prefixWord ++ tailWord_7958864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958864).length < 2 ^ (prefixWord ++ tailWord_7958864).sum := by decide
  have hdescent : baseEnd_7958864 < baseStart_7958864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958873 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_7958873 : Nat := 118140960795 + 7958873 * 2 ^ 59
def prefixEnd_7958873 : Nat := 4983230072969 + 3 ^ 40 * 7958873 * 2
def baseEnd_7958873 : Nat := 4086727317091344606485315

theorem tailTrace_7958873 : CollatzResearch.WordTrace tailWord_7958873 prefixEnd_7958873 4086727317091344606485315 := by
  unfold tailWord_7958873
  simp only [CollatzResearch.WordTrace]
  refine ⟨290283946095369863136713273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193522630730246575424475515 290283946095369863136713273)
  ·
    refine ⟨217712959571527397352534955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290283946095369863136713273 217712959571527397352534955)
    ·
      refine ⟨326569439357291096028802433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217712959571527397352534955 326569439357291096028802433)
      ·
        refine ⟨244927079517968322021601825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326569439357291096028802433 244927079517968322021601825)
        ·
          refine ⟨183695309638476241516201369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244927079517968322021601825 183695309638476241516201369)
          ·
            refine ⟨137771482228857181137151027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183695309638476241516201369 137771482228857181137151027)
            ·
              refine ⟨206657223343285771705726541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137771482228857181137151027 206657223343285771705726541)
              ·
                refine ⟨77496458753732164389647453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206657223343285771705726541 77496458753732164389647453)
                ·
                  refine ⟨29061172032649561646117795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77496458753732164389647453 29061172032649561646117795)
                  ·
                    refine ⟨43591758048974342469176693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29061172032649561646117795 43591758048974342469176693)
                    ·
                      refine ⟨4086727317091344606485315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43591758048974342469176693 4086727317091344606485315)
                      ·
                        rfl

theorem cell23_7958873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_7958873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958873 prefixEnd_7958873 := by exact prefixLift 7958873
  have htrace : WordTrace (prefixWord ++ tailWord_7958873) baseStart_7958873 baseEnd_7958873 := by
    simpa [prefixWord, tailWord_7958873, baseEnd_7958873] using wordTrace_append hprefix tailTrace_7958873
  have hstable : (prefixWord ++ tailWord_7958873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958873).length < 2 ^ (prefixWord ++ tailWord_7958873).sum := by decide
  have hdescent : baseEnd_7958873 < baseStart_7958873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958907 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 1, 2, 3]
def baseStart_7958907 : Nat := 118140960795 + 7958907 * 2 ^ 59
def prefixEnd_7958907 : Nat := 4983230072969 + 3 ^ 40 * 7958907 * 2
def baseEnd_7958907 : Nat := 4086744775433597473460159

theorem tailTrace_7958907 : CollatzResearch.WordTrace tailWord_7958907 prefixEnd_7958907 4086744775433597473460159 := by
  unfold tailWord_7958907
  simp only [CollatzResearch.WordTrace]
  refine ⟨290285186177246686943450975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193523457451497791295633983 290285186177246686943450975)
  ·
    refine ⟨435427779265870030415176463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290285186177246686943450975 435427779265870030415176463)
    ·
      refine ⟨653141668898805045622764695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435427779265870030415176463 653141668898805045622764695)
      ·
        refine ⟨979712503348207568434147043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653141668898805045622764695 979712503348207568434147043)
        ·
          refine ⟨1469568755022311352651220565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979712503348207568434147043 1469568755022311352651220565)
          ·
            refine ⟨17221508847917711163881491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1469568755022311352651220565 17221508847917711163881491)
            ·
              refine ⟨25832263271876566745822237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17221508847917711163881491 25832263271876566745822237)
              ·
                refine ⟨9687098726953712529683339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25832263271876566745822237 9687098726953712529683339)
                ·
                  refine ⟨14530648090430568794525009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687098726953712529683339 14530648090430568794525009)
                  ·
                    refine ⟨10897986067822926595893757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14530648090430568794525009 10897986067822926595893757)
                    ·
                      refine ⟨4086744775433597473460159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10897986067822926595893757 4086744775433597473460159)
                      ·
                        rfl

theorem cell23_7958907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 2, 3].length) (baseStart_7958907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958907 prefixEnd_7958907 := by exact prefixLift 7958907
  have htrace : WordTrace (prefixWord ++ tailWord_7958907) baseStart_7958907 baseEnd_7958907 := by
    simpa [prefixWord, tailWord_7958907, baseEnd_7958907] using wordTrace_append hprefix tailTrace_7958907
  have hstable : (prefixWord ++ tailWord_7958907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958907).length < 2 ^ (prefixWord ++ tailWord_7958907).sum := by decide
  have hdescent : baseEnd_7958907 < baseStart_7958907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958921 : List Nat := [1, 2, 1, 1, 6, 1, 2, 4, 1, 2, 2]
def baseStart_7958921 : Nat := 118140960795 + 7958921 * 2 ^ 59
def prefixEnd_7958921 : Nat := 4983230072969 + 3 ^ 40 * 7958921 * 2
def baseEnd_7958921 : Nat := 4086751964162760418685095

theorem tailTrace_7958921 : CollatzResearch.WordTrace tailWord_7958921 prefixEnd_7958921 4086751964162760418685095 := by
  unfold tailWord_7958921
  simp only [CollatzResearch.WordTrace]
  refine ⟨290285696799195967334460617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193523797866130644889640411 290285696799195967334460617)
  ·
    refine ⟨217714272599396975500845463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290285696799195967334460617 217714272599396975500845463)
    ·
      refine ⟨326571408899095463251268195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217714272599396975500845463 326571408899095463251268195)
      ·
        refine ⟨489857113348643194876902293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326571408899095463251268195 489857113348643194876902293)
        ·
          refine ⟨22962052188217649759854795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 489857113348643194876902293 22962052188217649759854795)
          ·
            refine ⟨34443078282326474639782193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22962052188217649759854795 34443078282326474639782193)
            ·
              refine ⟨25832308711744855979836645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34443078282326474639782193 25832308711744855979836645)
              ·
                refine ⟨4843557883452160496219371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25832308711744855979836645 4843557883452160496219371)
                ·
                  refine ⟨7265336825178240744329057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4843557883452160496219371 7265336825178240744329057)
                  ·
                    refine ⟨5449002618883680558246793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7265336825178240744329057 5449002618883680558246793)
                    ·
                      refine ⟨4086751964162760418685095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449002618883680558246793 4086751964162760418685095)
                      ·
                        rfl

theorem cell23_7958921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 1, 2, 2].length) (baseStart_7958921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958921 prefixEnd_7958921 := by exact prefixLift 7958921
  have htrace : WordTrace (prefixWord ++ tailWord_7958921) baseStart_7958921 baseEnd_7958921 := by
    simpa [prefixWord, tailWord_7958921, baseEnd_7958921] using wordTrace_append hprefix tailTrace_7958921
  have hstable : (prefixWord ++ tailWord_7958921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958921).length < 2 ^ (prefixWord ++ tailWord_7958921).sum := by decide
  have hdescent : baseEnd_7958921 < baseStart_7958921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958953 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 1, 8]
def baseStart_7958953 : Nat := 118140960795 + 7958953 * 2 ^ 59
def prefixEnd_7958953 : Nat := 4983230072969 + 3 ^ 40 * 7958953 * 2
def baseEnd_7958953 : Nat := 1362256131847901431161649

theorem tailTrace_7958953 : CollatzResearch.WordTrace tailWord_7958953 prefixEnd_7958953 1362256131847901431161649 := by
  unfold tailWord_7958953
  simp only [CollatzResearch.WordTrace]
  refine ⟨290286863935080036799625513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193524575956720024533083675 290286863935080036799625513)
  ·
    refine ⟨217715147951310027599719135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290286863935080036799625513 217715147951310027599719135)
    ·
      refine ⟨326572721926965041399578703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217715147951310027599719135 326572721926965041399578703)
      ·
        refine ⟨489859082890447562099368055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326572721926965041399578703 489859082890447562099368055)
        ·
          refine ⟨734788624335671343149052083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489859082890447562099368055 734788624335671343149052083)
          ·
            refine ⟨1102182936503507014723578125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734788624335671343149052083 1102182936503507014723578125)
            ·
              refine ⟨413318601188815130521341797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1102182936503507014723578125 413318601188815130521341797)
              ·
                refine ⟨77497237722902836972751587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413318601188815130521341797 77497237722902836972751587)
                ·
                  refine ⟨116245856584354255459127381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77497237722902836972751587 116245856584354255459127381)
                  ·
                    refine ⟨1362256131847901431161649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116245856584354255459127381 1362256131847901431161649)
                    ·
                      rfl

theorem cell23_7958953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_7958953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958953 prefixEnd_7958953 := by exact prefixLift 7958953
  have htrace : WordTrace (prefixWord ++ tailWord_7958953) baseStart_7958953 baseEnd_7958953 := by
    simpa [prefixWord, tailWord_7958953, baseEnd_7958953] using wordTrace_append hprefix tailTrace_7958953
  have hstable : (prefixWord ++ tailWord_7958953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958953).length < 2 ^ (prefixWord ++ tailWord_7958953).sum := by decide
  have hdescent : baseEnd_7958953 < baseStart_7958953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958988 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 2, 1, 3]
def baseStart_7958988 : Nat := 118140960795 + 7958988 * 2 ^ 59
def prefixEnd_7958988 : Nat := 4983230072969 + 3 ^ 40 * 7958988 * 2
def baseEnd_7958988 : Nat := 4086786367366611656547287

theorem tailTrace_7958988 : CollatzResearch.WordTrace tailWord_7958988 prefixEnd_7958988 4086786367366611656547287 := by
  unfold tailWord_7958988
  simp only [CollatzResearch.WordTrace]
  refine ⟨145144070244976618888574809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193525426993302158518099745 145144070244976618888574809)
  ·
    refine ⟨108858052683732464166431107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145144070244976618888574809 108858052683732464166431107)
    ·
      refine ⟨163287079025598696249646661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108858052683732464166431107 163287079025598696249646661)
      ·
        refine ⟨30616327317299755546808749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163287079025598696249646661 30616327317299755546808749)
        ·
          refine ⟨11481122743987408330053281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30616327317299755546808749 11481122743987408330053281)
          ·
            refine ⟨8610842057990556247539961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11481122743987408330053281 8610842057990556247539961)
            ·
              refine ⟨6458131543492917185654971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8610842057990556247539961 6458131543492917185654971)
              ·
                refine ⟨9687197315239375778482457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458131543492917185654971 9687197315239375778482457)
                ·
                  refine ⟨7265397986429531833861843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9687197315239375778482457 7265397986429531833861843)
                  ·
                    refine ⟨10898096979644297750792765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7265397986429531833861843 10898096979644297750792765)
                    ·
                      refine ⟨4086786367366611656547287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10898096979644297750792765 4086786367366611656547287)
                      ·
                        rfl

theorem cell23_7958988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_7958988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958988 prefixEnd_7958988 := by exact prefixLift 7958988
  have htrace : WordTrace (prefixWord ++ tailWord_7958988) baseStart_7958988 baseEnd_7958988 := by
    simpa [prefixWord, tailWord_7958988, baseEnd_7958988] using wordTrace_append hprefix tailTrace_7958988
  have hstable : (prefixWord ++ tailWord_7958988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958988).length < 2 ^ (prefixWord ++ tailWord_7958988).sum := by decide
  have hdescent : baseEnd_7958988 < baseStart_7958988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7958990 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_7958990 : Nat := 118140960795 + 7958990 * 2 ^ 59
def prefixEnd_7958990 : Nat := 4983230072969 + 3 ^ 40 * 7958990 * 2
def baseEnd_7958990 : Nat := 4086787394327920648722277

theorem tailTrace_7958990 : CollatzResearch.WordTrace tailWord_7958990 prefixEnd_7958990 4086787394327920648722277 := by
  unfold tailWord_7958990
  simp only [CollatzResearch.WordTrace]
  refine ⟨36286026679493249014840303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193525475623963994745814949 36286026679493249014840303)
  ·
    refine ⟨54429040019239873522260455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36286026679493249014840303 54429040019239873522260455)
    ·
      refine ⟨81643560028859810283390683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54429040019239873522260455 81643560028859810283390683)
      ·
        refine ⟨122465340043289715425086025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81643560028859810283390683 122465340043289715425086025)
        ·
          refine ⟨91849005032467286568814519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122465340043289715425086025 91849005032467286568814519)
          ·
            refine ⟨137773507548700929853221779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91849005032467286568814519 137773507548700929853221779)
            ·
              refine ⟨206660261323051394779832669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137773507548700929853221779 206660261323051394779832669)
              ·
                refine ⟨77497597996144273042437251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206660261323051394779832669 77497597996144273042437251)
                ·
                  refine ⟨116246396994216409563655877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77497597996144273042437251 116246396994216409563655877)
                  ·
                    refine ⟨21796199436415576793185477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116246396994216409563655877 21796199436415576793185477)
                    ·
                      refine ⟨4086787394327920648722277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21796199436415576793185477 4086787394327920648722277)
                      ·
                        rfl

theorem cell23_7958990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_7958990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7958990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7958990 prefixEnd_7958990 := by exact prefixLift 7958990
  have htrace : WordTrace (prefixWord ++ tailWord_7958990) baseStart_7958990 baseEnd_7958990 := by
    simpa [prefixWord, tailWord_7958990, baseEnd_7958990] using wordTrace_append hprefix tailTrace_7958990
  have hstable : (prefixWord ++ tailWord_7958990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7958990).length < 2 ^ (prefixWord ++ tailWord_7958990).sum := by decide
  have hdescent : baseEnd_7958990 < baseStart_7958990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7958990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959037 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 1, 7, 2]
def baseStart_7959037 : Nat := 118140960795 + 7959037 * 2 ^ 59
def prefixEnd_7959037 : Nat := 4983230072969 + 3 ^ 40 * 7959037 * 2
def baseEnd_7959037 : Nat := 4086811527918681964834561

theorem tailTrace_7959037 : CollatzResearch.WordTrace tailWord_7959037 prefixEnd_7959037 4086811527918681964834561 := by
  unfold tailWord_7959037
  simp only [CollatzResearch.WordTrace]
  refine ⟨290289927666775719145683365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193526618444517146097122243 290289927666775719145683365)
  ·
    refine ⟨54429361437520447339815631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290289927666775719145683365 54429361437520447339815631)
    ·
      refine ⟨81644042156280671009723447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54429361437520447339815631 81644042156280671009723447)
      ·
        refine ⟨122466063234421006514585171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81644042156280671009723447 122466063234421006514585171)
        ·
          refine ⟨183699094851631509771877757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122466063234421006514585171 183699094851631509771877757)
          ·
            refine ⟨68887160569361816164454159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183699094851631509771877757 68887160569361816164454159)
            ·
              refine ⟨103330740854042724246681239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68887160569361816164454159 103330740854042724246681239)
              ·
                refine ⟨154996111281064086370021859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103330740854042724246681239 154996111281064086370021859)
                ·
                  refine ⟨232494166921596129555032789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154996111281064086370021859 232494166921596129555032789)
                  ·
                    refine ⟨5449082037224909286446081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232494166921596129555032789 5449082037224909286446081)
                    ·
                      refine ⟨4086811527918681964834561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449082037224909286446081 4086811527918681964834561)
                      ·
                        rfl

theorem cell23_7959037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_7959037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959037 prefixEnd_7959037 := by exact prefixLift 7959037
  have htrace : WordTrace (prefixWord ++ tailWord_7959037) baseStart_7959037 baseEnd_7959037 := by
    simpa [prefixWord, tailWord_7959037, baseEnd_7959037] using wordTrace_append hprefix tailTrace_7959037
  have hstable : (prefixWord ++ tailWord_7959037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959037).length < 2 ^ (prefixWord ++ tailWord_7959037).sum := by decide
  have hdescent : baseEnd_7959037 < baseStart_7959037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959044 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_7959044 : Nat := 118140960795 + 7959044 * 2 ^ 59
def prefixEnd_7959044 : Nat := 4983230072969 + 3 ^ 40 * 7959044 * 2
def baseEnd_7959044 : Nat := 4086815122283263437447029

theorem tailTrace_7959044 : CollatzResearch.WordTrace tailWord_7959044 prefixEnd_7959044 4086815122283263437447029 := by
  unfold tailWord_7959044
  simp only [CollatzResearch.WordTrace]
  refine ⟨145145091488875179670594093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193526788651833572894125457 145145091488875179670594093)
  ·
    refine ⟨54429409308328192376472785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145145091488875179670594093 54429409308328192376472785)
    ·
      refine ⟨40822056981246144282354589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54429409308328192376472785 40822056981246144282354589)
      ·
        refine ⟨15308271367967304105882971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40822056981246144282354589 15308271367967304105882971)
        ·
          refine ⟨22962407051950956158824457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15308271367967304105882971 22962407051950956158824457)
          ·
            refine ⟨17221805288963217119118343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22962407051950956158824457 17221805288963217119118343)
            ·
              refine ⟨25832707933444825678677515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17221805288963217119118343 25832707933444825678677515)
              ·
                refine ⟨38749061900167238518016273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25832707933444825678677515 38749061900167238518016273)
                ·
                  refine ⟨29061796425125428888512205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38749061900167238518016273 29061796425125428888512205)
                  ·
                    refine ⟨10898173659422035833192077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29061796425125428888512205 10898173659422035833192077)
                    ·
                      refine ⟨4086815122283263437447029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10898173659422035833192077 4086815122283263437447029)
                      ·
                        rfl

theorem cell23_7959044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_7959044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959044 prefixEnd_7959044 := by exact prefixLift 7959044
  have htrace : WordTrace (prefixWord ++ tailWord_7959044) baseStart_7959044 baseEnd_7959044 := by
    simpa [prefixWord, tailWord_7959044, baseEnd_7959044] using wordTrace_append hprefix tailTrace_7959044
  have hstable : (prefixWord ++ tailWord_7959044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959044).length < 2 ^ (prefixWord ++ tailWord_7959044).sum := by decide
  have hdescent : baseEnd_7959044 < baseStart_7959044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959064 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 2, 5]
def baseStart_7959064 : Nat := 118140960795 + 7959064 * 2 ^ 59
def prefixEnd_7959064 : Nat := 4983230072969 + 3 ^ 40 * 7959064 * 2
def baseEnd_7959064 : Nat := 1362275130632117786398979

theorem tailTrace_7959064 : CollatzResearch.WordTrace tailWord_7959064 prefixEnd_7959064 1362275130632117786398979 := by
  unfold tailWord_7959064
  simp only [CollatzResearch.WordTrace]
  refine ⟨145145456218838951378458123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193527274958451935171277497 145145456218838951378458123)
  ·
    refine ⟨217718184328258427067687185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145145456218838951378458123 217718184328258427067687185)
    ·
      refine ⟨163288638246193820300765389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217718184328258427067687185 163288638246193820300765389)
      ·
        refine ⟨61233239342322682612787021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163288638246193820300765389 61233239342322682612787021)
        ·
          refine ⟨22962464753371005979795133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61233239342322682612787021 22962464753371005979795133)
          ·
            refine ⟨8610924282514127242423175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22962464753371005979795133 8610924282514127242423175)
            ·
              refine ⟨12916386423771190863634763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610924282514127242423175 12916386423771190863634763)
              ·
                refine ⟨19374579635656786295452145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12916386423771190863634763 19374579635656786295452145)
                ·
                  refine ⟨14530934726742589721589109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19374579635656786295452145 14530934726742589721589109)
                  ·
                    refine ⟨1362275130632117786398979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14530934726742589721589109 1362275130632117786398979)
                    ·
                      rfl

theorem cell23_7959064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_7959064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959064 prefixEnd_7959064 := by exact prefixLift 7959064
  have htrace : WordTrace (prefixWord ++ tailWord_7959064) baseStart_7959064 baseEnd_7959064 := by
    simpa [prefixWord, tailWord_7959064, baseEnd_7959064] using wordTrace_append hprefix tailTrace_7959064
  have hstable : (prefixWord ++ tailWord_7959064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959064).length < 2 ^ (prefixWord ++ tailWord_7959064).sum := by decide
  have hdescent : baseEnd_7959064 < baseStart_7959064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959138 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7959138 : Nat := 118140960795 + 7959138 * 2 ^ 59
def prefixEnd_7959138 : Nat := 4983230072969 + 3 ^ 40 * 7959138 * 2
def baseEnd_7959138 : Nat := 4086863389464786069671597

theorem tailTrace_7959138 : CollatzResearch.WordTrace tailWord_7959138 prefixEnd_7959138 4086863389464786069671597 := by
  unfold tailWord_7959138
  simp only [CollatzResearch.WordTrace]
  refine ⟨72573402859852453348777517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193529074292939875596740045 72573402859852453348777517)
  ·
    refine ⟨27215026072444670005791569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72573402859852453348777517 27215026072444670005791569)
    ·
      refine ⟨20411269554333502504343677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27215026072444670005791569 20411269554333502504343677)
      ·
        refine ⟨7654226082875063439128879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20411269554333502504343677 7654226082875063439128879)
        ·
          refine ⟨11481339124312595158693319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7654226082875063439128879 11481339124312595158693319)
          ·
            refine ⟨17222008686468892738039979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11481339124312595158693319 17222008686468892738039979)
            ·
              refine ⟨25833013029703339107059969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17222008686468892738039979 25833013029703339107059969)
              ·
                refine ⟨19374759772277504330294977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25833013029703339107059969 19374759772277504330294977)
                ·
                  refine ⟨14531069829208128247721233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19374759772277504330294977 14531069829208128247721233)
                  ·
                    refine ⟨10898302371906096185790925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14531069829208128247721233 10898302371906096185790925)
                    ·
                      refine ⟨4086863389464786069671597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10898302371906096185790925 4086863389464786069671597)
                      ·
                        rfl

theorem cell23_7959138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7959138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959138 prefixEnd_7959138 := by exact prefixLift 7959138
  have htrace : WordTrace (prefixWord ++ tailWord_7959138) baseStart_7959138 baseEnd_7959138 := by
    simpa [prefixWord, tailWord_7959138, baseEnd_7959138] using wordTrace_append hprefix tailTrace_7959138
  have hstable : (prefixWord ++ tailWord_7959138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959138).length < 2 ^ (prefixWord ++ tailWord_7959138).sum := by decide
  have hdescent : baseEnd_7959138 < baseStart_7959138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959151 : List Nat := [1, 1, 2, 1, 3, 2, 2, 6, 1, 1, 3]
def baseStart_7959151 : Nat := 118140960795 + 7959151 * 2 ^ 59
def prefixEnd_7959151 : Nat := 4983230072969 + 3 ^ 40 * 7959151 * 2
def baseEnd_7959151 : Nat := 4086870064713294518809037

theorem tailTrace_7959151 : CollatzResearch.WordTrace tailWord_7959151 prefixEnd_7959151 4086870064713294518809037 := by
  unfold tailWord_7959151
  simp only [CollatzResearch.WordTrace]
  refine ⟨290294085588362716615333307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193529390392241811076888871 290294085588362716615333307)
  ·
    refine ⟨435441128382544074922999961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290294085588362716615333307 435441128382544074922999961)
    ·
      refine ⟨326580846286908056192249971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435441128382544074922999961 326580846286908056192249971)
      ·
        refine ⟨489871269430362084288374957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326580846286908056192249971 489871269430362084288374957)
        ·
          refine ⟨183701726036385781608140609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489871269430362084288374957 183701726036385781608140609)
          ·
            refine ⟨137776294527289336206105457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183701726036385781608140609 137776294527289336206105457)
            ·
              refine ⟨103332220895467002154579093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137776294527289336206105457 103332220895467002154579093)
              ·
                refine ⟨4843697854475015725995895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103332220895467002154579093 4843697854475015725995895)
                ·
                  refine ⟨7265546781712523588993843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4843697854475015725995895 7265546781712523588993843)
                  ·
                    refine ⟨10898320172568785383490765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7265546781712523588993843 10898320172568785383490765)
                    ·
                      refine ⟨4086870064713294518809037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10898320172568785383490765 4086870064713294518809037)
                      ·
                        rfl

theorem cell23_7959151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 1, 1, 3].length) (baseStart_7959151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959151 prefixEnd_7959151 := by exact prefixLift 7959151
  have htrace : WordTrace (prefixWord ++ tailWord_7959151) baseStart_7959151 baseEnd_7959151 := by
    simpa [prefixWord, tailWord_7959151, baseEnd_7959151] using wordTrace_append hprefix tailTrace_7959151
  have hstable : (prefixWord ++ tailWord_7959151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959151).length < 2 ^ (prefixWord ++ tailWord_7959151).sum := by decide
  have hdescent : baseEnd_7959151 < baseStart_7959151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959158 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_7959158 : Nat := 118140960795 + 7959158 * 2 ^ 59
def prefixEnd_7959158 : Nat := 4983230072969 + 3 ^ 40 * 7959158 * 2
def baseEnd_7959158 : Nat := 454097073230875110157945

theorem tailTrace_7959158 : CollatzResearch.WordTrace tailWord_7959158 prefixEnd_7959158 454097073230875110157945 := by
  unfold tailWord_7959158
  simp only [CollatzResearch.WordTrace]
  refine ⟨18143396306208584800677383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193529560599558237873892085 18143396306208584800677383)
  ·
    refine ⟨27215094459312877201016075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18143396306208584800677383 27215094459312877201016075)
    ·
      refine ⟨40822641688969315801524113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27215094459312877201016075 40822641688969315801524113)
      ·
        refine ⟨30616981266726986851143085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40822641688969315801524113 30616981266726986851143085)
        ·
          refine ⟨11481367975022620069178657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30616981266726986851143085 11481367975022620069178657)
          ·
            refine ⟨8611025981266965051883993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11481367975022620069178657 8611025981266965051883993)
            ·
              refine ⟨6458269485950223788912995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8611025981266965051883993 6458269485950223788912995)
              ·
                refine ⟨9687404228925335683369493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458269485950223788912995 9687404228925335683369493)
                ·
                  refine ⟨454097073230875110157945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9687404228925335683369493 454097073230875110157945)
                  ·
                    rfl

theorem cell23_7959158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_7959158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959158 prefixEnd_7959158 := by exact prefixLift 7959158
  have htrace : WordTrace (prefixWord ++ tailWord_7959158) baseStart_7959158 baseEnd_7959158 := by
    simpa [prefixWord, tailWord_7959158, baseEnd_7959158] using wordTrace_append hprefix tailTrace_7959158
  have hstable : (prefixWord ++ tailWord_7959158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959158).length < 2 ^ (prefixWord ++ tailWord_7959158).sum := by decide
  have hdescent : baseEnd_7959158 < baseStart_7959158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959167 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 6, 4]
def baseStart_7959167 : Nat := 118140960795 + 7959167 * 2 ^ 59
def prefixEnd_7959167 : Nat := 4983230072969 + 3 ^ 40 * 7959167 * 2
def baseEnd_7959167 : Nat := 1362292760134588818736321

theorem tailTrace_7959167 : CollatzResearch.WordTrace tailWord_7959167 prefixEnd_7959167 1362292760134588818736321 := by
  unfold tailWord_7959167
  simp only [CollatzResearch.WordTrace]
  refine ⟨290294669156304751347915755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193529779437536500898610503 290294669156304751347915755)
  ·
    refine ⟨435442003734457127021873633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290294669156304751347915755 435442003734457127021873633)
    ·
      refine ⟨326581502800842845266405225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435442003734457127021873633 326581502800842845266405225)
      ·
        refine ⟨244936127100632133949803919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326581502800842845266405225 244936127100632133949803919)
        ·
          refine ⟨367404190650948200924705879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244936127100632133949803919 367404190650948200924705879)
          ·
            refine ⟨551106285976422301387058819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367404190650948200924705879 551106285976422301387058819)
            ·
              refine ⟨826659428964633452080588229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551106285976422301387058819 826659428964633452080588229)
              ·
                refine ⟨154998642930868772265110293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 826659428964633452080588229 154998642930868772265110293)
                ·
                  refine ⟨7265561387384473699927045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154998642930868772265110293 7265561387384473699927045)
                  ·
                    refine ⟨1362292760134588818736321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7265561387384473699927045 1362292760134588818736321)
                    ·
                      rfl

theorem cell23_7959167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 4].length) (baseStart_7959167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959167 prefixEnd_7959167 := by exact prefixLift 7959167
  have htrace : WordTrace (prefixWord ++ tailWord_7959167) baseStart_7959167 baseEnd_7959167 := by
    simpa [prefixWord, tailWord_7959167, baseEnd_7959167] using wordTrace_append hprefix tailTrace_7959167
  have hstable : (prefixWord ++ tailWord_7959167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959167).length < 2 ^ (prefixWord ++ tailWord_7959167).sum := by decide
  have hdescent : baseEnd_7959167 < baseStart_7959167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959178 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2]
def baseStart_7959178 : Nat := 118140960795 + 7959178 * 2 ^ 59
def prefixEnd_7959178 : Nat := 4983230072969 + 3 ^ 40 * 7959178 * 2
def baseEnd_7959178 : Nat := 4086883928690965913171413

theorem tailTrace_7959178 : CollatzResearch.WordTrace tailWord_7959178 prefixEnd_7959178 4086883928690965913171413 := by
  unfold tailWord_7959178
  simp only [CollatzResearch.WordTrace]
  refine ⟨72573767589816225056641547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193530046906176600151044125 72573767589816225056641547)
  ·
    refine ⟨108860651384724337584962321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72573767589816225056641547 108860651384724337584962321)
    ·
      refine ⟨81645488538543253188721741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108860651384724337584962321 81645488538543253188721741)
      ·
        refine ⟨30617058201953719945770653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81645488538543253188721741 30617058201953719945770653)
        ·
          refine ⟨11481396825732644979663995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30617058201953719945770653 11481396825732644979663995)
          ·
            refine ⟨17222095238598967469495993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11481396825732644979663995 17222095238598967469495993)
            ·
              refine ⟨12916571428949225602121995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17222095238598967469495993 12916571428949225602121995)
              ·
                refine ⟨19374857143423838403182993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12916571428949225602121995 19374857143423838403182993)
                ·
                  refine ⟨14531142857567878802387245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19374857143423838403182993 14531142857567878802387245)
                  ·
                    refine ⟨5449178571587954550895217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14531142857567878802387245 5449178571587954550895217)
                    ·
                      refine ⟨4086883928690965913171413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449178571587954550895217 4086883928690965913171413)
                      ·
                        rfl

theorem cell23_7959178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_7959178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959178 prefixEnd_7959178 := by exact prefixLift 7959178
  have htrace : WordTrace (prefixWord ++ tailWord_7959178) baseStart_7959178 baseEnd_7959178 := by
    simpa [prefixWord, tailWord_7959178, baseEnd_7959178] using wordTrace_append hprefix tailTrace_7959178
  have hstable : (prefixWord ++ tailWord_7959178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959178).length < 2 ^ (prefixWord ++ tailWord_7959178).sum := by decide
  have hdescent : baseEnd_7959178 < baseStart_7959178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959187 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 4]
def baseStart_7959187 : Nat := 118140960795 + 7959187 * 2 ^ 59
def prefixEnd_7959187 : Nat := 4983230072969 + 3 ^ 40 * 7959187 * 2
def baseEnd_7959187 : Nat := 4086888550016856377958871

theorem tailTrace_7959187 : CollatzResearch.WordTrace tailWord_7959187 prefixEnd_7959187 4086888550016856377958871 := by
  unfold tailWord_7959187
  simp only [CollatzResearch.WordTrace]
  refine ⟨290295398616232294763643815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193530265744154863175762543 290295398616232294763643815)
  ·
    refine ⟨435443097924348442145465723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290295398616232294763643815 435443097924348442145465723)
    ·
      refine ⟨653164646886522663218198585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435443097924348442145465723 653164646886522663218198585)
      ·
        refine ⟨489873485164891997413648939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653164646886522663218198585 489873485164891997413648939)
        ·
          refine ⟨734810227747337996120473409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489873485164891997413648939 734810227747337996120473409)
          ·
            refine ⟨551107670810503497090355057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734810227747337996120473409 551107670810503497090355057)
            ·
              refine ⟨413330753107877622817766293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551107670810503497090355057 413330753107877622817766293)
              ·
                refine ⟨19374879051931763569582795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 413330753107877622817766293 19374879051931763569582795)
                ·
                  refine ⟨29062318577897645354374193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19374879051931763569582795 29062318577897645354374193)
                  ·
                    refine ⟨21796738933423234015780645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29062318577897645354374193 21796738933423234015780645)
                    ·
                      refine ⟨4086888550016856377958871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21796738933423234015780645 4086888550016856377958871)
                      ·
                        rfl

theorem cell23_7959187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_7959187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959187 prefixEnd_7959187 := by exact prefixLift 7959187
  have htrace : WordTrace (prefixWord ++ tailWord_7959187) baseStart_7959187 baseEnd_7959187 := by
    simpa [prefixWord, tailWord_7959187, baseEnd_7959187] using wordTrace_append hprefix tailTrace_7959187
  have hstable : (prefixWord ++ tailWord_7959187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959187).length < 2 ^ (prefixWord ++ tailWord_7959187).sum := by decide
  have hdescent : baseEnd_7959187 < baseStart_7959187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959188 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_7959188 : Nat := 118140960795 + 7959188 * 2 ^ 59
def prefixEnd_7959188 : Nat := 4983230072969 + 3 ^ 40 * 7959188 * 2
def baseEnd_7959188 : Nat := 1362296354499170291348789

theorem tailTrace_7959188 : CollatzResearch.WordTrace tailWord_7959188 prefixEnd_7959188 1362296354499170291348789 := by
  unfold tailWord_7959188
  simp only [CollatzResearch.WordTrace]
  refine ⟨145147717544614335967215109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193530290059485781289620145 145147717544614335967215109)
  ·
    refine ⟨27215197039615187993852833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145147717544614335967215109 27215197039615187993852833)
    ·
      refine ⟨20411397779711390995389625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27215197039615187993852833 20411397779711390995389625)
      ·
        refine ⟨15308548334783543246542219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20411397779711390995389625 15308548334783543246542219)
        ·
          refine ⟨22962822502175314869813329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15308548334783543246542219 22962822502175314869813329)
          ·
            refine ⟨17222116876631486152359997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22962822502175314869813329 17222116876631486152359997)
            ·
              refine ⟨6458293828736807307134999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17222116876631486152359997 6458293828736807307134999)
              ·
                refine ⟨9687440743105210960702499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458293828736807307134999 9687440743105210960702499)
                ·
                  refine ⟨14531161114657816441053749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687440743105210960702499 14531161114657816441053749)
                  ·
                    refine ⟨1362296354499170291348789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14531161114657816441053749 1362296354499170291348789)
                    ·
                      rfl

theorem cell23_7959188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_7959188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959188 prefixEnd_7959188 := by exact prefixLift 7959188
  have htrace : WordTrace (prefixWord ++ tailWord_7959188) baseStart_7959188 baseEnd_7959188 := by
    simpa [prefixWord, tailWord_7959188, baseEnd_7959188] using wordTrace_append hprefix tailTrace_7959188
  have hstable : (prefixWord ++ tailWord_7959188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959188).length < 2 ^ (prefixWord ++ tailWord_7959188).sum := by decide
  have hdescent : baseEnd_7959188 < baseStart_7959188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959191 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 1, 1, 4]
def baseStart_7959191 : Nat := 118140960795 + 7959191 * 2 ^ 59
def prefixEnd_7959191 : Nat := 4983230072969 + 3 ^ 40 * 7959191 * 2
def baseEnd_7959191 : Nat := 4086890603939474362308853

theorem tailTrace_7959191 : CollatzResearch.WordTrace tailWord_7959191 prefixEnd_7959191 4086890603939474362308853 := by
  unfold tailWord_7959191
  simp only [CollatzResearch.WordTrace]
  refine ⟨290295544508217803446789427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193530363005478535631192951 290295544508217803446789427)
  ·
    refine ⟨435443316762326705170184141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290295544508217803446789427 435443316762326705170184141)
    ·
      refine ⟨163291243785872514438819053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435443316762326705170184141 163291243785872514438819053)
      ·
        refine ⟨61234216419702192914557145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163291243785872514438819053 61234216419702192914557145)
        ·
          refine ⟨45925662314776644685917859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61234216419702192914557145 45925662314776644685917859)
          ·
            refine ⟨68888493472164967028876789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45925662314776644685917859 68888493472164967028876789)
            ·
              refine ⟨6458296263015465658957199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68888493472164967028876789 6458296263015465658957199)
              ·
                refine ⟨9687444394523198488435799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6458296263015465658957199 9687444394523198488435799)
                ·
                  refine ⟨14531166591784797732653699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687444394523198488435799 14531166591784797732653699)
                  ·
                    refine ⟨21796749887677196598980549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14531166591784797732653699 21796749887677196598980549)
                    ·
                      refine ⟨4086890603939474362308853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21796749887677196598980549 4086890603939474362308853)
                      ·
                        rfl

theorem cell23_7959191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_7959191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959191 prefixEnd_7959191 := by exact prefixLift 7959191
  have htrace : WordTrace (prefixWord ++ tailWord_7959191) baseStart_7959191 baseEnd_7959191 := by
    simpa [prefixWord, tailWord_7959191, baseEnd_7959191] using wordTrace_append hprefix tailTrace_7959191
  have hstable : (prefixWord ++ tailWord_7959191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959191).length < 2 ^ (prefixWord ++ tailWord_7959191).sum := by decide
  have hdescent : baseEnd_7959191 < baseStart_7959191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959221 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_7959221 : Nat := 118140960795 + 7959221 * 2 ^ 59
def prefixEnd_7959221 : Nat := 4983230072969 + 3 ^ 40 * 7959221 * 2
def baseEnd_7959221 : Nat := 4086906008359109244933715

theorem tailTrace_7959221 : CollatzResearch.WordTrace tailWord_7959221 prefixEnd_7959221 4086906008359109244933715 := by
  unfold tailWord_7959221
  simp only [CollatzResearch.WordTrace]
  refine ⟨290296638698109118570381517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193531092465406079046921011 290296638698109118570381517)
  ·
    refine ⟨108861239511790919463893069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290296638698109118570381517 108861239511790919463893069)
    ·
      refine ⟨40822964816921594798959901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108861239511790919463893069 40822964816921594798959901)
      ·
        refine ⟨15308611806345598049609963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40822964816921594798959901 15308611806345598049609963)
        ·
          refine ⟨22962917709518397074414945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15308611806345598049609963 22962917709518397074414945)
          ·
            refine ⟨17222188282138797805811209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22962917709518397074414945 17222188282138797805811209)
            ·
              refine ⟨12916641211604098354358407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17222188282138797805811209 12916641211604098354358407)
              ·
                refine ⟨19374961817406147531537611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12916641211604098354358407 19374961817406147531537611)
                ·
                  refine ⟨29062442726109221297306417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19374961817406147531537611 29062442726109221297306417)
                  ·
                    refine ⟨21796832044581915972979813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29062442726109221297306417 21796832044581915972979813)
                    ·
                      refine ⟨4086906008359109244933715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21796832044581915972979813 4086906008359109244933715)
                      ·
                        rfl

theorem cell23_7959221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_7959221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959221 prefixEnd_7959221 := by exact prefixLift 7959221
  have htrace : WordTrace (prefixWord ++ tailWord_7959221) baseStart_7959221 baseEnd_7959221 := by
    simpa [prefixWord, tailWord_7959221, baseEnd_7959221] using wordTrace_append hprefix tailTrace_7959221
  have hstable : (prefixWord ++ tailWord_7959221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959221).length < 2 ^ (prefixWord ++ tailWord_7959221).sum := by decide
  have hdescent : baseEnd_7959221 < baseStart_7959221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959224 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 8, 1, 3]
def baseStart_7959224 : Nat := 118140960795 + 7959224 * 2 ^ 59
def prefixEnd_7959224 : Nat := 4983230072969 + 3 ^ 40 * 7959224 * 2
def baseEnd_7959224 : Nat := 4086907548801072733196201

theorem tailTrace_7959224 : CollatzResearch.WordTrace tailWord_7959224 prefixEnd_7959224 4086907548801072733196201 := by
  unfold tailWord_7959224
  simp only [CollatzResearch.WordTrace]
  refine ⟨145148374058549125041370363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193531165411398833388493817 145148374058549125041370363)
  ·
    refine ⟨217722561087823687562055545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145148374058549125041370363 217722561087823687562055545)
    ·
      refine ⟨163291920815867765671541659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217722561087823687562055545 163291920815867765671541659)
      ·
        refine ⟨244937881223801648507312489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163291920815867765671541659 244937881223801648507312489)
        ·
          refine ⟨183703410917851236380484367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244937881223801648507312489 183703410917851236380484367)
          ·
            refine ⟨275555116376776854570726551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183703410917851236380484367 275555116376776854570726551)
            ·
              refine ⟨413332674565165281856089827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275555116376776854570726551 413332674565165281856089827)
              ·
                refine ⟨619999011847747922784134741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413332674565165281856089827 619999011847747922784134741)
                ·
                  refine ⟨7265613420090795970126579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 619999011847747922784134741 7265613420090795970126579)
                  ·
                    refine ⟨10898420130136193955189869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7265613420090795970126579 10898420130136193955189869)
                    ·
                      refine ⟨4086907548801072733196201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10898420130136193955189869 4086907548801072733196201)
                      ·
                        rfl

theorem cell23_7959224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_7959224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959224 prefixEnd_7959224 := by exact prefixLift 7959224
  have htrace : WordTrace (prefixWord ++ tailWord_7959224) baseStart_7959224 baseEnd_7959224 := by
    simpa [prefixWord, tailWord_7959224, baseEnd_7959224] using wordTrace_append hprefix tailTrace_7959224
  have hstable : (prefixWord ++ tailWord_7959224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959224).length < 2 ^ (prefixWord ++ tailWord_7959224).sum := by decide
  have hdescent : baseEnd_7959224 < baseStart_7959224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959245 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_7959245 : Nat := 118140960795 + 7959245 * 2 ^ 59
def prefixEnd_7959245 : Nat := 4983230072969 + 3 ^ 40 * 7959245 * 2
def baseEnd_7959245 : Nat := 4086918331894817151033605

theorem tailTrace_7959245 : CollatzResearch.WordTrace tailWord_7959245 prefixEnd_7959245 4086918331894817151033605 := by
  unfold tailWord_7959245
  simp only [CollatzResearch.WordTrace]
  refine ⟨290297514050022170669255189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193531676033348113779503459 290297514050022170669255189)
  ·
    refine ⟨13607695971094789250121337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 290297514050022170669255189 13607695971094789250121337)
    ·
      refine ⟨10205771978321091937591003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13607695971094789250121337 10205771978321091937591003)
      ·
        refine ⟨15308657967481637906386505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10205771978321091937591003 15308657967481637906386505)
        ·
          refine ⟨11481493475611228429789879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15308657967481637906386505 11481493475611228429789879)
          ·
            refine ⟨17222240213416842644684819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11481493475611228429789879 17222240213416842644684819)
            ·
              refine ⟨25833360320125263967027229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17222240213416842644684819 25833360320125263967027229)
              ·
                refine ⟨9687510120046973987635211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25833360320125263967027229 9687510120046973987635211)
                ·
                  refine ⟨14531265180070460981452817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687510120046973987635211 14531265180070460981452817)
                  ·
                    refine ⟨10898448885052845736089613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14531265180070460981452817 10898448885052845736089613)
                    ·
                      refine ⟨4086918331894817151033605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10898448885052845736089613 4086918331894817151033605)
                      ·
                        rfl

theorem cell23_7959245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_7959245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959245 prefixEnd_7959245 := by exact prefixLift 7959245
  have htrace : WordTrace (prefixWord ++ tailWord_7959245) baseStart_7959245 baseEnd_7959245 := by
    simpa [prefixWord, tailWord_7959245, baseEnd_7959245] using wordTrace_append hprefix tailTrace_7959245
  have hstable : (prefixWord ++ tailWord_7959245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959245).length < 2 ^ (prefixWord ++ tailWord_7959245).sum := by decide
  have hdescent : baseEnd_7959245 < baseStart_7959245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959257 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 4, 6]
def baseStart_7959257 : Nat := 118140960795 + 7959257 * 2 ^ 59
def prefixEnd_7959257 : Nat := 4983230072969 + 3 ^ 40 * 7959257 * 2
def baseEnd_7959257 : Nat := 1362308164554223701361183

theorem tailTrace_7959257 : CollatzResearch.WordTrace tailWord_7959257 prefixEnd_7959257 1362308164554223701361183 := by
  unfold tailWord_7959257
  simp only [CollatzResearch.WordTrace]
  refine ⟨290297951725978696718692025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193531967817319131145794683 290297951725978696718692025)
  ·
    refine ⟨217723463794484022539019019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290297951725978696718692025 217723463794484022539019019)
    ·
      refine ⟨326585195691726033808528529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217723463794484022539019019 326585195691726033808528529)
      ·
        refine ⟨244938896768794525356396397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326585195691726033808528529 244938896768794525356396397)
        ·
          refine ⟨91852086288297947008648649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244938896768794525356396397 91852086288297947008648649)
          ·
            refine ⟨68889064716223460256486487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91852086288297947008648649 68889064716223460256486487)
            ·
              refine ⟨103333597074335190384729731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68889064716223460256486487 103333597074335190384729731)
              ·
                refine ⟨155000395611502785577094597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103333597074335190384729731 155000395611502785577094597)
                ·
                  refine ⟨29062574177156772295705237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155000395611502785577094597 29062574177156772295705237)
                  ·
                    refine ⟨1362308164554223701361183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29062574177156772295705237 1362308164554223701361183)
                    ·
                      rfl

theorem cell23_7959257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_7959257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959257 prefixEnd_7959257 := by exact prefixLift 7959257
  have htrace : WordTrace (prefixWord ++ tailWord_7959257) baseStart_7959257 baseEnd_7959257 := by
    simpa [prefixWord, tailWord_7959257, baseEnd_7959257] using wordTrace_append hprefix tailTrace_7959257
  have hstable : (prefixWord ++ tailWord_7959257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959257).length < 2 ^ (prefixWord ++ tailWord_7959257).sum := by decide
  have hdescent : baseEnd_7959257 < baseStart_7959257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959381 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_7959381 : Nat := 118140960795 + 7959381 * 2 ^ 59
def prefixEnd_7959381 : Nat := 4983230072969 + 3 ^ 40 * 7959381 * 2
def baseEnd_7959381 : Nat := 1362329388421276206310993

theorem tailTrace_7959381 : CollatzResearch.WordTrace tailWord_7959381 prefixEnd_7959381 1362329388421276206310993 := by
  unfold tailWord_7959381
  simp only [CollatzResearch.WordTrace]
  refine ⟨290302474377529465896205997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193534982918352977264137331 290302474377529465896205997)
  ·
    refine ⟨108863427891573549711077249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290302474377529465896205997 108863427891573549711077249)
    ·
      refine ⟨81647570918680162283307937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108863427891573549711077249 81647570918680162283307937)
      ·
        refine ⟨61235678189010121712480953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81647570918680162283307937 61235678189010121712480953)
        ·
          refine ⟨45926758641757591284360715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61235678189010121712480953 45926758641757591284360715)
          ·
            refine ⟨68890137962636386926541073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45926758641757591284360715 68890137962636386926541073)
            ·
              refine ⟨51667603471977290194905805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68890137962636386926541073 51667603471977290194905805)
              ·
                refine ⟨19375351301991483823089677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51667603471977290194905805 19375351301991483823089677)
                ·
                  refine ⟨7265756738246806433658629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19375351301991483823089677 7265756738246806433658629)
                  ·
                    refine ⟨1362329388421276206310993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7265756738246806433658629 1362329388421276206310993)
                    ·
                      rfl

theorem cell23_7959381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_7959381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959381 prefixEnd_7959381 := by exact prefixLift 7959381
  have htrace : WordTrace (prefixWord ++ tailWord_7959381) baseStart_7959381 baseEnd_7959381 := by
    simpa [prefixWord, tailWord_7959381, baseEnd_7959381] using wordTrace_append hprefix tailTrace_7959381
  have hstable : (prefixWord ++ tailWord_7959381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959381).length < 2 ^ (prefixWord ++ tailWord_7959381).sum := by decide
  have hdescent : baseEnd_7959381 < baseStart_7959381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959388 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7959388 : Nat := 118140960795 + 7959388 * 2 ^ 59
def prefixEnd_7959388 : Nat := 4983230072969 + 3 ^ 40 * 7959388 * 2
def baseEnd_7959388 : Nat := 4086991759628410091545447

theorem tailTrace_7959388 : CollatzResearch.WordTrace tailWord_7959388 prefixEnd_7959388 4086991759628410091545447 := by
  unfold tailWord_7959388
  simp only [CollatzResearch.WordTrace]
  refine ⟨145151364844252053045855409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193535153125669404061140545 145151364844252053045855409)
  ·
    refine ⟨108863523633189039784391557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145151364844252053045855409 108863523633189039784391557)
    ·
      refine ⟨20411910681222944959573417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108863523633189039784391557 20411910681222944959573417)
      ·
        refine ⟨15308933010917208719680063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20411910681222944959573417 15308933010917208719680063)
        ·
          refine ⟨22963399516375813079520095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15308933010917208719680063 22963399516375813079520095)
          ·
            refine ⟨34445099274563719619280143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22963399516375813079520095 34445099274563719619280143)
            ·
              refine ⟨51667648911845579428920215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34445099274563719619280143 51667648911845579428920215)
              ·
                refine ⟨77501473367768369143380323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51667648911845579428920215 77501473367768369143380323)
                ·
                  refine ⟨116252210051652553715070485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77501473367768369143380323 116252210051652553715070485)
                  ·
                    refine ⟨5449322346171213455393929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116252210051652553715070485 5449322346171213455393929)
                    ·
                      refine ⟨4086991759628410091545447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5449322346171213455393929 4086991759628410091545447)
                      ·
                        rfl

theorem cell23_7959388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7959388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959388 prefixEnd_7959388 := by exact prefixLift 7959388
  have htrace : WordTrace (prefixWord ++ tailWord_7959388) baseStart_7959388 baseEnd_7959388 := by
    simpa [prefixWord, tailWord_7959388, baseEnd_7959388] using wordTrace_append hprefix tailTrace_7959388
  have hstable : (prefixWord ++ tailWord_7959388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959388).length < 2 ^ (prefixWord ++ tailWord_7959388).sum := by decide
  have hdescent : baseEnd_7959388 < baseStart_7959388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959424 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 5, 5]
def baseStart_7959424 : Nat := 118140960795 + 7959424 * 2 ^ 59
def prefixEnd_7959424 : Nat := 4983230072969 + 3 ^ 40 * 7959424 * 2
def baseEnd_7959424 : Nat := 1362336748310657316898427

theorem tailTrace_7959424 : CollatzResearch.WordTrace tailWord_7959424 prefixEnd_7959424 1362336748310657316898427 := by
  unfold tailWord_7959424
  simp only [CollatzResearch.WordTrace]
  refine ⟨145152021358186842120010663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193536028477582456160014217 145152021358186842120010663)
  ·
    refine ⟨217728032037280263180015995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145152021358186842120010663 217728032037280263180015995)
    ·
      refine ⟨326592048055920394770023993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217728032037280263180015995 326592048055920394770023993)
      ·
        refine ⟨244944036041940296077517995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326592048055920394770023993 244944036041940296077517995)
        ·
          refine ⟨367416054062910444116276993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244944036041940296077517995 367416054062910444116276993)
          ·
            refine ⟨275562040547182833087207745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367416054062910444116276993 275562040547182833087207745)
            ·
              refine ⟨206671530410387124815405809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275562040547182833087207745 206671530410387124815405809)
              ·
                refine ⟨155003647807790343611554357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206671530410387124815405809 155003647807790343611554357)
                ·
                  refine ⟨14531591981980344713583221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155003647807790343611554357 14531591981980344713583221)
                  ·
                    refine ⟨1362336748310657316898427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14531591981980344713583221 1362336748310657316898427)
                    ·
                      rfl

theorem cell23_7959424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_7959424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959424 prefixEnd_7959424 := by exact prefixLift 7959424
  have htrace : WordTrace (prefixWord ++ tailWord_7959424) baseStart_7959424 baseEnd_7959424 := by
    simpa [prefixWord, tailWord_7959424, baseEnd_7959424] using wordTrace_append hprefix tailTrace_7959424
  have hstable : (prefixWord ++ tailWord_7959424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959424).length < 2 ^ (prefixWord ++ tailWord_7959424).sum := by decide
  have hdescent : baseEnd_7959424 < baseStart_7959424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959458 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_7959458 : Nat := 118140960795 + 7959458 * 2 ^ 59
def prefixEnd_7959458 : Nat := 4983230072969 + 3 ^ 40 * 7959458 * 2
def baseEnd_7959458 : Nat := 1362342567758074939223375

theorem tailTrace_7959458 : CollatzResearch.WordTrace tailWord_7959458 prefixEnd_7959458 1362342567758074939223375 := by
  unfold tailWord_7959458
  simp only [CollatzResearch.WordTrace]
  refine ⟨72576320699562627011689757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193536855198833672031172685 72576320699562627011689757)
  ·
    refine ⟨27216120262335985129383659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72576320699562627011689757 27216120262335985129383659)
    ·
      refine ⟨40824180393503977694075489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27216120262335985129383659 40824180393503977694075489)
      ·
        refine ⟨30618135295127983270556617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40824180393503977694075489 30618135295127983270556617)
        ·
          refine ⟨22963601471345987452917463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30618135295127983270556617 22963601471345987452917463)
          ·
            refine ⟨34445402207018981179376195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22963601471345987452917463 34445402207018981179376195)
            ·
              refine ⟨51668103310528471769064293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34445402207018981179376195 51668103310528471769064293)
              ·
                refine ⟨9687769370724088456699555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51668103310528471769064293 9687769370724088456699555)
                ·
                  refine ⟨14531654056086132685049333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9687769370724088456699555 14531654056086132685049333)
                  ·
                    refine ⟨1362342567758074939223375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14531654056086132685049333 1362342567758074939223375)
                    ·
                      rfl

theorem cell23_7959458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_7959458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959458 prefixEnd_7959458 := by exact prefixLift 7959458
  have htrace : WordTrace (prefixWord ++ tailWord_7959458) baseStart_7959458 baseEnd_7959458 := by
    simpa [prefixWord, tailWord_7959458, baseEnd_7959458] using wordTrace_append hprefix tailTrace_7959458
  have hstable : (prefixWord ++ tailWord_7959458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959458).length < 2 ^ (prefixWord ++ tailWord_7959458).sum := by decide
  have hdescent : baseEnd_7959458 < baseStart_7959458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7959481 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 5]
def baseStart_7959481 : Nat := 118140960795 + 7959481 * 2 ^ 59
def prefixEnd_7959481 : Nat := 4983230072969 + 3 ^ 40 * 7959481 * 2
def baseEnd_7959481 : Nat := 4087039513329278227682519

theorem tailTrace_7959481 : CollatzResearch.WordTrace tailWord_7959481 prefixEnd_7959481 4087039513329278227682519 := by
  unfold tailWord_7959481
  simp only [CollatzResearch.WordTrace]
  refine ⟨290306121677167182974846297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193537414451444788649897531 290306121677167182974846297)
  ·
    refine ⟨217729591257875387231134723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290306121677167182974846297 217729591257875387231134723)
    ·
      refine ⟨326594386886813080846702085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217729591257875387231134723 326594386886813080846702085)
      ·
        refine ⟨61236447541277452658756641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326594386886813080846702085 61236447541277452658756641)
        ·
          refine ⟨45927335655958089494067481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61236447541277452658756641 45927335655958089494067481)
          ·
            refine ⟨34445501741968567120550611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45927335655958089494067481 34445501741968567120550611)
            ·
              refine ⟨51668252612952850680825917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34445501741968567120550611 51668252612952850680825917)
              ·
                refine ⟨19375594729857319005309719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51668252612952850680825917 19375594729857319005309719)
                ·
                  refine ⟨29063392094785978507964579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19375594729857319005309719 29063392094785978507964579)
                  ·
                    refine ⟨43595088142178967761946869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29063392094785978507964579 43595088142178967761946869)
                    ·
                      refine ⟨4087039513329278227682519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43595088142178967761946869 4087039513329278227682519)
                      ·
                        rfl

theorem cell23_7959481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_7959481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7959481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7959481 prefixEnd_7959481 := by exact prefixLift 7959481
  have htrace : WordTrace (prefixWord ++ tailWord_7959481) baseStart_7959481 baseEnd_7959481 := by
    simpa [prefixWord, tailWord_7959481, baseEnd_7959481] using wordTrace_append hprefix tailTrace_7959481
  have hstable : (prefixWord ++ tailWord_7959481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7959481).length < 2 ^ (prefixWord ++ tailWord_7959481).sum := by decide
  have hdescent : baseEnd_7959481 < baseStart_7959481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7959481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
