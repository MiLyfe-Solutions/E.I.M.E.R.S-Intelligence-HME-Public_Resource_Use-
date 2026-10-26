import V185TrunkScan23Chunk1336

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7918233 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 1, 6, 3]
def baseStart_7918233 : Nat := 118140960795 + 7918233 * 2 ^ 59
def prefixEnd_7918233 : Nat := 4983230072969 + 3 ^ 40 * 7918233 * 2
def baseEnd_7918233 : Nat := 4065859463292623610672215

theorem tailTrace_7918233 : CollatzResearch.WordTrace tailWord_7918233 prefixEnd_7918233 4065859463292623610672215 := by
  unfold tailWord_7918233
  simp only [CollatzResearch.WordTrace]
  refine ⟨288801683522601642377295353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192534455681734428251530235 288801683522601642377295353)
  ·
    refine ⟨216601262641951231782971515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288801683522601642377295353 216601262641951231782971515)
    ·
      refine ⟨324901893962926847674457273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216601262641951231782971515 324901893962926847674457273)
      ·
        refine ⟨243676420472195135755842955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324901893962926847674457273 243676420472195135755842955)
        ·
          refine ⟨365514630708292703633764433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243676420472195135755842955 365514630708292703633764433)
          ·
            refine ⟨274135973031219527725323325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365514630708292703633764433 274135973031219527725323325)
            ·
              refine ⟨102800989886707322896996247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274135973031219527725323325 102800989886707322896996247)
              ·
                refine ⟨154201484830060984345494371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102800989886707322896996247 154201484830060984345494371)
                ·
                  refine ⟨231302227245091476518241557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154201484830060984345494371 231302227245091476518241557)
                  ·
                    refine ⟨10842291902113662961792573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 231302227245091476518241557 10842291902113662961792573)
                    ·
                      refine ⟨4065859463292623610672215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10842291902113662961792573 4065859463292623610672215)
                      ·
                        rfl

theorem cell23_7918233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_7918233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918233 prefixEnd_7918233 := by exact prefixLift 7918233
  have htrace : WordTrace (prefixWord ++ tailWord_7918233) baseStart_7918233 baseEnd_7918233 := by
    simpa [prefixWord, tailWord_7918233, baseEnd_7918233] using wordTrace_append hprefix tailTrace_7918233
  have hstable : (prefixWord ++ tailWord_7918233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918233).length < 2 ^ (prefixWord ++ tailWord_7918233).sum := by decide
  have hdescent : baseEnd_7918233 < baseStart_7918233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918240 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 2, 6]
def baseStart_7918240 : Nat := 118140960795 + 7918240 * 2 ^ 59
def prefixEnd_7918240 : Nat := 4983230072969 + 3 ^ 40 * 7918240 * 2
def baseEnd_7918240 : Nat := 1355287685885735027761561

theorem tailTrace_7918240 : CollatzResearch.WordTrace tailWord_7918240 prefixEnd_7918240 1355287685885735027761561 := by
  unfold tailWord_7918240
  simp only [CollatzResearch.WordTrace]
  refine ⟨144400969416788141286400087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192534625889050855048533449 144400969416788141286400087)
  ·
    refine ⟨216601454125182211929600131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144400969416788141286400087 216601454125182211929600131)
    ·
      refine ⟨324902181187773317894400197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216601454125182211929600131 324902181187773317894400197)
      ·
        refine ⟨60919158972707497105200037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324902181187773317894400197 60919158972707497105200037)
        ·
          refine ⟨11422342307382655707225007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60919158972707497105200037 11422342307382655707225007)
          ·
            refine ⟨17133513461073983560837511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11422342307382655707225007 17133513461073983560837511)
            ·
              refine ⟨25700270191610975341256267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17133513461073983560837511 25700270191610975341256267)
              ·
                refine ⟨38550405287416463011884401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25700270191610975341256267 38550405287416463011884401)
                ·
                  refine ⟨28912803965562347258913301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38550405287416463011884401 28912803965562347258913301)
                  ·
                    refine ⟨1355287685885735027761561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28912803965562347258913301 1355287685885735027761561)
                    ·
                      rfl

theorem cell23_7918240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 6].length) (baseStart_7918240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918240 prefixEnd_7918240 := by exact prefixLift 7918240
  have htrace : WordTrace (prefixWord ++ tailWord_7918240) baseStart_7918240 baseEnd_7918240 := by
    simpa [prefixWord, tailWord_7918240, baseEnd_7918240] using wordTrace_append hprefix tailTrace_7918240
  have hstable : (prefixWord ++ tailWord_7918240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918240).length < 2 ^ (prefixWord ++ tailWord_7918240).sum := by decide
  have hdescent : baseEnd_7918240 < baseStart_7918240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918280 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_7918280 : Nat := 118140960795 + 7918280 * 2 ^ 59
def prefixEnd_7918280 : Nat := 4983230072969 + 3 ^ 40 * 7918280 * 2
def baseEnd_7918280 : Nat := 4065883596883384926784499

theorem tailTrace_7918280 : CollatzResearch.WordTrace tailWord_7918280 prefixEnd_7918280 4065883596883384926784499 := by
  unfold tailWord_7918280
  simp only [CollatzResearch.WordTrace]
  refine ⟨144401698876715684702128147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192535598502287579602837529 144401698876715684702128147)
  ·
    refine ⟨216602548315073527053192221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144401698876715684702128147 216602548315073527053192221)
    ·
      refine ⟨81225955618152572644947083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216602548315073527053192221 81225955618152572644947083)
      ·
        refine ⟨121838933427228858967420625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81225955618152572644947083 121838933427228858967420625)
        ·
          refine ⟨91379200070421644225565469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121838933427228858967420625 91379200070421644225565469)
          ·
            refine ⟨34267200026408116584587051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91379200070421644225565469 34267200026408116584587051)
            ·
              refine ⟨51400800039612174876880577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34267200026408116584587051 51400800039612174876880577)
              ·
                refine ⟨38550600029709131157660433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51400800039612174876880577 38550600029709131157660433)
                ·
                  refine ⟨28912950022281848368245325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38550600029709131157660433 28912950022281848368245325)
                  ·
                    refine ⟨10842356258355693138091997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28912950022281848368245325 10842356258355693138091997)
                    ·
                      refine ⟨4065883596883384926784499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10842356258355693138091997 4065883596883384926784499)
                      ·
                        rfl

theorem cell23_7918280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_7918280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918280 prefixEnd_7918280 := by exact prefixLift 7918280
  have htrace : WordTrace (prefixWord ++ tailWord_7918280) baseStart_7918280 baseEnd_7918280 := by
    simpa [prefixWord, tailWord_7918280, baseEnd_7918280] using wordTrace_append hprefix tailTrace_7918280
  have hstable : (prefixWord ++ tailWord_7918280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918280).length < 2 ^ (prefixWord ++ tailWord_7918280).sum := by decide
  have hdescent : baseEnd_7918280 < baseStart_7918280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918320 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 4]
def baseStart_7918320 : Nat := 118140960795 + 7918320 * 2 ^ 59
def prefixEnd_7918320 : Nat := 4983230072969 + 3 ^ 40 * 7918320 * 2
def baseEnd_7918320 : Nat := 4065904136109564770284315

theorem tailTrace_7918320 : CollatzResearch.WordTrace tailWord_7918320 prefixEnd_7918320 4065904136109564770284315 := by
  unfold tailWord_7918320
  simp only [CollatzResearch.WordTrace]
  refine ⟨144402428336643228117856207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192536571115524304157141609 144402428336643228117856207)
  ·
    refine ⟨216603642504964842176784311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144402428336643228117856207 216603642504964842176784311)
    ·
      refine ⟨324905463757447263265176467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216603642504964842176784311 324905463757447263265176467)
      ·
        refine ⟨487358195636170894897764701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324905463757447263265176467 487358195636170894897764701)
        ·
          refine ⟨182759323363564085586661763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487358195636170894897764701 182759323363564085586661763)
          ·
            refine ⟨274138985045346128379992645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182759323363564085586661763 274138985045346128379992645)
            ·
              refine ⟨51401059696002399071248621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274138985045346128379992645 51401059696002399071248621)
              ·
                refine ⟨19275397386000899651718233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51401059696002399071248621 19275397386000899651718233)
                ·
                  refine ⟨14456548039500674738788675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19275397386000899651718233 14456548039500674738788675)
                  ·
                    refine ⟨21684822059251012108183013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14456548039500674738788675 21684822059251012108183013)
                    ·
                      refine ⟨4065904136109564770284315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21684822059251012108183013 4065904136109564770284315)
                      ·
                        rfl

theorem cell23_7918320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_7918320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918320 prefixEnd_7918320 := by exact prefixLift 7918320
  have htrace : WordTrace (prefixWord ++ tailWord_7918320) baseStart_7918320 baseEnd_7918320 := by
    simpa [prefixWord, tailWord_7918320, baseEnd_7918320] using wordTrace_append hprefix tailTrace_7918320
  have hstable : (prefixWord ++ tailWord_7918320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918320).length < 2 ^ (prefixWord ++ tailWord_7918320).sum := by decide
  have hdescent : baseEnd_7918320 < baseStart_7918320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918323 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 5]
def baseStart_7918323 : Nat := 118140960795 + 7918323 * 2 ^ 59
def prefixEnd_7918323 : Nat := 4983230072969 + 3 ^ 40 * 7918323 * 2
def baseEnd_7918323 : Nat := 4065905676551528258546801

theorem tailTrace_7918323 : CollatzResearch.WordTrace tailWord_7918323 prefixEnd_7918323 4065905676551528258546801 := by
  unfold tailWord_7918323
  simp only [CollatzResearch.WordTrace]
  refine ⟨288804966092275587748071623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192536644061517058498714415 288804966092275587748071623)
  ·
    refine ⟨433207449138413381622107435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288804966092275587748071623 433207449138413381622107435)
    ·
      refine ⟨649811173707620072433161153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433207449138413381622107435 649811173707620072433161153)
      ·
        refine ⟨487358380280715054324870865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649811173707620072433161153 487358380280715054324870865)
        ·
          refine ⟨365518785210536290743653149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487358380280715054324870865 365518785210536290743653149)
          ·
            refine ⟨137069544453951109028869931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365518785210536290743653149 137069544453951109028869931)
            ·
              refine ⟨205604316680926663543304897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137069544453951109028869931 205604316680926663543304897)
              ·
                refine ⟨154203237510694997657478673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205604316680926663543304897 154203237510694997657478673)
                ·
                  refine ⟨115652428133021248243109005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154203237510694997657478673 115652428133021248243109005)
                  ·
                    refine ⟨43369660549882968091165877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115652428133021248243109005 43369660549882968091165877)
                    ·
                      refine ⟨4065905676551528258546801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43369660549882968091165877 4065905676551528258546801)
                      ·
                        rfl

theorem cell23_7918323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_7918323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918323 prefixEnd_7918323 := by exact prefixLift 7918323
  have htrace : WordTrace (prefixWord ++ tailWord_7918323) baseStart_7918323 baseEnd_7918323 := by
    simpa [prefixWord, tailWord_7918323, baseEnd_7918323] using wordTrace_append hprefix tailTrace_7918323
  have hstable : (prefixWord ++ tailWord_7918323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918323).length < 2 ^ (prefixWord ++ tailWord_7918323).sum := by decide
  have hdescent : baseEnd_7918323 < baseStart_7918323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918330 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_7918330 : Nat := 118140960795 + 7918330 * 2 ^ 59
def prefixEnd_7918330 : Nat := 4983230072969 + 3 ^ 40 * 7918330 * 2
def baseEnd_7918330 : Nat := 1355303090305369910386423

theorem tailTrace_7918330 : CollatzResearch.WordTrace tailWord_7918330 prefixEnd_7918330 1355303090305369910386423 := by
  unfold tailWord_7918330
  simp only [CollatzResearch.WordTrace]
  refine ⟨72201305350812556985894111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192536814268833485295717629 72201305350812556985894111)
  ·
    refine ⟨108301958026218835478841167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72201305350812556985894111 108301958026218835478841167)
    ·
      refine ⟨162452937039328253218261751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108301958026218835478841167 162452937039328253218261751)
      ·
        refine ⟨243679405558992379827392627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162452937039328253218261751 243679405558992379827392627)
        ·
          refine ⟨365519108338488569741088941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243679405558992379827392627 365519108338488569741088941)
          ·
            refine ⟨137069665626933213652908353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365519108338488569741088941 137069665626933213652908353)
            ·
              refine ⟨102802249220199910239681265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137069665626933213652908353 102802249220199910239681265)
              ·
                refine ⟨77101686915149932679760949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102802249220199910239681265 77101686915149932679760949)
                ·
                  refine ⟨7228283148295306188727589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77101686915149932679760949 7228283148295306188727589)
                  ·
                    refine ⟨1355303090305369910386423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7228283148295306188727589 1355303090305369910386423)
                    ·
                      rfl

theorem cell23_7918330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_7918330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918330 prefixEnd_7918330 := by exact prefixLift 7918330
  have htrace : WordTrace (prefixWord ++ tailWord_7918330) baseStart_7918330 baseEnd_7918330 := by
    simpa [prefixWord, tailWord_7918330, baseEnd_7918330] using wordTrace_append hprefix tailTrace_7918330
  have hstable : (prefixWord ++ tailWord_7918330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918330).length < 2 ^ (prefixWord ++ tailWord_7918330).sum := by decide
  have hdescent : baseEnd_7918330 < baseStart_7918330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918444 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 5, 2, 2]
def baseStart_7918444 : Nat := 118140960795 + 7918444 * 2 ^ 59
def prefixEnd_7918444 : Nat := 4983230072969 + 3 ^ 40 * 7918444 * 2
def baseEnd_7918444 : Nat := 4065967807710722285133745

theorem tailTrace_7918444 : CollatzResearch.WordTrace tailWord_7918444 prefixEnd_7918444 4065967807710722285133745 := by
  unfold tailWord_7918444
  simp only [CollatzResearch.WordTrace]
  refine ⟨144404689662418612706613193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192539586216558150275484257 144404689662418612706613193)
  ·
    refine ⟨108303517246813959529959895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144404689662418612706613193 108303517246813959529959895)
    ·
      refine ⟨162455275870220939294939843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108303517246813959529959895 162455275870220939294939843)
      ·
        refine ⟨243682913805331408942409765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162455275870220939294939843 243682913805331408942409765)
        ·
          refine ⟨45690546338499639176701831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243682913805331408942409765 45690546338499639176701831)
          ·
            refine ⟨68535819507749458765052747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45690546338499639176701831 68535819507749458765052747)
            ·
              refine ⟨102803729261624188147579121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68535819507749458765052747 102803729261624188147579121)
              ·
                refine ⟨77102796946218141110684341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102803729261624188147579121 77102796946218141110684341)
                ·
                  refine ⟨7228387213707950729126657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77102796946218141110684341 7228387213707950729126657)
                  ·
                    refine ⟨5421290410280963046844993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7228387213707950729126657 5421290410280963046844993)
                    ·
                      refine ⟨4065967807710722285133745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421290410280963046844993 4065967807710722285133745)
                      ·
                        rfl

theorem cell23_7918444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_7918444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918444 prefixEnd_7918444 := by exact prefixLift 7918444
  have htrace : WordTrace (prefixWord ++ tailWord_7918444) baseStart_7918444 baseEnd_7918444 := by
    simpa [prefixWord, tailWord_7918444, baseEnd_7918444] using wordTrace_append hprefix tailTrace_7918444
  have hstable : (prefixWord ++ tailWord_7918444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918444).length < 2 ^ (prefixWord ++ tailWord_7918444).sum := by decide
  have hdescent : baseEnd_7918444 < baseStart_7918444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918471 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 2, 4]
def baseStart_7918471 : Nat := 118140960795 + 7918471 * 2 ^ 59
def prefixEnd_7918471 : Nat := 4983230072969 + 3 ^ 40 * 7918471 * 2
def baseEnd_7918471 : Nat := 1355327223896131226498707

theorem tailTrace_7918471 : CollatzResearch.WordTrace tailWord_7918471 prefixEnd_7918471 1355327223896131226498707 := by
  unfold tailWord_7918471
  simp only [CollatzResearch.WordTrace]
  refine ⟨288810364095739409024459267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192540242730492939349639511 288810364095739409024459267)
  ·
    refine ⟨433215546143609113536688901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288810364095739409024459267 433215546143609113536688901)
    ·
      refine ⟨81227914901926708788129169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433215546143609113536688901 81227914901926708788129169)
      ·
        refine ⟨60920936176445031591096877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81227914901926708788129169 60920936176445031591096877)
        ·
          refine ⟨22845351066166886846661329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60920936176445031591096877 22845351066166886846661329)
          ·
            refine ⟨17134013299625165134995997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22845351066166886846661329 17134013299625165134995997)
            ·
              refine ⟨6425254987359436925623499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17134013299625165134995997 6425254987359436925623499)
              ·
                refine ⟨9637882481039155388435249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6425254987359436925623499 9637882481039155388435249)
                ·
                  refine ⟨7228411860779366541326437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9637882481039155388435249 7228411860779366541326437)
                  ·
                    refine ⟨1355327223896131226498707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7228411860779366541326437 1355327223896131226498707)
                    ·
                      rfl

theorem cell23_7918471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_7918471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918471 prefixEnd_7918471 := by exact prefixLift 7918471
  have htrace : WordTrace (prefixWord ++ tailWord_7918471) baseStart_7918471 baseEnd_7918471 := by
    simpa [prefixWord, tailWord_7918471, baseEnd_7918471] using wordTrace_append hprefix tailTrace_7918471
  have hstable : (prefixWord ++ tailWord_7918471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918471).length < 2 ^ (prefixWord ++ tailWord_7918471).sum := by decide
  have hdescent : baseEnd_7918471 < baseStart_7918471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918474 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_7918474 : Nat := 118140960795 + 7918474 * 2 ^ 59
def prefixEnd_7918474 : Nat := 4983230072969 + 3 ^ 40 * 7918474 * 2
def baseEnd_7918474 : Nat := 4065983212130357167758607

theorem tailTrace_7918474 : CollatzResearch.WordTrace tailWord_7918474 prefixEnd_7918474 4065983212130357167758607 := by
  unfold tailWord_7918474
  simp only [CollatzResearch.WordTrace]
  refine ⟨72202618378682135134204619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192540315676485693691212317 72202618378682135134204619)
  ·
    refine ⟨108303927568023202701306929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72202618378682135134204619 108303927568023202701306929)
    ·
      refine ⟨81227945676017402025980197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108303927568023202701306929 81227945676017402025980197)
      ·
        refine ⟨15230239814253262879871287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81227945676017402025980197 15230239814253262879871287)
        ·
          refine ⟨22845359721379894319806931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15230239814253262879871287 22845359721379894319806931)
          ·
            refine ⟨34268039582069841479710397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22845359721379894319806931 34268039582069841479710397)
            ·
              refine ⟨12850514843276190554891399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34268039582069841479710397 12850514843276190554891399)
              ·
                refine ⟨19275772264914285832337099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12850514843276190554891399 19275772264914285832337099)
                ·
                  refine ⟨28913658397371428748505649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19275772264914285832337099 28913658397371428748505649)
                  ·
                    refine ⟨21685243798028571561379237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28913658397371428748505649 21685243798028571561379237)
                    ·
                      refine ⟨4065983212130357167758607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21685243798028571561379237 4065983212130357167758607)
                      ·
                        rfl

theorem cell23_7918474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_7918474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918474 prefixEnd_7918474 := by exact prefixLift 7918474
  have htrace : WordTrace (prefixWord ++ tailWord_7918474) baseStart_7918474 baseEnd_7918474 := by
    simpa [prefixWord, tailWord_7918474, baseEnd_7918474] using wordTrace_append hprefix tailTrace_7918474
  have hstable : (prefixWord ++ tailWord_7918474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918474).length < 2 ^ (prefixWord ++ tailWord_7918474).sum := by decide
  have hdescent : baseEnd_7918474 < baseStart_7918474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918495 : List Nat := [1, 1, 2, 5, 2, 3, 1, 3, 1, 2, 2]
def baseStart_7918495 : Nat := 118140960795 + 7918495 * 2 ^ 59
def prefixEnd_7918495 : Nat := 4983230072969 + 3 ^ 40 * 7918495 * 2
def baseEnd_7918495 : Nat := 4065993995224101585596011

theorem tailTrace_7918495 : CollatzResearch.WordTrace tailWord_7918495 prefixEnd_7918495 4065993995224101585596011 := by
  unfold tailWord_7918495
  simp only [CollatzResearch.WordTrace]
  refine ⟨288811239447652461123332939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192540826298434974082221959 288811239447652461123332939)
  ·
    refine ⟨433216859171478691684999409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288811239447652461123332939 433216859171478691684999409)
    ·
      refine ⟨324912644378609018763749557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433216859171478691684999409 324912644378609018763749557)
      ·
        refine ⟨30460560410494595509101521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 324912644378609018763749557 30460560410494595509101521)
        ·
          refine ⟨22845420307870946631826141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30460560410494595509101521 22845420307870946631826141)
          ·
            refine ⟨8567032615451604986934803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22845420307870946631826141 8567032615451604986934803)
            ·
              refine ⟨12850548923177407480402205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8567032615451604986934803 12850548923177407480402205)
              ·
                refine ⟨4818955846191527805150827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12850548923177407480402205 4818955846191527805150827)
                ·
                  refine ⟨7228433769287291707726241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818955846191527805150827 7228433769287291707726241)
                  ·
                    refine ⟨5421325326965468780794681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7228433769287291707726241 5421325326965468780794681)
                    ·
                      refine ⟨4065993995224101585596011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421325326965468780794681 4065993995224101585596011)
                      ·
                        rfl

theorem cell23_7918495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_7918495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918495 prefixEnd_7918495 := by exact prefixLift 7918495
  have htrace : WordTrace (prefixWord ++ tailWord_7918495) baseStart_7918495 baseEnd_7918495 := by
    simpa [prefixWord, tailWord_7918495, baseEnd_7918495] using wordTrace_append hprefix tailTrace_7918495
  have hstable : (prefixWord ++ tailWord_7918495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918495).length < 2 ^ (prefixWord ++ tailWord_7918495).sum := by decide
  have hdescent : baseEnd_7918495 < baseStart_7918495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918517 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7918517 : Nat := 118140960795 + 7918517 * 2 ^ 59
def prefixEnd_7918517 : Nat := 4983230072969 + 3 ^ 40 * 7918517 * 2
def baseEnd_7918517 : Nat := 4066005291798500499520909

theorem tailTrace_7918517 : CollatzResearch.WordTrace tailWord_7918517 prefixEnd_7918517 4066005291798500499520909 := by
  unfold tailWord_7918517
  simp only [CollatzResearch.WordTrace]
  refine ⟨288812041853572758880633805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192541361235715172587089203 288812041853572758880633805)
  ·
    refine ⟨108304515695089784580237677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288812041853572758880633805 108304515695089784580237677)
    ·
      refine ⟨40614193385658669217589129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108304515695089784580237677 40614193385658669217589129)
      ·
        refine ⟨30460645039244001913191847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40614193385658669217589129 30460645039244001913191847)
        ·
          refine ⟨45690967558866002869787771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30460645039244001913191847 45690967558866002869787771)
          ·
            refine ⟨68536451338299004304681657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45690967558866002869787771 68536451338299004304681657)
            ·
              refine ⟨51402338503724253228511243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68536451338299004304681657 51402338503724253228511243)
              ·
                refine ⟨77103507755586379842766865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51402338503724253228511243 77103507755586379842766865)
                ·
                  refine ⟨57827630816689784882075149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77103507755586379842766865 57827630816689784882075149)
                  ·
                    refine ⟨21685361556258669330778181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57827630816689784882075149 21685361556258669330778181)
                    ·
                      refine ⟨4066005291798500499520909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21685361556258669330778181 4066005291798500499520909)
                      ·
                        rfl

theorem cell23_7918517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7918517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918517 prefixEnd_7918517 := by exact prefixLift 7918517
  have htrace : WordTrace (prefixWord ++ tailWord_7918517) baseStart_7918517 baseEnd_7918517 := by
    simpa [prefixWord, tailWord_7918517, baseEnd_7918517] using wordTrace_append hprefix tailTrace_7918517
  have hstable : (prefixWord ++ tailWord_7918517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918517).length < 2 ^ (prefixWord ++ tailWord_7918517).sum := by decide
  have hdescent : baseEnd_7918517 < baseStart_7918517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918518 : List Nat := [5, 1, 4, 1, 1, 1, 2, 8]
def baseStart_7918518 : Nat := 118140960795 + 7918518 * 2 ^ 59
def prefixEnd_7918518 : Nat := 4983230072969 + 3 ^ 40 * 7918518 * 2
def baseEnd_7918518 : Nat := 150592807602931666504015

theorem tailTrace_7918518 : CollatzResearch.WordTrace tailWord_7918518 prefixEnd_7918518 150592807602931666504015 := by
  unfold tailWord_7918518
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050754895410571003213763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192541385551046090700946805 18050754895410571003213763)
  ·
    refine ⟨27076132343115856504820645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18050754895410571003213763 27076132343115856504820645)
    ·
      refine ⟨5076774814334223094653871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27076132343115856504820645 5076774814334223094653871)
      ·
        refine ⟨7615162221501334641980807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5076774814334223094653871 7615162221501334641980807)
        ·
          refine ⟨11422743332252001962971211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7615162221501334641980807 11422743332252001962971211)
          ·
            refine ⟨17134114998378002944456817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11422743332252001962971211 17134114998378002944456817)
            ·
              refine ⟨12850586248783502208342613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17134114998378002944456817 12850586248783502208342613)
              ·
                refine ⟨150592807602931666504015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12850586248783502208342613 150592807602931666504015)
                ·
                  rfl

theorem cell23_7918518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_7918518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918518 prefixEnd_7918518 := by exact prefixLift 7918518
  have htrace : WordTrace (prefixWord ++ tailWord_7918518) baseStart_7918518 baseEnd_7918518 := by
    simpa [prefixWord, tailWord_7918518, baseEnd_7918518] using wordTrace_append hprefix tailTrace_7918518
  have hstable : (prefixWord ++ tailWord_7918518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918518).length < 2 ^ (prefixWord ++ tailWord_7918518).sum := by decide
  have hdescent : baseEnd_7918518 < baseStart_7918518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918528 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 2, 1, 3]
def baseStart_7918528 : Nat := 118140960795 + 7918528 * 2 ^ 59
def prefixEnd_7918528 : Nat := 4983230072969 + 3 ^ 40 * 7918528 * 2
def baseEnd_7918528 : Nat := 4066010940085699956483359

theorem tailTrace_7918528 : CollatzResearch.WordTrace tailWord_7918528 prefixEnd_7918528 4066010940085699956483359 := by
  unfold tailWord_7918528
  simp only [CollatzResearch.WordTrace]
  refine ⟨144406221528266453879642119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192541628704355271839522825 144406221528266453879642119)
  ·
    refine ⟨216609332292399680819463179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144406221528266453879642119 216609332292399680819463179)
    ·
      refine ⟨324913998438599521229194769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216609332292399680819463179 324913998438599521229194769)
      ·
        refine ⟨243685498828949640921896077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324913998438599521229194769 243685498828949640921896077)
        ·
          refine ⟨91382062060856115345711029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243685498828949640921896077 91382062060856115345711029)
          ·
            refine ⟨8567068318205260813660409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91382062060856115345711029 8567068318205260813660409)
            ·
              refine ⟨6425301238653945610245307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8567068318205260813660409 6425301238653945610245307)
              ·
                refine ⟨9637951857980918415367961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6425301238653945610245307 9637951857980918415367961)
                ·
                  refine ⟨7228463893485688811525971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9637951857980918415367961 7228463893485688811525971)
                  ·
                    refine ⟨10842695840228533217288957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7228463893485688811525971 10842695840228533217288957)
                    ·
                      refine ⟨4066010940085699956483359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10842695840228533217288957 4066010940085699956483359)
                      ·
                        rfl

theorem cell23_7918528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_7918528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918528 prefixEnd_7918528 := by exact prefixLift 7918528
  have htrace : WordTrace (prefixWord ++ tailWord_7918528) baseStart_7918528 baseEnd_7918528 := by
    simpa [prefixWord, tailWord_7918528, baseEnd_7918528] using wordTrace_append hprefix tailTrace_7918528
  have hstable : (prefixWord ++ tailWord_7918528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918528).length < 2 ^ (prefixWord ++ tailWord_7918528).sum := by decide
  have hdescent : baseEnd_7918528 < baseStart_7918528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918604 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_7918604 : Nat := 118140960795 + 7918604 * 2 ^ 59
def prefixEnd_7918604 : Nat := 4983230072969 + 3 ^ 40 * 7918604 * 2
def baseEnd_7918604 : Nat := 1355349988205147219711003

theorem tailTrace_7918604 : CollatzResearch.WordTrace tailWord_7918604 prefixEnd_7918604 1355349988205147219711003 := by
  unfold tailWord_7918604
  simp only [CollatzResearch.WordTrace]
  refine ⟨144407607502128786369525433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192543476669505048492700577 144407607502128786369525433)
  ·
    refine ⟨108305705626596589777144075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144407607502128786369525433 108305705626596589777144075)
    ·
      refine ⟨162458558439894884665716113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108305705626596589777144075 162458558439894884665716113)
      ·
        refine ⟨121843918829921163499287085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162458558439894884665716113 121843918829921163499287085)
        ·
          refine ⟨45691469561220436312232657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121843918829921163499287085 45691469561220436312232657)
          ·
            refine ⟨34268602170915327234174493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45691469561220436312232657 34268602170915327234174493)
            ·
              refine ⟨12850725814093247712815435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34268602170915327234174493 12850725814093247712815435)
              ·
                refine ⟨19276088721139871569223153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12850725814093247712815435 19276088721139871569223153)
                ·
                  refine ⟨14457066540854903676917365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19276088721139871569223153 14457066540854903676917365)
                  ·
                    refine ⟨1355349988205147219711003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14457066540854903676917365 1355349988205147219711003)
                    ·
                      rfl

theorem cell23_7918604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_7918604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918604 prefixEnd_7918604 := by exact prefixLift 7918604
  have htrace : WordTrace (prefixWord ++ tailWord_7918604) baseStart_7918604 baseEnd_7918604 := by
    simpa [prefixWord, tailWord_7918604, baseEnd_7918604] using wordTrace_append hprefix tailTrace_7918604
  have hstable : (prefixWord ++ tailWord_7918604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918604).length < 2 ^ (prefixWord ++ tailWord_7918604).sum := by decide
  have hdescent : baseEnd_7918604 < baseStart_7918604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918607 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 4]
def baseStart_7918607 : Nat := 118140960795 + 7918607 * 2 ^ 59
def prefixEnd_7918607 : Nat := 4983230072969 + 3 ^ 40 * 7918607 * 2
def baseEnd_7918607 : Nat := 4066051505057405147395495

theorem tailTrace_7918607 : CollatzResearch.WordTrace tailWord_7918607 prefixEnd_7918607 4066051505057405147395495 := by
  unfold tailWord_7918607
  simp only [CollatzResearch.WordTrace]
  refine ⟨288815324423246704251410075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192543549615497802834273383 288815324423246704251410075)
  ·
    refine ⟨433222986634870056377115113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288815324423246704251410075 433222986634870056377115113)
    ·
      refine ⟨324917239976152542282836335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433222986634870056377115113 324917239976152542282836335)
      ·
        refine ⟨487375859964228813424254503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324917239976152542282836335 487375859964228813424254503)
        ·
          refine ⟨731063789946343220136381755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487375859964228813424254503 731063789946343220136381755)
          ·
            refine ⟨1096595684919514830204572633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731063789946343220136381755 1096595684919514830204572633)
            ·
              refine ⟨822446763689636122653429475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096595684919514830204572633 822446763689636122653429475)
              ·
                refine ⟨1233670145534454183980144213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822446763689636122653429475 1233670145534454183980144213)
                ·
                  refine ⟨14457072017981884968517315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1233670145534454183980144213 14457072017981884968517315)
                  ·
                    refine ⟨21685608026972827452775973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14457072017981884968517315 21685608026972827452775973)
                    ·
                      refine ⟨4066051505057405147395495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21685608026972827452775973 4066051505057405147395495)
                      ·
                        rfl

theorem cell23_7918607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_7918607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918607 prefixEnd_7918607 := by exact prefixLift 7918607
  have htrace : WordTrace (prefixWord ++ tailWord_7918607) baseStart_7918607 baseEnd_7918607 := by
    simpa [prefixWord, tailWord_7918607, baseEnd_7918607] using wordTrace_append hprefix tailTrace_7918607
  have hstable : (prefixWord ++ tailWord_7918607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918607).length < 2 ^ (prefixWord ++ tailWord_7918607).sum := by decide
  have hdescent : baseEnd_7918607 < baseStart_7918607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918685 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_7918685 : Nat := 118140960795 + 7918685 * 2 ^ 59
def prefixEnd_7918685 : Nat := 4983230072969 + 3 ^ 40 * 7918685 * 2
def baseEnd_7918685 : Nat := 1355363852182818614073379

theorem tailTrace_7918685 : CollatzResearch.WordTrace tailWord_7918685 prefixEnd_7918685 1355363852182818614073379 := by
  unfold tailWord_7918685
  simp only [CollatzResearch.WordTrace]
  refine ⟨288818169316964123572749509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192545446211309415715166339 288818169316964123572749509)
  ·
    refine ⟨54153406746930773169890533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288818169316964123572749509 54153406746930773169890533)
    ·
      refine ⟨10153763765049519969354475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54153406746930773169890533 10153763765049519969354475)
      ·
        refine ⟨15230645647574279954031713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10153763765049519969354475 15230645647574279954031713)
        ·
          refine ⟨11422984235680709965523785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15230645647574279954031713 11422984235680709965523785)
          ·
            refine ⟨8567238176760532474142839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11422984235680709965523785 8567238176760532474142839)
            ·
              refine ⟨12850857265140798711214259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8567238176760532474142839 12850857265140798711214259)
              ·
                refine ⟨19276285897711198066821389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12850857265140798711214259 19276285897711198066821389)
                ·
                  refine ⟨7228607211641699275058021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19276285897711198066821389 7228607211641699275058021)
                  ·
                    refine ⟨1355363852182818614073379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7228607211641699275058021 1355363852182818614073379)
                    ·
                      rfl

theorem cell23_7918685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_7918685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918685 prefixEnd_7918685 := by exact prefixLift 7918685
  have htrace : WordTrace (prefixWord ++ tailWord_7918685) baseStart_7918685 baseEnd_7918685 := by
    simpa [prefixWord, tailWord_7918685, baseEnd_7918685] using wordTrace_append hprefix tailTrace_7918685
  have hstable : (prefixWord ++ tailWord_7918685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918685).length < 2 ^ (prefixWord ++ tailWord_7918685).sum := by decide
  have hdescent : baseEnd_7918685 < baseStart_7918685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918698 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 6]
def baseStart_7918698 : Nat := 118140960795 + 7918698 * 2 ^ 59
def prefixEnd_7918698 : Nat := 4983230072969 + 3 ^ 40 * 7918698 * 2
def baseEnd_7918698 : Nat := 451788692421884921261953

theorem tailTrace_7918698 : CollatzResearch.WordTrace tailWord_7918698 prefixEnd_7918698 451788692421884921261953 := by
  unfold tailWord_7918698
  simp only [CollatzResearch.WordTrace]
  refine ⟨72204660866479256698243187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192545762310611351195315165 72204660866479256698243187)
  ·
    refine ⟨108306991299718885047364781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72204660866479256698243187 108306991299718885047364781)
    ·
      refine ⟨40615121737394581892761793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108306991299718885047364781 40615121737394581892761793)
      ·
        refine ⟨30461341303045936419571345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40615121737394581892761793 30461341303045936419571345)
        ·
          refine ⟨22846005977284452314678509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30461341303045936419571345 22846005977284452314678509)
          ·
            refine ⟨8567252241481669618004441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22846005977284452314678509 8567252241481669618004441)
            ·
              refine ⟨6425439181111252213503331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8567252241481669618004441 6425439181111252213503331)
              ·
                refine ⟨9638158771666878320254997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6425439181111252213503331 9638158771666878320254997)
                ·
                  refine ⟨451788692421884921261953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9638158771666878320254997 451788692421884921261953)
                  ·
                    rfl

theorem cell23_7918698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_7918698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918698 prefixEnd_7918698 := by exact prefixLift 7918698
  have htrace : WordTrace (prefixWord ++ tailWord_7918698) baseStart_7918698 baseEnd_7918698 := by
    simpa [prefixWord, tailWord_7918698, baseEnd_7918698] using wordTrace_append hprefix tailTrace_7918698
  have hstable : (prefixWord ++ tailWord_7918698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918698).length < 2 ^ (prefixWord ++ tailWord_7918698).sum := by decide
  have hdescent : baseEnd_7918698 < baseStart_7918698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918707 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 7, 6]
def baseStart_7918707 : Nat := 118140960795 + 7918707 * 2 ^ 59
def prefixEnd_7918707 : Nat := 4983230072969 + 3 ^ 40 * 7918707 * 2
def baseEnd_7918707 : Nat := 1355367617707618252048345

theorem tailTrace_7918707 : CollatzResearch.WordTrace tailWord_7918707 prefixEnd_7918707 1355367617707618252048345 := by
  unfold tailWord_7918707
  simp only [CollatzResearch.WordTrace]
  refine ⟨288818971722884421330050375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192545981148589614220033583 288818971722884421330050375)
  ·
    refine ⟨433228457584326631995075563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288818971722884421330050375 433228457584326631995075563)
    ·
      refine ⟨649842686376489947992613345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433228457584326631995075563 649842686376489947992613345)
      ·
        refine ⟨487382014782367460994460009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649842686376489947992613345 487382014782367460994460009)
        ·
          refine ⟨365536511086775595745845007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487382014782367460994460009 365536511086775595745845007)
          ·
            refine ⟨548304766630163393618767511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365536511086775595745845007 548304766630163393618767511)
            ·
              refine ⟨822457149945245090428151267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548304766630163393618767511 822457149945245090428151267)
              ·
                refine ⟨1233685724917867635642226901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822457149945245090428151267 1233685724917867635642226901)
                ·
                  refine ⟨28914509177762522710364693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1233685724917867635642226901 28914509177762522710364693)
                  ·
                    refine ⟨1355367617707618252048345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28914509177762522710364693 1355367617707618252048345)
                    ·
                      rfl

theorem cell23_7918707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 6].length) (baseStart_7918707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918707 prefixEnd_7918707 := by exact prefixLift 7918707
  have htrace : WordTrace (prefixWord ++ tailWord_7918707) baseStart_7918707 baseEnd_7918707 := by
    simpa [prefixWord, tailWord_7918707, baseEnd_7918707] using wordTrace_append hprefix tailTrace_7918707
  have hstable : (prefixWord ++ tailWord_7918707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918707).length < 2 ^ (prefixWord ++ tailWord_7918707).sum := by decide
  have hdescent : baseEnd_7918707 < baseStart_7918707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918724 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_7918724 : Nat := 118140960795 + 7918724 * 2 ^ 59
def prefixEnd_7918724 : Nat := 4983230072969 + 3 ^ 40 * 7918724 * 2
def baseEnd_7918724 : Nat := 1355370527431327063210819

theorem tailTrace_7918724 : CollatzResearch.WordTrace tailWord_7918724 prefixEnd_7918724 1355370527431327063210819 := by
  unfold tailWord_7918724
  simp only [CollatzResearch.WordTrace]
  refine ⟨144409795881911416616709613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192546394509215222155612817 144409795881911416616709613)
  ·
    refine ⟨54153673455716781231266105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144409795881911416616709613 54153673455716781231266105)
    ·
      refine ⟨40615255091787585923449579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54153673455716781231266105 40615255091787585923449579)
      ·
        refine ⟨60922882637681378885174369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40615255091787585923449579 60922882637681378885174369)
        ·
          refine ⟨45692161978261034163880777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60922882637681378885174369 45692161978261034163880777)
          ·
            refine ⟨34269121483695775622910583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45692161978261034163880777 34269121483695775622910583)
            ·
              refine ⟨51403682225543663434365875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34269121483695775622910583 51403682225543663434365875)
              ·
                refine ⟨77105523338315495151548813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51403682225543663434365875 77105523338315495151548813)
                ·
                  refine ⟨28914571251868310681830805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77105523338315495151548813 28914571251868310681830805)
                  ·
                    refine ⟨1355370527431327063210819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28914571251868310681830805 1355370527431327063210819)
                    ·
                      rfl

theorem cell23_7918724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_7918724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918724 prefixEnd_7918724 := by exact prefixLift 7918724
  have htrace : WordTrace (prefixWord ++ tailWord_7918724) baseStart_7918724 baseEnd_7918724 := by
    simpa [prefixWord, tailWord_7918724, baseEnd_7918724] using wordTrace_append hprefix tailTrace_7918724
  have hstable : (prefixWord ++ tailWord_7918724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918724).length < 2 ^ (prefixWord ++ tailWord_7918724).sum := by decide
  have hdescent : baseEnd_7918724 < baseStart_7918724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918747 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 7]
def baseStart_7918747 : Nat := 118140960795 + 7918747 * 2 ^ 59
def prefixEnd_7918747 : Nat := 4983230072969 + 3 ^ 40 * 7918747 * 2
def baseEnd_7918747 : Nat := 4066123392349034599644851

theorem tailTrace_7918747 : CollatzResearch.WordTrace tailWord_7918747 prefixEnd_7918747 4066123392349034599644851 := by
  unfold tailWord_7918747
  simp only [CollatzResearch.WordTrace]
  refine ⟨288820430642739508161506495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192546953761826338774337663 288820430642739508161506495)
  ·
    refine ⟨433230645964109262242259743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288820430642739508161506495 433230645964109262242259743)
    ·
      refine ⟨649845968946163893363389615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433230645964109262242259743 649845968946163893363389615)
      ·
        refine ⟨974768953419245840045084423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649845968946163893363389615 974768953419245840045084423)
        ·
          refine ⟨1462153430128868760067626635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974768953419245840045084423 1462153430128868760067626635)
          ·
            refine ⟨2193230145193303140101439953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462153430128868760067626635 2193230145193303140101439953)
            ·
              refine ⟨1644922608894977355076079965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193230145193303140101439953 1644922608894977355076079965)
              ·
                refine ⟨616845978335616508153529987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1644922608894977355076079965 616845978335616508153529987)
                ·
                  refine ⟨925268967503424762230294981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616845978335616508153529987 925268967503424762230294981)
                  ·
                    refine ⟨173487931406892142918180309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 925268967503424762230294981 173487931406892142918180309)
                    ·
                      refine ⟨4066123392349034599644851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173487931406892142918180309 4066123392349034599644851)
                      ·
                        rfl

theorem cell23_7918747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_7918747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918747 prefixEnd_7918747 := by exact prefixLift 7918747
  have htrace : WordTrace (prefixWord ++ tailWord_7918747) baseStart_7918747 baseEnd_7918747 := by
    simpa [prefixWord, tailWord_7918747, baseEnd_7918747] using wordTrace_append hprefix tailTrace_7918747
  have hstable : (prefixWord ++ tailWord_7918747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918747).length < 2 ^ (prefixWord ++ tailWord_7918747).sum := by decide
  have hdescent : baseEnd_7918747 < baseStart_7918747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918781 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_7918781 : Nat := 118140960795 + 7918781 * 2 ^ 59
def prefixEnd_7918781 : Nat := 4983230072969 + 3 ^ 40 * 7918781 * 2
def baseEnd_7918781 : Nat := 4066140850691287466619695

theorem tailTrace_7918781 : CollatzResearch.WordTrace tailWord_7918781 prefixEnd_7918781 4066140850691287466619695 := by
  unfold tailWord_7918781
  simp only [CollatzResearch.WordTrace]
  refine ⟨288821670724616331968244197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192547780483077554645496131 288821670724616331968244197)
  ·
    refine ⟨54154063260865562244045787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288821670724616331968244197 54154063260865562244045787)
    ·
      refine ⟨81231094891298343366068681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54154063260865562244045787 81231094891298343366068681)
      ·
        refine ⟨60923321168473757524551511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81231094891298343366068681 60923321168473757524551511)
        ·
          refine ⟨91384981752710636286827267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60923321168473757524551511 91384981752710636286827267)
          ·
            refine ⟨137077472629065954430240901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91384981752710636286827267 137077472629065954430240901)
            ·
              refine ⟨25702026117949866455670169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137077472629065954430240901 25702026117949866455670169)
              ·
                refine ⟨19276519588462399841752627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25702026117949866455670169 19276519588462399841752627)
                ·
                  refine ⟨28914779382693599762628941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19276519588462399841752627 28914779382693599762628941)
                  ·
                    refine ⟨10843042268510099910985853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28914779382693599762628941 10843042268510099910985853)
                    ·
                      refine ⟨4066140850691287466619695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843042268510099910985853 4066140850691287466619695)
                      ·
                        rfl

theorem cell23_7918781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_7918781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918781 prefixEnd_7918781 := by exact prefixLift 7918781
  have htrace : WordTrace (prefixWord ++ tailWord_7918781) baseStart_7918781 baseEnd_7918781 := by
    simpa [prefixWord, tailWord_7918781, baseEnd_7918781] using wordTrace_append hprefix tailTrace_7918781
  have hstable : (prefixWord ++ tailWord_7918781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918781).length < 2 ^ (prefixWord ++ tailWord_7918781).sum := by decide
  have hdescent : baseEnd_7918781 < baseStart_7918781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918782 : List Nat := [4, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_7918782 : Nat := 118140960795 + 7918782 * 2 ^ 59
def prefixEnd_7918782 : Nat := 4983230072969 + 3 ^ 40 * 7918782 * 2
def baseEnd_7918782 : Nat := 4066141364171941962707191

theorem tailTrace_7918782 : CollatzResearch.WordTrace tailWord_7918782 prefixEnd_7918782 4066141364171941962707191 := by
  unfold tailWord_7918782
  simp only [CollatzResearch.WordTrace]
  refine ⟨36102713399701588642378825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192547804798408472759353733 36102713399701588642378825)
  ·
    refine ⟨27077035049776191481784119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36102713399701588642378825 27077035049776191481784119)
    ·
      refine ⟨40615552574664287222676179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27077035049776191481784119 40615552574664287222676179)
      ·
        refine ⟨60923328861996430834014269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40615552574664287222676179 60923328861996430834014269)
        ·
          refine ⟨22846248323248661562755351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60923328861996430834014269 22846248323248661562755351)
          ·
            refine ⟨34269372484872992344133027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22846248323248661562755351 34269372484872992344133027)
            ·
              refine ⟨51404058727309488516199541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34269372484872992344133027 51404058727309488516199541)
              ·
                refine ⟨4819130505685264548393707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51404058727309488516199541 4819130505685264548393707)
                ·
                  refine ⟨7228695758527896822590561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4819130505685264548393707 7228695758527896822590561)
                  ·
                    refine ⟨5421521818895922616942921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7228695758527896822590561 5421521818895922616942921)
                    ·
                      refine ⟨4066141364171941962707191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421521818895922616942921 4066141364171941962707191)
                      ·
                        rfl

theorem cell23_7918782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_7918782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918782 prefixEnd_7918782 := by exact prefixLift 7918782
  have htrace : WordTrace (prefixWord ++ tailWord_7918782) baseStart_7918782 baseEnd_7918782 := by
    simpa [prefixWord, tailWord_7918782, baseEnd_7918782] using wordTrace_append hprefix tailTrace_7918782
  have hstable : (prefixWord ++ tailWord_7918782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918782).length < 2 ^ (prefixWord ++ tailWord_7918782).sum := by decide
  have hdescent : baseEnd_7918782 < baseStart_7918782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918785 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_7918785 : Nat := 118140960795 + 7918785 * 2 ^ 59
def prefixEnd_7918785 : Nat := 4983230072969 + 3 ^ 40 * 7918785 * 2
def baseEnd_7918785 : Nat := 4066142904613905450969677

theorem tailTrace_7918785 : CollatzResearch.WordTrace tailWord_7918785 prefixEnd_7918785 4066142904613905450969677 := by
  unfold tailWord_7918785
  simp only [CollatzResearch.WordTrace]
  refine ⟨288821816616601840651389809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192547877744401227100926539 288821816616601840651389809)
  ·
    refine ⟨216616362462451380488542357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288821816616601840651389809 216616362462451380488542357)
    ·
      refine ⟨10153891990427408460400423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 216616362462451380488542357 10153891990427408460400423)
      ·
        refine ⟨15230837985641112690600635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10153891990427408460400423 15230837985641112690600635)
        ·
          refine ⟨22846256978461669035900953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15230837985641112690600635 22846256978461669035900953)
          ·
            refine ⟨17134692733846251776925715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22846256978461669035900953 17134692733846251776925715)
            ·
              refine ⟨25702039100769377665388573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17134692733846251776925715 25702039100769377665388573)
              ·
                refine ⟨9638264662788516624520715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25702039100769377665388573 9638264662788516624520715)
                ·
                  refine ⟨14457396994182774936781073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9638264662788516624520715 14457396994182774936781073)
                  ·
                    refine ⟨10843047745637081202585805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14457396994182774936781073 10843047745637081202585805)
                    ·
                      refine ⟨4066142904613905450969677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843047745637081202585805 4066142904613905450969677)
                      ·
                        rfl

theorem cell23_7918785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_7918785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918785 prefixEnd_7918785 := by exact prefixLift 7918785
  have htrace : WordTrace (prefixWord ++ tailWord_7918785) baseStart_7918785 baseEnd_7918785 := by
    simpa [prefixWord, tailWord_7918785, baseEnd_7918785] using wordTrace_append hprefix tailTrace_7918785
  have hstable : (prefixWord ++ tailWord_7918785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918785).length < 2 ^ (prefixWord ++ tailWord_7918785).sum := by decide
  have hdescent : baseEnd_7918785 < baseStart_7918785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918838 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_7918838 : Nat := 118140960795 + 7918838 * 2 ^ 59
def prefixEnd_7918838 : Nat := 4983230072969 + 3 ^ 40 * 7918838 * 2
def baseEnd_7918838 : Nat := 4066170119088593743606933

theorem tailTrace_7918838 : CollatzResearch.WordTrace tailWord_7918838 prefixEnd_7918838 4066170119088593743606933 := by
  unfold tailWord_7918838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18051484355338114418941823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192549166456939887135379445 18051484355338114418941823)
  ·
    refine ⟨27077226533007171628412735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18051484355338114418941823 27077226533007171628412735)
    ·
      refine ⟨40615839799510757442619103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27077226533007171628412735 40615839799510757442619103)
      ·
        refine ⟨60923759699266136163928655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40615839799510757442619103 60923759699266136163928655)
        ·
          refine ⟨91385639548899204245892983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60923759699266136163928655 91385639548899204245892983)
          ·
            refine ⟨137078459323348806368839475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91385639548899204245892983 137078459323348806368839475)
            ·
              refine ⟨205617688985023209553259213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137078459323348806368839475 205617688985023209553259213)
              ·
                refine ⟨77106633369383703582472205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205617688985023209553259213 77106633369383703582472205)
                ·
                  refine ⟨28914987513518888843427077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77106633369383703582472205 28914987513518888843427077)
                  ·
                    refine ⟨5421560158784791658142577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28914987513518888843427077 5421560158784791658142577)
                    ·
                      refine ⟨4066170119088593743606933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421560158784791658142577 4066170119088593743606933)
                      ·
                        rfl

theorem cell23_7918838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_7918838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918838 prefixEnd_7918838 := by exact prefixLift 7918838
  have htrace : WordTrace (prefixWord ++ tailWord_7918838) baseStart_7918838 baseEnd_7918838 := by
    simpa [prefixWord, tailWord_7918838, baseEnd_7918838] using wordTrace_append hprefix tailTrace_7918838
  have hstable : (prefixWord ++ tailWord_7918838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918838).length < 2 ^ (prefixWord ++ tailWord_7918838).sum := by decide
  have hdescent : baseEnd_7918838 < baseStart_7918838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918866 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7918866 : Nat := 118140960795 + 7918866 * 2 ^ 59
def prefixEnd_7918866 : Nat := 4983230072969 + 3 ^ 40 * 7918866 * 2
def baseEnd_7918866 : Nat := 4066184496546919634056805

theorem tailTrace_7918866 : CollatzResearch.WordTrace tailWord_7918866 prefixEnd_7918866 4066184496546919634056805 := by
  unfold tailWord_7918866
  simp only [CollatzResearch.WordTrace]
  refine ⟨72206192732327097871272113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192549847286205594323392301 72206192732327097871272113)
  ·
    refine ⟨54154644549245323403454085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72206192732327097871272113 54154644549245323403454085)
    ·
      refine ⟨10153995852983498138147641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54154644549245323403454085 10153995852983498138147641)
      ·
        refine ⟨7615496889737623603610731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10153995852983498138147641 7615496889737623603610731)
        ·
          refine ⟨11423245334606435405416097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7615496889737623603610731 11423245334606435405416097)
          ·
            refine ⟨8567434000954826554062073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11423245334606435405416097 8567434000954826554062073)
            ·
              refine ⟨6425575500716119915546555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8567434000954826554062073 6425575500716119915546555)
              ·
                refine ⟨9638363251074179873319833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6425575500716119915546555 9638363251074179873319833)
                ·
                  refine ⟨7228772438305634904989875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9638363251074179873319833 7228772438305634904989875)
                  ·
                    refine ⟨10843158657458452357484813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7228772438305634904989875 10843158657458452357484813)
                    ·
                      refine ⟨4066184496546919634056805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843158657458452357484813 4066184496546919634056805)
                      ·
                        rfl

theorem cell23_7918866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7918866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918866 prefixEnd_7918866 := by exact prefixLift 7918866
  have htrace : WordTrace (prefixWord ++ tailWord_7918866) baseStart_7918866 baseEnd_7918866 := by
    simpa [prefixWord, tailWord_7918866, baseEnd_7918866] using wordTrace_append hprefix tailTrace_7918866
  have hstable : (prefixWord ++ tailWord_7918866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918866).length < 2 ^ (prefixWord ++ tailWord_7918866).sum := by decide
  have hdescent : baseEnd_7918866 < baseStart_7918866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918871 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 3]
def baseStart_7918871 : Nat := 118140960795 + 7918871 * 2 ^ 59
def prefixEnd_7918871 : Nat := 4983230072969 + 3 ^ 40 * 7918871 * 2
def baseEnd_7918871 : Nat := 4066187063950192114494281

theorem tailTrace_7918871 : CollatzResearch.WordTrace tailWord_7918871 prefixEnd_7918871 4066187063950192114494281 := by
  unfold tailWord_7918871
  simp only [CollatzResearch.WordTrace]
  refine ⟨288824953294290277339020467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192549968862860184892680311 288824953294290277339020467)
  ·
    refine ⟨433237429941435416008530701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288824953294290277339020467 433237429941435416008530701)
    ·
      refine ⟨162464036228038281003199013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433237429941435416008530701 162464036228038281003199013)
      ·
        refine ⟨30462006792757177688099815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162464036228038281003199013 30462006792757177688099815)
        ·
          refine ⟨45693010189135766532149723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30462006792757177688099815 45693010189135766532149723)
          ·
            refine ⟨68539515283703649798224585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45693010189135766532149723 68539515283703649798224585)
            ·
              refine ⟨51404636462777737348668439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68539515283703649798224585 51404636462777737348668439)
              ·
                refine ⟨77106954694166606023002659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51404636462777737348668439 77106954694166606023002659)
                ·
                  refine ⟨115660432041249909034503989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77106954694166606023002659 115660432041249909034503989)
                  ·
                    refine ⟨10843165503867178971984749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115660432041249909034503989 10843165503867178971984749)
                    ·
                      refine ⟨4066187063950192114494281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843165503867178971984749 4066187063950192114494281)
                      ·
                        rfl

theorem cell23_7918871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_7918871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918871 prefixEnd_7918871 := by exact prefixLift 7918871
  have htrace : WordTrace (prefixWord ++ tailWord_7918871) baseStart_7918871 baseEnd_7918871 := by
    simpa [prefixWord, tailWord_7918871, baseEnd_7918871] using wordTrace_append hprefix tailTrace_7918871
  have hstable : (prefixWord ++ tailWord_7918871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918871).length < 2 ^ (prefixWord ++ tailWord_7918871).sum := by decide
  have hdescent : baseEnd_7918871 < baseStart_7918871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918872 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 2, 2, 2]
def baseStart_7918872 : Nat := 118140960795 + 7918872 * 2 ^ 59
def prefixEnd_7918872 : Nat := 4983230072969 + 3 ^ 40 * 7918872 * 2
def baseEnd_7918872 : Nat := 4066187577430846610581777

theorem tailTrace_7918872 : CollatzResearch.WordTrace tailWord_7918872 prefixEnd_7918872 4066187577430846610581777 := by
  unfold tailWord_7918872
  simp only [CollatzResearch.WordTrace]
  refine ⟨144412494883643327254903435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192549993178191103006537913 144412494883643327254903435)
  ·
    refine ⟨216618742325464990882355153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144412494883643327254903435 216618742325464990882355153)
    ·
      refine ⟨162464056744098743161766365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216618742325464990882355153 162464056744098743161766365)
      ·
        refine ⟨60924021279037028685662387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162464056744098743161766365 60924021279037028685662387)
        ·
          refine ⟨91386031918555543028493581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60924021279037028685662387 91386031918555543028493581)
          ·
            refine ⟨34269761969458328635685093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91386031918555543028493581 34269761969458328635685093)
            ·
              refine ⟨6425580369273436619190955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34269761969458328635685093 6425580369273436619190955)
              ·
                refine ⟨9638370553910154928786433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6425580369273436619190955 9638370553910154928786433)
                ·
                  refine ⟨7228777915432616196589825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9638370553910154928786433 7228777915432616196589825)
                  ·
                    refine ⟨5421583436574462147442369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7228777915432616196589825 5421583436574462147442369)
                    ·
                      refine ⟨4066187577430846610581777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421583436574462147442369 4066187577430846610581777)
                      ·
                        rfl

theorem cell23_7918872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_7918872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918872 prefixEnd_7918872 := by exact prefixLift 7918872
  have htrace : WordTrace (prefixWord ++ tailWord_7918872) baseStart_7918872 baseEnd_7918872 := by
    simpa [prefixWord, tailWord_7918872, baseEnd_7918872] using wordTrace_append hprefix tailTrace_7918872
  have hstable : (prefixWord ++ tailWord_7918872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918872).length < 2 ^ (prefixWord ++ tailWord_7918872).sum := by decide
  have hdescent : baseEnd_7918872 < baseStart_7918872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918901 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_7918901 : Nat := 118140960795 + 7918901 * 2 ^ 59
def prefixEnd_7918901 : Nat := 4983230072969 + 3 ^ 40 * 7918901 * 2
def baseEnd_7918901 : Nat := 4066202468369826997119143

theorem tailTrace_7918901 : CollatzResearch.WordTrace tailWord_7918901 prefixEnd_7918901 4066202468369826997119143 := by
  unfold tailWord_7918901
  simp only [CollatzResearch.WordTrace]
  refine ⟨288826047484181592462612557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192550698322787728308408371 288826047484181592462612557)
  ·
    refine ⟨108309767806568097173479709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288826047484181592462612557 108309767806568097173479709)
    ·
      refine ⟨40616162927463036440054891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108309767806568097173479709 40616162927463036440054891)
      ·
        refine ⟨60924244391194554660082337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40616162927463036440054891 60924244391194554660082337)
        ·
          refine ⟨45693183293395915995061753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60924244391194554660082337 45693183293395915995061753)
          ·
            refine ⟨34269887470046936996296315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45693183293395915995061753 34269887470046936996296315)
            ·
              refine ⟨51404831205070405494444473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34269887470046936996296315 51404831205070405494444473)
              ·
                refine ⟨38553623403802804120833355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51404831205070405494444473 38553623403802804120833355)
                ·
                  refine ⟨57830435105704206181250033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38553623403802804120833355 57830435105704206181250033)
                  ·
                    refine ⟨43372826329278154635937525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57830435105704206181250033 43372826329278154635937525)
                    ·
                      refine ⟨4066202468369826997119143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43372826329278154635937525 4066202468369826997119143)
                      ·
                        rfl

theorem cell23_7918901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_7918901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918901 prefixEnd_7918901 := by exact prefixLift 7918901
  have htrace : WordTrace (prefixWord ++ tailWord_7918901) baseStart_7918901 baseEnd_7918901 := by
    simpa [prefixWord, tailWord_7918901, baseEnd_7918901] using wordTrace_append hprefix tailTrace_7918901
  have hstable : (prefixWord ++ tailWord_7918901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918901).length < 2 ^ (prefixWord ++ tailWord_7918901).sum := by decide
  have hdescent : baseEnd_7918901 < baseStart_7918901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918928 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 2, 4, 2]
def baseStart_7918928 : Nat := 118140960795 + 7918928 * 2 ^ 59
def prefixEnd_7918928 : Nat := 4983230072969 + 3 ^ 40 * 7918928 * 2
def baseEnd_7918928 : Nat := 4066216332347498391481519

theorem tailTrace_7918928 : CollatzResearch.WordTrace tailWord_7918928 prefixEnd_7918928 4066216332347498391481519 := by
  unfold tailWord_7918928
  simp only [CollatzResearch.WordTrace]
  refine ⟨144413516127541888036922719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192551354836722517382563625 144413516127541888036922719)
  ·
    refine ⟨216620274191312832055384079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144413516127541888036922719 216620274191312832055384079)
    ·
      refine ⟨324930411286969248083076119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216620274191312832055384079 324930411286969248083076119)
      ·
        refine ⟨487395616930453872124614179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324930411286969248083076119 487395616930453872124614179)
        ·
          refine ⟨731093425395680808186921269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487395616930453872124614179 731093425395680808186921269)
          ·
            refine ⟨68540008630845075767523869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 731093425395680808186921269 68540008630845075767523869)
            ·
              refine ⟨25702503236566903412821451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68540008630845075767523869 25702503236566903412821451)
              ·
                refine ⟨38553754854850355119232177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25702503236566903412821451 38553754854850355119232177)
                ·
                  refine ⟨28915316141137766339424133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38553754854850355119232177 28915316141137766339424133)
                  ·
                    refine ⟨5421621776463331188642025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28915316141137766339424133 5421621776463331188642025)
                    ·
                      refine ⟨4066216332347498391481519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421621776463331188642025 4066216332347498391481519)
                      ·
                        rfl

theorem cell23_7918928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 4, 2].length) (baseStart_7918928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918928 prefixEnd_7918928 := by exact prefixLift 7918928
  have htrace : WordTrace (prefixWord ++ tailWord_7918928) baseStart_7918928 baseEnd_7918928 := by
    simpa [prefixWord, tailWord_7918928, baseEnd_7918928] using wordTrace_append hprefix tailTrace_7918928
  have hstable : (prefixWord ++ tailWord_7918928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918928).length < 2 ^ (prefixWord ++ tailWord_7918928).sum := by decide
  have hdescent : baseEnd_7918928 < baseStart_7918928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918931 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 3]
def baseStart_7918931 : Nat := 118140960795 + 7918931 * 2 ^ 59
def prefixEnd_7918931 : Nat := 4983230072969 + 3 ^ 40 * 7918931 * 2
def baseEnd_7918931 : Nat := 4066217872789461879744005

theorem tailTrace_7918931 : CollatzResearch.WordTrace tailWord_7918931 prefixEnd_7918931 4066217872789461879744005 := by
  unfold tailWord_7918931
  simp only [CollatzResearch.WordTrace]
  refine ⟨288827141674072907586204647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192551427782715271724136431 288827141674072907586204647)
  ·
    refine ⟨433240712511109361379306971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288827141674072907586204647 433240712511109361379306971)
    ·
      refine ⟨649861068766664042068960457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433240712511109361379306971 649861068766664042068960457)
      ·
        refine ⟨487395801574998031551720343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649861068766664042068960457 487395801574998031551720343)
        ·
          refine ⟨731093702362497047327580515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487395801574998031551720343 731093702362497047327580515)
          ·
            refine ⟨1096640553543745570991370773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731093702362497047327580515 1096640553543745570991370773)
            ·
              refine ⟨51405025947363073640220505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1096640553543745570991370773 51405025947363073640220505)
              ·
                refine ⟨38553769460522305230165379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51405025947363073640220505 38553769460522305230165379)
                ·
                  refine ⟨57830654190783457845248069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38553769460522305230165379 57830654190783457845248069)
                  ·
                    refine ⟨10843247660771898345984013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57830654190783457845248069 10843247660771898345984013)
                    ·
                      refine ⟨4066217872789461879744005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843247660771898345984013 4066217872789461879744005)
                      ·
                        rfl

theorem cell23_7918931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 3].length) (baseStart_7918931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918931 prefixEnd_7918931 := by exact prefixLift 7918931
  have htrace : WordTrace (prefixWord ++ tailWord_7918931) baseStart_7918931 baseEnd_7918931 := by
    simpa [prefixWord, tailWord_7918931, baseEnd_7918931] using wordTrace_append hprefix tailTrace_7918931
  have hstable : (prefixWord ++ tailWord_7918931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918931).length < 2 ^ (prefixWord ++ tailWord_7918931).sum := by decide
  have hdescent : baseEnd_7918931 < baseStart_7918931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918948 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_7918948 : Nat := 118140960795 + 7918948 * 2 ^ 59
def prefixEnd_7918948 : Nat := 4983230072969 + 3 ^ 40 * 7918948 * 2
def baseEnd_7918948 : Nat := 4066226601960588313231427

theorem tailTrace_7918948 : CollatzResearch.WordTrace tailWord_7918948 prefixEnd_7918948 4066226601960588313231427 := by
  unfold tailWord_7918948
  simp only [CollatzResearch.WordTrace]
  refine ⟨144413880857505659744786749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192551841143340879659715665 144413880857505659744786749)
  ·
    refine ⟨54155205321564622404295031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144413880857505659744786749 54155205321564622404295031)
    ·
      refine ⟨81232807982346933606442547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54155205321564622404295031 81232807982346933606442547)
      ·
        refine ⟨121849211973520400409663821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81232807982346933606442547 121849211973520400409663821)
        ·
          refine ⟨45693454490070150153623933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121849211973520400409663821 45693454490070150153623933)
          ·
            refine ⟨17135045433776306307608975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45693454490070150153623933 17135045433776306307608975)
            ·
              refine ⟨25702568150664459461413463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17135045433776306307608975 25702568150664459461413463)
              ·
                refine ⟨38553852225996689192120195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25702568150664459461413463 38553852225996689192120195)
                ·
                  refine ⟨57830778338995033788180293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38553852225996689192120195 57830778338995033788180293)
                  ·
                    refine ⟨10843270938561568835283805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57830778338995033788180293 10843270938561568835283805)
                    ·
                      refine ⟨4066226601960588313231427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843270938561568835283805 4066226601960588313231427)
                      ·
                        rfl

theorem cell23_7918948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_7918948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918948 prefixEnd_7918948 := by exact prefixLift 7918948
  have htrace : WordTrace (prefixWord ++ tailWord_7918948) baseStart_7918948 baseEnd_7918948 := by
    simpa [prefixWord, tailWord_7918948, baseEnd_7918948] using wordTrace_append hprefix tailTrace_7918948
  have hstable : (prefixWord ++ tailWord_7918948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918948).length < 2 ^ (prefixWord ++ tailWord_7918948).sum := by decide
  have hdescent : baseEnd_7918948 < baseStart_7918948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918981 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_7918981 : Nat := 118140960795 + 7918981 * 2 ^ 59
def prefixEnd_7918981 : Nat := 4983230072969 + 3 ^ 40 * 7918981 * 2
def baseEnd_7918981 : Nat := 1355414515607395561372925

theorem tailTrace_7918981 : CollatzResearch.WordTrace tailWord_7918981 prefixEnd_7918981 1355414515607395561372925 := by
  unfold tailWord_7918981
  simp only [CollatzResearch.WordTrace]
  refine ⟨288828965323891766125524797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192552643549261177417016531 288828965323891766125524797)
  ·
    refine ⟨108310861996459412297071799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288828965323891766125524797 108310861996459412297071799)
    ·
      refine ⟨162466292994689118445607699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108310861996459412297071799 162466292994689118445607699)
      ·
        refine ⟨243699439492033677668411549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162466292994689118445607699 243699439492033677668411549)
        ·
          refine ⟨91387289809512629125654331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243699439492033677668411549 91387289809512629125654331)
          ·
            refine ⟨137080934714268943688481497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91387289809512629125654331 137080934714268943688481497)
            ·
              refine ⟨102810701035701707766361123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137080934714268943688481497 102810701035701707766361123)
              ·
                refine ⟨154216051553552561649541685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102810701035701707766361123 154216051553552561649541685)
                ·
                  refine ⟨14457754833145552654644533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154216051553552561649541685 14457754833145552654644533)
                  ·
                    refine ⟨1355414515607395561372925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14457754833145552654644533 1355414515607395561372925)
                    ·
                      rfl

theorem cell23_7918981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_7918981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918981 prefixEnd_7918981 := by exact prefixLift 7918981
  have htrace : WordTrace (prefixWord ++ tailWord_7918981) baseStart_7918981 baseEnd_7918981 := by
    simpa [prefixWord, tailWord_7918981, baseEnd_7918981] using wordTrace_append hprefix tailTrace_7918981
  have hstable : (prefixWord ++ tailWord_7918981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918981).length < 2 ^ (prefixWord ++ tailWord_7918981).sum := by decide
  have hdescent : baseEnd_7918981 < baseStart_7918981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918985 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 6]
def baseStart_7918985 : Nat := 118140960795 + 7918985 * 2 ^ 59
def prefixEnd_7918985 : Nat := 4983230072969 + 3 ^ 40 * 7918985 * 2
def baseEnd_7918985 : Nat := 451805066749422740940973

theorem tailTrace_7918985 : CollatzResearch.WordTrace tailWord_7918985 prefixEnd_7918985 451805066749422740940973 := by
  unfold tailWord_7918985
  simp only [CollatzResearch.WordTrace]
  refine ⟨288829111215877274808670409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192552740810584849872446939 288829111215877274808670409)
  ·
    refine ⟨216621833411907956106502807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288829111215877274808670409 216621833411907956106502807)
    ·
      refine ⟨324932750117861934159754211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216621833411907956106502807 324932750117861934159754211)
      ·
        refine ⟨487399125176792901239631317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324932750117861934159754211 487399125176792901239631317)
        ·
          refine ⟨11423416996331083622803859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 487399125176792901239631317 11423416996331083622803859)
          ·
            refine ⟨17135125494496625434205789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11423416996331083622803859 17135125494496625434205789)
            ·
              refine ⟨6425672060436234537827171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17135125494496625434205789 6425672060436234537827171)
              ·
                refine ⟨9638508090654351806740757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6425672060436234537827171 9638508090654351806740757)
                ·
                  refine ⟨451805066749422740940973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9638508090654351806740757 451805066749422740940973)
                  ·
                    rfl

theorem cell23_7918985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 6].length) (baseStart_7918985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918985 prefixEnd_7918985 := by exact prefixLift 7918985
  have htrace : WordTrace (prefixWord ++ tailWord_7918985) baseStart_7918985 baseEnd_7918985 := by
    simpa [prefixWord, tailWord_7918985, baseEnd_7918985] using wordTrace_append hprefix tailTrace_7918985
  have hstable : (prefixWord ++ tailWord_7918985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918985).length < 2 ^ (prefixWord ++ tailWord_7918985).sum := by decide
  have hdescent : baseEnd_7918985 < baseStart_7918985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918988 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 3, 5, 2]
def baseStart_7918988 : Nat := 118140960795 + 7918988 * 2 ^ 59
def prefixEnd_7918988 : Nat := 4983230072969 + 3 ^ 40 * 7918988 * 2
def baseEnd_7918988 : Nat := 4066247141186768156731243

theorem tailTrace_7918988 : CollatzResearch.WordTrace tailWord_7918988 prefixEnd_7918988 4066247141186768156731243 := by
  unfold tailWord_7918988
  simp only [CollatzResearch.WordTrace]
  refine ⟨144414610317433203160514809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192552813756577604214019745 144414610317433203160514809)
  ·
    refine ⟨108310957738074902370386107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144414610317433203160514809 108310957738074902370386107)
    ·
      refine ⟨162466436607112353555579161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108310957738074902370386107 162466436607112353555579161)
      ·
        refine ⟨121849827455334265166684371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162466436607112353555579161 121849827455334265166684371)
        ·
          refine ⟨182774741183001397750026557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121849827455334265166684371 182774741183001397750026557)
          ·
            refine ⟨68540527943625524156259959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182774741183001397750026557 68540527943625524156259959)
            ·
              refine ⟨102810791915438286234389939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68540527943625524156259959 102810791915438286234389939)
              ·
                refine ⟨154216187873157429351584909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102810791915438286234389939 154216187873157429351584909)
                ·
                  refine ⟨57831070452434036006844341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154216187873157429351584909 57831070452434036006844341)
                  ·
                    refine ⟨5421662854915690875641657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57831070452434036006844341 5421662854915690875641657)
                    ·
                      refine ⟨4066247141186768156731243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421662854915690875641657 4066247141186768156731243)
                      ·
                        rfl

theorem cell23_7918988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_7918988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918988 prefixEnd_7918988 := by exact prefixLift 7918988
  have htrace : WordTrace (prefixWord ++ tailWord_7918988) baseStart_7918988 baseEnd_7918988 := by
    simpa [prefixWord, tailWord_7918988, baseEnd_7918988] using wordTrace_append hprefix tailTrace_7918988
  have hstable : (prefixWord ++ tailWord_7918988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918988).length < 2 ^ (prefixWord ++ tailWord_7918988).sum := by decide
  have hdescent : baseEnd_7918988 < baseStart_7918988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919005 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_7919005 : Nat := 118140960795 + 7919005 * 2 ^ 59
def prefixEnd_7919005 : Nat := 4983230072969 + 3 ^ 40 * 7919005 * 2
def baseEnd_7919005 : Nat := 4066255870357894590218665

theorem tailTrace_7919005 : CollatzResearch.WordTrace tailWord_7919005 prefixEnd_7919005 4066255870357894590218665 := by
  unfold tailWord_7919005
  simp only [CollatzResearch.WordTrace]
  refine ⟨288829840675804818224398469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192553227117203212149598979 288829840675804818224398469)
  ·
    refine ⟨54155595126713403417074713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288829840675804818224398469 54155595126713403417074713)
    ·
      refine ⟨40616696345035052562806035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54155595126713403417074713 40616696345035052562806035)
      ·
        refine ⟨60925044517552578844209053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40616696345035052562806035 60925044517552578844209053)
        ·
          refine ⟨22846891694082217066578395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60925044517552578844209053 22846891694082217066578395)
          ·
            refine ⟨34270337541123325599867593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22846891694082217066578395 34270337541123325599867593)
            ·
              refine ⟨25702753155842494199900695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34270337541123325599867593 25702753155842494199900695)
              ·
                refine ⟨38554129733763741299851043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25702753155842494199900695 38554129733763741299851043)
                ·
                  refine ⟨57831194600645611949776565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38554129733763741299851043 57831194600645611949776565)
                  ·
                    refine ⟨5421674493810526120291553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57831194600645611949776565 5421674493810526120291553)
                    ·
                      refine ⟨4066255870357894590218665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421674493810526120291553 4066255870357894590218665)
                      ·
                        rfl

theorem cell23_7919005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_7919005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919005 prefixEnd_7919005 := by exact prefixLift 7919005
  have htrace : WordTrace (prefixWord ++ tailWord_7919005) baseStart_7919005 baseEnd_7919005 := by
    simpa [prefixWord, tailWord_7919005, baseEnd_7919005] using wordTrace_append hprefix tailTrace_7919005
  have hstable : (prefixWord ++ tailWord_7919005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919005).length < 2 ^ (prefixWord ++ tailWord_7919005).sum := by decide
  have hdescent : baseEnd_7919005 < baseStart_7919005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919006 : List Nat := [4, 3, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_7919006 : Nat := 118140960795 + 7919006 * 2 ^ 59
def prefixEnd_7919006 : Nat := 4983230072969 + 3 ^ 40 * 7919006 * 2
def baseEnd_7919006 : Nat := 1355418794612849695435387

theorem tailTrace_7919006 : CollatzResearch.WordTrace tailWord_7919006 prefixEnd_7919006 1355418794612849695435387 := by
  unfold tailWord_7919006
  simp only [CollatzResearch.WordTrace]
  refine ⟨36103734643600149424398109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192553251432534130263456581 36103734643600149424398109)
  ·
    refine ⟨13538900491350056034149291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36103734643600149424398109 13538900491350056034149291)
    ·
      refine ⟨20308350737025084051223937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13538900491350056034149291 20308350737025084051223937)
      ·
        refine ⟨15231263052768813038417953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20308350737025084051223937 15231263052768813038417953)
        ·
          refine ⟨11423447289576609778813465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15231263052768813038417953 11423447289576609778813465)
          ·
            refine ⟨8567585467182457334110099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11423447289576609778813465 8567585467182457334110099)
            ·
              refine ⟨12851378200773686001165149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8567585467182457334110099 12851378200773686001165149)
              ·
                refine ⟨4819266825290132250436931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12851378200773686001165149 4819266825290132250436931)
                ·
                  refine ⟨7228900237935198375655397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4819266825290132250436931 7228900237935198375655397)
                  ·
                    refine ⟨1355418794612849695435387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7228900237935198375655397 1355418794612849695435387)
                    ·
                      rfl

theorem cell23_7919006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_7919006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919006 prefixEnd_7919006 := by exact prefixLift 7919006
  have htrace : WordTrace (prefixWord ++ tailWord_7919006) baseStart_7919006 baseEnd_7919006 := by
    simpa [prefixWord, tailWord_7919006, baseEnd_7919006] using wordTrace_append hprefix tailTrace_7919006
  have hstable : (prefixWord ++ tailWord_7919006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919006).length < 2 ^ (prefixWord ++ tailWord_7919006).sum := by decide
  have hdescent : baseEnd_7919006 < baseStart_7919006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919011 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 3, 6]
def baseStart_7919011 : Nat := 118140960795 + 7919011 * 2 ^ 59
def prefixEnd_7919011 : Nat := 4983230072969 + 3 ^ 40 * 7919011 * 2
def baseEnd_7919011 : Nat := 1355419650413940522247879

theorem tailTrace_7919011 : CollatzResearch.WordTrace tailWord_7919011 prefixEnd_7919011 1355419650413940522247879 := by
  unfold tailWord_7919011
  simp only [CollatzResearch.WordTrace]
  refine ⟨288830059513783081249116887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192553373009188720832744591 288830059513783081249116887)
  ·
    refine ⟨433245089270674621873675331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288830059513783081249116887 433245089270674621873675331)
    ·
      refine ⟨649867633906011932810512997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433245089270674621873675331 649867633906011932810512997)
      ·
        refine ⟨121850181357377237401971187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 649867633906011932810512997 121850181357377237401971187)
        ·
          refine ⟨182775272036065856102956781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121850181357377237401971187 182775272036065856102956781)
          ·
            refine ⟨68540727013524696038608793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182775272036065856102956781 68540727013524696038608793)
            ·
              refine ⟨51405545260143522028956595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68540727013524696038608793 51405545260143522028956595)
              ·
                refine ⟨77108317890215283043434893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51405545260143522028956595 77108317890215283043434893)
                ·
                  refine ⟨28915619208830731141288085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77108317890215283043434893 28915619208830731141288085)
                  ·
                    refine ⟨1355419650413940522247879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28915619208830731141288085 1355419650413940522247879)
                    ·
                      rfl

theorem cell23_7919011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 6].length) (baseStart_7919011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919011 prefixEnd_7919011 := by exact prefixLift 7919011
  have htrace : WordTrace (prefixWord ++ tailWord_7919011) baseStart_7919011 baseEnd_7919011 := by
    simpa [prefixWord, tailWord_7919011, baseEnd_7919011] using wordTrace_append hprefix tailTrace_7919011
  have hstable : (prefixWord ++ tailWord_7919011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919011).length < 2 ^ (prefixWord ++ tailWord_7919011).sum := by decide
  have hdescent : baseEnd_7919011 < baseStart_7919011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919031 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_7919031 : Nat := 118140960795 + 7919031 * 2 ^ 59
def prefixEnd_7919031 : Nat := 4983230072969 + 3 ^ 40 * 7919031 * 2
def baseEnd_7919031 : Nat := 4066269220854911488493545

theorem tailTrace_7919031 : CollatzResearch.WordTrace tailWord_7919031 prefixEnd_7919031 4066269220854911488493545 := by
  unfold tailWord_7919031
  simp only [CollatzResearch.WordTrace]
  refine ⟨288830788973710624664844947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192553859315807083109896631 288830788973710624664844947)
  ·
    refine ⟨433246183460565936997267421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288830788973710624664844947 433246183460565936997267421)
    ·
      refine ⟨162467318797712226373975283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433246183460565936997267421 162467318797712226373975283)
      ·
        refine ⟨243700978196568339560962925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162467318797712226373975283 243700978196568339560962925)
        ·
          refine ⟨91387866823713127335361097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243700978196568339560962925 91387866823713127335361097)
          ·
            refine ⟨68540900117784845501520823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91387866823713127335361097 68540900117784845501520823)
            ·
              refine ⟨102811350176677268252281235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68540900117784845501520823 102811350176677268252281235)
              ·
                refine ⟨154217025265015902378421853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102811350176677268252281235 154217025265015902378421853)
                ·
                  refine ⟨57831384474380963391908195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154217025265015902378421853 57831384474380963391908195)
                  ·
                    refine ⟨86747076711571445087862293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57831384474380963391908195 86747076711571445087862293)
                    ·
                      refine ⟨4066269220854911488493545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86747076711571445087862293 4066269220854911488493545)
                      ·
                        rfl

theorem cell23_7919031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_7919031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919031 prefixEnd_7919031 := by exact prefixLift 7919031
  have htrace : WordTrace (prefixWord ++ tailWord_7919031) baseStart_7919031 baseEnd_7919031 := by
    simpa [prefixWord, tailWord_7919031, baseEnd_7919031] using wordTrace_append hprefix tailTrace_7919031
  have hstable : (prefixWord ++ tailWord_7919031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919031).length < 2 ^ (prefixWord ++ tailWord_7919031).sum := by decide
  have hdescent : baseEnd_7919031 < baseStart_7919031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919038 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_7919038 : Nat := 118140960795 + 7919038 * 2 ^ 59
def prefixEnd_7919038 : Nat := 4983230072969 + 3 ^ 40 * 7919038 * 2
def baseEnd_7919038 : Nat := 4066272815219492961106013

theorem tailTrace_7919038 : CollatzResearch.WordTrace tailWord_7919038 prefixEnd_7919038 4066272815219492961106013 := by
  unfold tailWord_7919038
  simp only [CollatzResearch.WordTrace]
  refine ⟨36103880535585658107543721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192554029523123509906899845 36103880535585658107543721)
  ·
    refine ⟨27077910401689243580657791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36103880535585658107543721 27077910401689243580657791)
    ·
      refine ⟨40616865602533865370986687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27077910401689243580657791 40616865602533865370986687)
      ·
        refine ⟨60925298403800798056480031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40616865602533865370986687 60925298403800798056480031)
        ·
          refine ⟨91387947605701197084720047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60925298403800798056480031 91387947605701197084720047)
          ·
            refine ⟨137081921408551795627080071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91387947605701197084720047 137081921408551795627080071)
            ·
              refine ⟨205622882112827693440620107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137081921408551795627080071 205622882112827693440620107)
              ·
                refine ⟨308434323169241540160930161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205622882112827693440620107 308434323169241540160930161)
                ·
                  refine ⟨231325742376931155120697621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308434323169241540160930161 231325742376931155120697621)
                  ·
                    refine ⟨10843394173918647896282701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 231325742376931155120697621 10843394173918647896282701)
                    ·
                      refine ⟨4066272815219492961106013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843394173918647896282701 4066272815219492961106013)
                      ·
                        rfl

theorem cell23_7919038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_7919038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919038 prefixEnd_7919038 := by exact prefixLift 7919038
  have htrace : WordTrace (prefixWord ++ tailWord_7919038) baseStart_7919038 baseEnd_7919038 := by
    simpa [prefixWord, tailWord_7919038, baseEnd_7919038] using wordTrace_append hprefix tailTrace_7919038
  have hstable : (prefixWord ++ tailWord_7919038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919038).length < 2 ^ (prefixWord ++ tailWord_7919038).sum := by decide
  have hdescent : baseEnd_7919038 < baseStart_7919038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919048 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_7919048 : Nat := 118140960795 + 7919048 * 2 ^ 59
def prefixEnd_7919048 : Nat := 4983230072969 + 3 ^ 40 * 7919048 * 2
def baseEnd_7919048 : Nat := 4066277950026037921980967

theorem tailTrace_7919048 : CollatzResearch.WordTrace tailWord_7919048 prefixEnd_7919048 4066277950026037921980967 := by
  unfold tailWord_7919048
  simp only [CollatzResearch.WordTrace]
  refine ⟨144415704507324518284106899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192554272676432691045475865 144415704507324518284106899)
  ·
    refine ⟨216623556760986777426160349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144415704507324518284106899 216623556760986777426160349)
    ·
      refine ⟨81233833785370041534810131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216623556760986777426160349 81233833785370041534810131)
      ·
        refine ⟨121850750678055062302215197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81233833785370041534810131 121850750678055062302215197)
        ·
          refine ⟨45694031504270648363330699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121850750678055062302215197 45694031504270648363330699)
          ·
            refine ⟨68541047256405972544996049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45694031504270648363330699 68541047256405972544996049)
            ·
              refine ⟨51405785442304479408747037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68541047256405972544996049 51405785442304479408747037)
              ·
                refine ⟨19277169540864179778280139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51405785442304479408747037 19277169540864179778280139)
                ·
                  refine ⟨28915754311296269667420209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19277169540864179778280139 28915754311296269667420209)
                  ·
                    refine ⟨21686815733472202250565157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28915754311296269667420209 21686815733472202250565157)
                    ·
                      refine ⟨4066277950026037921980967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21686815733472202250565157 4066277950026037921980967)
                      ·
                        rfl

theorem cell23_7919048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_7919048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919048 prefixEnd_7919048 := by exact prefixLift 7919048
  have htrace : WordTrace (prefixWord ++ tailWord_7919048) baseStart_7919048 baseEnd_7919048 := by
    simpa [prefixWord, tailWord_7919048, baseEnd_7919048] using wordTrace_append hprefix tailTrace_7919048
  have hstable : (prefixWord ++ tailWord_7919048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919048).length < 2 ^ (prefixWord ++ tailWord_7919048).sum := by decide
  have hdescent : baseEnd_7919048 < baseStart_7919048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919052 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 1, 1, 4]
def baseStart_7919052 : Nat := 118140960795 + 7919052 * 2 ^ 59
def prefixEnd_7919052 : Nat := 4983230072969 + 3 ^ 40 * 7919052 * 2
def baseEnd_7919052 : Nat := 4066280003948655906330949

theorem tailTrace_7919052 : CollatzResearch.WordTrace tailWord_7919052 prefixEnd_7919052 4066280003948655906330949 := by
  unfold tailWord_7919052
  simp only [CollatzResearch.WordTrace]
  refine ⟨144415777453317272625679705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192554369937756363500906273 144415777453317272625679705)
  ·
    refine ⟨108311833089987954469259779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144415777453317272625679705 108311833089987954469259779)
    ·
      refine ⟨162467749634981931703889669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108311833089987954469259779 162467749634981931703889669)
      ·
        refine ⟨30462703056559112194479313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162467749634981931703889669 30462703056559112194479313)
        ·
          refine ⟨22847027292419334145859485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30462703056559112194479313 22847027292419334145859485)
          ·
            refine ⟨8567635234657250304697307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22847027292419334145859485 8567635234657250304697307)
            ·
              refine ⟨12851452851985875457045961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8567635234657250304697307 12851452851985875457045961)
              ·
                refine ⟨9638589638989406592784471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12851452851985875457045961 9638589638989406592784471)
                ·
                  refine ⟨14457884458484109889176707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9638589638989406592784471 14457884458484109889176707)
                  ·
                    refine ⟨21686826687726164833765061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14457884458484109889176707 21686826687726164833765061)
                    ·
                      refine ⟨4066280003948655906330949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21686826687726164833765061 4066280003948655906330949)
                      ·
                        rfl

theorem cell23_7919052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_7919052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919052 prefixEnd_7919052 := by exact prefixLift 7919052
  have htrace : WordTrace (prefixWord ++ tailWord_7919052) baseStart_7919052 baseEnd_7919052 := by
    simpa [prefixWord, tailWord_7919052, baseEnd_7919052] using wordTrace_append hprefix tailTrace_7919052
  have hstable : (prefixWord ++ tailWord_7919052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919052).length < 2 ^ (prefixWord ++ tailWord_7919052).sum := by decide
  have hdescent : baseEnd_7919052 < baseStart_7919052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919055 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 1, 2, 3]
def baseStart_7919055 : Nat := 118140960795 + 7919055 * 2 ^ 59
def prefixEnd_7919055 : Nat := 4983230072969 + 3 ^ 40 * 7919055 * 2
def baseEnd_7919055 : Nat := 4066281544390619394593435

theorem tailTrace_7919055 : CollatzResearch.WordTrace tailWord_7919055 prefixEnd_7919055 4066281544390619394593435 := by
  unfold tailWord_7919055
  simp only [CollatzResearch.WordTrace]
  refine ⟨288831664325623676763718619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192554442883749117842479079 288831664325623676763718619)
  ·
    refine ⟨433247496488435515145577929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288831664325623676763718619 433247496488435515145577929)
    ·
      refine ⟨324935622366326636359183447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433247496488435515145577929 324935622366326636359183447)
      ·
        refine ⟨487403433549489954538775171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324935622366326636359183447 487403433549489954538775171)
        ·
          refine ⟨731105150324234931808162757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487403433549489954538775171 731105150324234931808162757)
          ·
            refine ⟨137082215685794049714030517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 731105150324234931808162757 137082215685794049714030517)
            ·
              refine ⟨12851457720543192160690361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137082215685794049714030517 12851457720543192160690361)
              ·
                refine ⟨9638593290407394120517771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12851457720543192160690361 9638593290407394120517771)
                ·
                  refine ⟨14457889935611091180776657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9638593290407394120517771 14457889935611091180776657)
                  ·
                    refine ⟨10843417451708318385582493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14457889935611091180776657 10843417451708318385582493)
                    ·
                      refine ⟨4066281544390619394593435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843417451708318385582493 4066281544390619394593435)
                      ·
                        rfl

theorem cell23_7919055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 2, 3].length) (baseStart_7919055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919055 prefixEnd_7919055 := by exact prefixLift 7919055
  have htrace : WordTrace (prefixWord ++ tailWord_7919055) baseStart_7919055 baseEnd_7919055 := by
    simpa [prefixWord, tailWord_7919055, baseEnd_7919055] using wordTrace_append hprefix tailTrace_7919055
  have hstable : (prefixWord ++ tailWord_7919055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919055).length < 2 ^ (prefixWord ++ tailWord_7919055).sum := by decide
  have hdescent : baseEnd_7919055 < baseStart_7919055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919081 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_7919081 : Nat := 118140960795 + 7919081 * 2 ^ 59
def prefixEnd_7919081 : Nat := 4983230072969 + 3 ^ 40 * 7919081 * 2
def baseEnd_7919081 : Nat := 4066294894887636292868315

theorem tailTrace_7919081 : CollatzResearch.WordTrace tailWord_7919081 prefixEnd_7919081 4066294894887636292868315 := by
  unfold tailWord_7919081
  simp only [CollatzResearch.WordTrace]
  refine ⟨288832612623529483204165097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192555075082352988802776731 288832612623529483204165097)
  ·
    refine ⟨216624459467647112403123823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288832612623529483204165097 216624459467647112403123823)
    ·
      refine ⟨324936689201470668604685735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216624459467647112403123823 324936689201470668604685735)
      ·
        refine ⟨487405033802206002907028603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324936689201470668604685735 487405033802206002907028603)
        ·
          refine ⟨731107550703309004360542905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487405033802206002907028603 731107550703309004360542905)
          ·
            refine ⟨548330663027481753270407179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731107550703309004360542905 548330663027481753270407179)
            ·
              refine ⟨822495994541222629905610769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548330663027481753270407179 822495994541222629905610769)
              ·
                refine ⟨616871995905916972429208077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822495994541222629905610769 616871995905916972429208077)
                ·
                  refine ⟨231326998464718864660953029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616871995905916972429208077 231326998464718864660953029)
                  ·
                    refine ⟨43373812212134787123928693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231326998464718864660953029 43373812212134787123928693)
                    ·
                      refine ⟨4066294894887636292868315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43373812212134787123928693 4066294894887636292868315)
                      ·
                        rfl

theorem cell23_7919081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_7919081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919081 prefixEnd_7919081 := by exact prefixLift 7919081
  have htrace : WordTrace (prefixWord ++ tailWord_7919081) baseStart_7919081 baseEnd_7919081 := by
    simpa [prefixWord, tailWord_7919081, baseEnd_7919081] using wordTrace_append hprefix tailTrace_7919081
  have hstable : (prefixWord ++ tailWord_7919081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919081).length < 2 ^ (prefixWord ++ tailWord_7919081).sum := by decide
  have hdescent : baseEnd_7919081 < baseStart_7919081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919178 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_7919178 : Nat := 118140960795 + 7919178 * 2 ^ 59
def prefixEnd_7919178 : Nat := 4983230072969 + 3 ^ 40 * 7919178 * 2
def baseEnd_7919178 : Nat := 1355448234170374137785123

theorem tailTrace_7919178 : CollatzResearch.WordTrace tailWord_7919178 prefixEnd_7919178 1355448234170374137785123 := by
  unfold tailWord_7919178
  simp only [CollatzResearch.WordTrace]
  refine ⟨72209037626044517192611547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192557433669452045846964125 72209037626044517192611547)
  ·
    refine ⟨108313556439066775788917321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72209037626044517192611547 108313556439066775788917321)
    ·
      refine ⟨81235167329300081841687991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108313556439066775788917321 81235167329300081841687991)
      ·
        refine ⟨121852750993950122762531987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81235167329300081841687991 121852750993950122762531987)
        ·
          refine ⟨182779126490925184143797981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121852750993950122762531987 182779126490925184143797981)
          ·
            refine ⟨68542172434096944053924243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182779126490925184143797981 68542172434096944053924243)
            ·
              refine ⟨102813258651145416080886365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68542172434096944053924243 102813258651145416080886365)
              ·
                refine ⟨38554971994179531030332387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102813258651145416080886365 38554971994179531030332387)
                ·
                  refine ⟨57832457991269296545498581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38554971994179531030332387 57832457991269296545498581)
                  ·
                    refine ⟨1355448234170374137785123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57832457991269296545498581 1355448234170374137785123)
                    ·
                      rfl

theorem cell23_7919178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_7919178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919178 prefixEnd_7919178 := by exact prefixLift 7919178
  have htrace : WordTrace (prefixWord ++ tailWord_7919178) baseStart_7919178 baseEnd_7919178 := by
    simpa [prefixWord, tailWord_7919178, baseEnd_7919178] using wordTrace_append hprefix tailTrace_7919178
  have hstable : (prefixWord ++ tailWord_7919178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919178).length < 2 ^ (prefixWord ++ tailWord_7919178).sum := by decide
  have hdescent : baseEnd_7919178 < baseStart_7919178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919205 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_7919205 : Nat := 118140960795 + 7919205 * 2 ^ 59
def prefixEnd_7919205 : Nat := 4983230072969 + 3 ^ 40 * 7919205 * 2
def baseEnd_7919205 : Nat := 4066358566488793807717745

theorem tailTrace_7919205 : CollatzResearch.WordTrace tailWord_7919205 prefixEnd_7919205 4066358566488793807717745 := by
  unfold tailWord_7919205
  simp only [CollatzResearch.WordTrace]
  refine ⟨288837135275080252381679069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192558090183386834921119379 288837135275080252381679069)
  ·
    refine ⟨108313925728155094643129651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288837135275080252381679069 108313925728155094643129651)
    ·
      refine ⟨162470888592232641964694477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108313925728155094643129651 162470888592232641964694477)
      ·
        refine ⟨60926583222087240736760429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162470888592232641964694477 60926583222087240736760429)
        ·
          refine ⟨22847468708282715276285161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60926583222087240736760429 22847468708282715276285161)
          ·
            refine ⟨17135601531212036457213871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22847468708282715276285161 17135601531212036457213871)
            ·
              refine ⟨25703402296818054685820807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17135601531212036457213871 25703402296818054685820807)
              ·
                refine ⟨38555103445227082028731211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25703402296818054685820807 38555103445227082028731211)
                ·
                  refine ⟨57832655167840623043096817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38555103445227082028731211 57832655167840623043096817)
                  ·
                    refine ⟨43374491375880467282322613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57832655167840623043096817 43374491375880467282322613)
                    ·
                      refine ⟨4066358566488793807717745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43374491375880467282322613 4066358566488793807717745)
                      ·
                        rfl

theorem cell23_7919205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_7919205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919205 prefixEnd_7919205 := by exact prefixLift 7919205
  have htrace : WordTrace (prefixWord ++ tailWord_7919205) baseStart_7919205 baseEnd_7919205 := by
    simpa [prefixWord, tailWord_7919205, baseEnd_7919205] using wordTrace_append hprefix tailTrace_7919205
  have hstable : (prefixWord ++ tailWord_7919205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919205).length < 2 ^ (prefixWord ++ tailWord_7919205).sum := by decide
  have hdescent : baseEnd_7919205 < baseStart_7919205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919215 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 1, 6, 2]
def baseStart_7919215 : Nat := 118140960795 + 7919215 * 2 ^ 59
def prefixEnd_7919215 : Nat := 4983230072969 + 3 ^ 40 * 7919215 * 2
def baseEnd_7919215 : Nat := 4066363701295338768592699

theorem tailTrace_7919215 : CollatzResearch.WordTrace tailWord_7919215 prefixEnd_7919215 4066363701295338768592699 := by
  unfold tailWord_7919215
  simp only [CollatzResearch.WordTrace]
  refine ⟨288837500005044024089543099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192558333336696016059695399 288837500005044024089543099)
  ·
    refine ⟨433256250007566036134314649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288837500005044024089543099 433256250007566036134314649)
    ·
      refine ⟨324942187505674527100735987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433256250007566036134314649 324942187505674527100735987)
      ·
        refine ⟨487413281258511790651103981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324942187505674527100735987 487413281258511790651103981)
        ·
          refine ⟨182779980471941921494163993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487413281258511790651103981 182779980471941921494163993)
          ·
            refine ⟨137084985353956441120622995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182779980471941921494163993 137084985353956441120622995)
            ·
              refine ⟨205627478030934661680934493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137084985353956441120622995 205627478030934661680934493)
              ·
                refine ⟨77110304261600498130350435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205627478030934661680934493 77110304261600498130350435)
                ·
                  refine ⟨115665456392400747195525653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77110304261600498130350435 115665456392400747195525653)
                  ·
                    refine ⟨5421818268393785024790265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115665456392400747195525653 5421818268393785024790265)
                    ·
                      refine ⟨4066363701295338768592699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421818268393785024790265 4066363701295338768592699)
                      ·
                        rfl

theorem cell23_7919215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 6, 2].length) (baseStart_7919215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919215 prefixEnd_7919215 := by exact prefixLift 7919215
  have htrace : WordTrace (prefixWord ++ tailWord_7919215) baseStart_7919215 baseEnd_7919215 := by
    simpa [prefixWord, tailWord_7919215, baseEnd_7919215] using wordTrace_append hprefix tailTrace_7919215
  have hstable : (prefixWord ++ tailWord_7919215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919215).length < 2 ^ (prefixWord ++ tailWord_7919215).sum := by decide
  have hdescent : baseEnd_7919215 < baseStart_7919215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919225 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 5, 4]
def baseStart_7919225 : Nat := 118140960795 + 7919225 * 2 ^ 59
def prefixEnd_7919225 : Nat := 4983230072969 + 3 ^ 40 * 7919225 * 2
def baseEnd_7919225 : Nat := 1355456278700627909822551

theorem tailTrace_7919225 : CollatzResearch.WordTrace tailWord_7919225 prefixEnd_7919225 1355456278700627909822551 := by
  unfold tailWord_7919225
  simp only [CollatzResearch.WordTrace]
  refine ⟨288837864735007795797407129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192558576490005197198271419 288837864735007795797407129)
  ·
    refine ⟨216628398551255846848055347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288837864735007795797407129 216628398551255846848055347)
    ·
      refine ⟨324942597826883770272083021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216628398551255846848055347 324942597826883770272083021)
      ·
        refine ⟨121853474185081413852031133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324942597826883770272083021 121853474185081413852031133)
        ·
          refine ⟨45695052819405530194511675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121853474185081413852031133 45695052819405530194511675)
          ·
            refine ⟨68542579229108295291767513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45695052819405530194511675 68542579229108295291767513)
            ·
              refine ⟨51406934421831221468825635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68542579229108295291767513 51406934421831221468825635)
              ·
                refine ⟨77110401632746832203238453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51406934421831221468825635 77110401632746832203238453)
                ·
                  refine ⟨7229100153070015519053605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77110401632746832203238453 7229100153070015519053605)
                  ·
                    refine ⟨1355456278700627909822551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7229100153070015519053605 1355456278700627909822551)
                    ·
                      rfl

theorem cell23_7919225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 4].length) (baseStart_7919225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919225 prefixEnd_7919225 := by exact prefixLift 7919225
  have htrace : WordTrace (prefixWord ++ tailWord_7919225) baseStart_7919225 baseEnd_7919225 := by
    simpa [prefixWord, tailWord_7919225, baseEnd_7919225] using wordTrace_append hprefix tailTrace_7919225
  have hstable : (prefixWord ++ tailWord_7919225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919225).length < 2 ^ (prefixWord ++ tailWord_7919225).sum := by decide
  have hdescent : baseEnd_7919225 < baseStart_7919225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919228 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_7919228 : Nat := 118140960795 + 7919228 * 2 ^ 59
def prefixEnd_7919228 : Nat := 4983230072969 + 3 ^ 40 * 7919228 * 2
def baseEnd_7919228 : Nat := 4066370376543847217730139

theorem tailTrace_7919228 : CollatzResearch.WordTrace tailWord_7919228 prefixEnd_7919228 4066370376543847217730139 := by
  unfold tailWord_7919228
  simp only [CollatzResearch.WordTrace]
  refine ⟨144418987076998463654883169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192558649435997951539844225 144418987076998463654883169)
  ·
    refine ⟨108314240307748847741162377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144418987076998463654883169 108314240307748847741162377)
    ·
      refine ⟨81235680230811635805871783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108314240307748847741162377 81235680230811635805871783)
      ·
        refine ⟨121853520346217453708807675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81235680230811635805871783 121853520346217453708807675)
        ·
          refine ⟨182780280519326180563211513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121853520346217453708807675 182780280519326180563211513)
          ·
            refine ⟨137085210389494635422408635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182780280519326180563211513 137085210389494635422408635)
            ·
              refine ⟨205627815584241953133612953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137085210389494635422408635 205627815584241953133612953)
              ·
                refine ⟨154220861688181464850209715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205627815584241953133612953 154220861688181464850209715)
                ·
                  refine ⟨231331292532272197275314573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154220861688181464850209715 231331292532272197275314573)
                  ·
                    refine ⟨86749234699602073978242965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231331292532272197275314573 86749234699602073978242965)
                    ·
                      refine ⟨4066370376543847217730139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86749234699602073978242965 4066370376543847217730139)
                      ·
                        rfl

theorem cell23_7919228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_7919228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919228 prefixEnd_7919228 := by exact prefixLift 7919228
  have htrace : WordTrace (prefixWord ++ tailWord_7919228) baseStart_7919228 baseEnd_7919228 := by
    simpa [prefixWord, tailWord_7919228, baseEnd_7919228] using wordTrace_append hprefix tailTrace_7919228
  have hstable : (prefixWord ++ tailWord_7919228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919228).length < 2 ^ (prefixWord ++ tailWord_7919228).sum := by decide
  have hdescent : baseEnd_7919228 < baseStart_7919228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919255 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 6]
def baseStart_7919255 : Nat := 118140960795 + 7919255 * 2 ^ 59
def prefixEnd_7919255 : Nat := 4983230072969 + 3 ^ 40 * 7919255 * 2
def baseEnd_7919255 : Nat := 451820471169057623565835

theorem tailTrace_7919255 : CollatzResearch.WordTrace tailWord_7919255 prefixEnd_7919255 451820471169057623565835 := by
  unfold tailWord_7919255
  simp only [CollatzResearch.WordTrace]
  refine ⟨288838958924899110920999219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192559305949932740613999479 288838958924899110920999219)
  ·
    refine ⟨433258438387348666381498829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288838958924899110920999219 433258438387348666381498829)
    ·
      refine ⟨162471914395255749893062061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433258438387348666381498829 162471914395255749893062061)
      ·
        refine ⟨60926967898220906209898273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162471914395255749893062061 60926967898220906209898273)
        ·
          refine ⟨45695225923665679657423705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60926967898220906209898273 45695225923665679657423705)
          ·
            refine ⟨34271419442749259743067779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45695225923665679657423705 34271419442749259743067779)
            ·
              refine ⟨51407129164123889614601669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34271419442749259743067779 51407129164123889614601669)
              ·
                refine ⟨9638836718273229302737813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51407129164123889614601669 9638836718273229302737813)
                ·
                  refine ⟨451820471169057623565835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9638836718273229302737813 451820471169057623565835)
                  ·
                    rfl

theorem cell23_7919255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 6].length) (baseStart_7919255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919255 prefixEnd_7919255 := by exact prefixLift 7919255
  have htrace : WordTrace (prefixWord ++ tailWord_7919255) baseStart_7919255 baseEnd_7919255 := by
    simpa [prefixWord, tailWord_7919255, baseEnd_7919255] using wordTrace_append hprefix tailTrace_7919255
  have hstable : (prefixWord ++ tailWord_7919255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919255).length < 2 ^ (prefixWord ++ tailWord_7919255).sum := by decide
  have hdescent : baseEnd_7919255 < baseStart_7919255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919266 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7919266 : Nat := 118140960795 + 7919266 * 2 ^ 59
def prefixEnd_7919266 : Nat := 4983230072969 + 3 ^ 40 * 7919266 * 2
def baseEnd_7919266 : Nat := 4066389888808718069054965

theorem tailTrace_7919266 : CollatzResearch.WordTrace tailWord_7919266 prefixEnd_7919266 4066389888808718069054965 := by
  unfold tailWord_7919266
  simp only [CollatzResearch.WordTrace]
  refine ⟨72209840031964814949912413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192559573418572839866433101 72209840031964814949912413)
  ·
    refine ⟨27078690011986805606217155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72209840031964814949912413 27078690011986805606217155)
    ·
      refine ⟨40618035017980208409325733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27078690011986805606217155 40618035017980208409325733)
      ·
        refine ⟨7615881565871289076748575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40618035017980208409325733 7615881565871289076748575)
        ·
          refine ⟨11423822348806933615122863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7615881565871289076748575 11423822348806933615122863)
          ·
            refine ⟨17135733523210400422684295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11423822348806933615122863 17135733523210400422684295)
            ·
              refine ⟨25703600284815600634026443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17135733523210400422684295 25703600284815600634026443)
              ·
                refine ⟨38555400427223400951039665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25703600284815600634026443 38555400427223400951039665)
                ·
                  refine ⟨28916550320417550713279749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38555400427223400951039665 28916550320417550713279749)
                  ·
                    refine ⟨5421853185078290758739953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28916550320417550713279749 5421853185078290758739953)
                    ·
                      refine ⟨4066389888808718069054965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421853185078290758739953 4066389888808718069054965)
                      ·
                        rfl

theorem cell23_7919266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7919266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919266 prefixEnd_7919266 := by exact prefixLift 7919266
  have htrace : WordTrace (prefixWord ++ tailWord_7919266) baseStart_7919266 baseEnd_7919266 := by
    simpa [prefixWord, tailWord_7919266, baseEnd_7919266] using wordTrace_append hprefix tailTrace_7919266
  have hstable : (prefixWord ++ tailWord_7919266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919266).length < 2 ^ (prefixWord ++ tailWord_7919266).sum := by decide
  have hdescent : baseEnd_7919266 < baseStart_7919266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919282 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_7919282 : Nat := 118140960795 + 7919282 * 2 ^ 59
def prefixEnd_7919282 : Nat := 4983230072969 + 3 ^ 40 * 7919282 * 2
def baseEnd_7919282 : Nat := 4066398104499190006454891

theorem tailTrace_7919282 : CollatzResearch.WordTrace tailWord_7919282 prefixEnd_7919282 4066398104499190006454891 := by
  unfold tailWord_7919282
  simp only [CollatzResearch.WordTrace]
  refine ⟨72209985923950323633058025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192559962463867529688154733 72209985923950323633058025)
  ·
    refine ⟨54157489442962742724793519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72209985923950323633058025 54157489442962742724793519)
    ·
      refine ⟨81236234164444114087190279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54157489442962742724793519 81236234164444114087190279)
      ·
        refine ⟨121854351246666171130785419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81236234164444114087190279 121854351246666171130785419)
        ·
          refine ⟨182781526869999256696178129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121854351246666171130785419 182781526869999256696178129)
          ·
            refine ⟨137086145152499442522133597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182781526869999256696178129 137086145152499442522133597)
            ·
              refine ⟨51407304432187290945800099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137086145152499442522133597 51407304432187290945800099)
              ·
                refine ⟨77110956648280936418700149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51407304432187290945800099 77110956648280936418700149)
                ·
                  refine ⟨7229152185776337789253139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77110956648280936418700149 7229152185776337789253139)
                  ·
                    refine ⟨10843728278664506683879709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7229152185776337789253139 10843728278664506683879709)
                    ·
                      refine ⟨4066398104499190006454891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843728278664506683879709 4066398104499190006454891)
                      ·
                        rfl

theorem cell23_7919282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_7919282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919282 prefixEnd_7919282 := by exact prefixLift 7919282
  have htrace : WordTrace (prefixWord ++ tailWord_7919282) baseStart_7919282 baseEnd_7919282 := by
    simpa [prefixWord, tailWord_7919282, baseEnd_7919282] using wordTrace_append hprefix tailTrace_7919282
  have hstable : (prefixWord ++ tailWord_7919282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919282).length < 2 ^ (prefixWord ++ tailWord_7919282).sum := by decide
  have hdescent : baseEnd_7919282 < baseStart_7919282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919286 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_7919286 : Nat := 118140960795 + 7919286 * 2 ^ 59
def prefixEnd_7919286 : Nat := 4983230072969 + 3 ^ 40 * 7919286 * 2
def baseEnd_7919286 : Nat := 4066400158421807990804873

theorem tailTrace_7919286 : CollatzResearch.WordTrace tailWord_7919286 prefixEnd_7919286 4066400158421807990804873 := by
  unfold tailWord_7919286
  simp only [CollatzResearch.WordTrace]
  refine ⟨18052505599236675200961107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192560059725191202143585141 18052505599236675200961107)
  ·
    refine ⟨27078758398855012801441661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18052505599236675200961107 27078758398855012801441661)
    ·
      refine ⟨10154534399570629800540623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27078758398855012801441661 10154534399570629800540623)
      ·
        refine ⟨15231801599355944700810935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10154534399570629800540623 15231801599355944700810935)
        ·
          refine ⟨22847702399033917051216403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15231801599355944700810935 22847702399033917051216403)
          ·
            refine ⟨34271553598550875576824605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22847702399033917051216403 34271553598550875576824605)
            ·
              refine ⟨12851832599456578341309227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34271553598550875576824605 12851832599456578341309227)
              ·
                refine ⟨19277748899184867511963841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12851832599456578341309227 19277748899184867511963841)
                ·
                  refine ⟨14458311674388650633972881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19277748899184867511963841 14458311674388650633972881)
                  ·
                    refine ⟨10843733755791487975479661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14458311674388650633972881 10843733755791487975479661)
                    ·
                      refine ⟨4066400158421807990804873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843733755791487975479661 4066400158421807990804873)
                      ·
                        rfl

theorem cell23_7919286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_7919286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919286 prefixEnd_7919286 := by exact prefixLift 7919286
  have htrace : WordTrace (prefixWord ++ tailWord_7919286) baseStart_7919286 baseEnd_7919286 := by
    simpa [prefixWord, tailWord_7919286, baseEnd_7919286] using wordTrace_append hprefix tailTrace_7919286
  have hstable : (prefixWord ++ tailWord_7919286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919286).length < 2 ^ (prefixWord ++ tailWord_7919286).sum := by decide
  have hdescent : baseEnd_7919286 < baseStart_7919286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919316 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_7919316 : Nat := 118140960795 + 7919316 * 2 ^ 59
def prefixEnd_7919316 : Nat := 4983230072969 + 3 ^ 40 * 7919316 * 2
def baseEnd_7919316 : Nat := 4066415562841442873429735

theorem tailTrace_7919316 : CollatzResearch.WordTrace tailWord_7919316 prefixEnd_7919316 4066415562841442873429735 := by
  unfold tailWord_7919316
  simp only [CollatzResearch.WordTrace]
  refine ⟨144420591888839059169484901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192560789185118745559313201 144420591888839059169484901)
  ·
    refine ⟨27078860979157323594278419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144420591888839059169484901 27078860979157323594278419)
    ·
      refine ⟨40618291468735985391417629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27078860979157323594278419 40618291468735985391417629)
      ·
        refine ⟨15231859300775994521781611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40618291468735985391417629 15231859300775994521781611)
        ·
          refine ⟨22847788951163991782672417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15231859300775994521781611 22847788951163991782672417)
          ·
            refine ⟨17135841713372993837004313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22847788951163991782672417 17135841713372993837004313)
            ·
              refine ⟨12851881285029745377753235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17135841713372993837004313 12851881285029745377753235)
              ·
                refine ⟨19277821927544618066629853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12851881285029745377753235 19277821927544618066629853)
                ·
                  refine ⟨7229183222829231774986195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19277821927544618066629853 7229183222829231774986195)
                  ·
                    refine ⟨10843774834243847662479293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7229183222829231774986195 10843774834243847662479293)
                    ·
                      refine ⟨4066415562841442873429735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843774834243847662479293 4066415562841442873429735)
                      ·
                        rfl

theorem cell23_7919316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_7919316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919316 prefixEnd_7919316 := by exact prefixLift 7919316
  have htrace : WordTrace (prefixWord ++ tailWord_7919316) baseStart_7919316 baseEnd_7919316 := by
    simpa [prefixWord, tailWord_7919316, baseEnd_7919316] using wordTrace_append hprefix tailTrace_7919316
  have hstable : (prefixWord ++ tailWord_7919316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919316).length < 2 ^ (prefixWord ++ tailWord_7919316).sum := by decide
  have hdescent : baseEnd_7919316 < baseStart_7919316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919339 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 3, 2, 2]
def baseStart_7919339 : Nat := 118140960795 + 7919339 * 2 ^ 59
def prefixEnd_7919339 : Nat := 4983230072969 + 3 ^ 40 * 7919339 * 2
def baseEnd_7919339 : Nat := 4066427372896496283442129

theorem tailTrace_7919339 : CollatzResearch.WordTrace tailWord_7919339 prefixEnd_7919339 4066427372896496283442129 := by
  unfold tailWord_7919339
  simp only [CollatzResearch.WordTrace]
  refine ⟨288842022656594793267057071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192561348437729862178038047 288842022656594793267057071)
  ·
    refine ⟨433263033984892189900585607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288842022656594793267057071 433263033984892189900585607)
    ·
      refine ⟨649894550977338284850878411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433263033984892189900585607 649894550977338284850878411)
      ·
        refine ⟨974841826466007427276317617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649894550977338284850878411 974841826466007427276317617)
        ·
          refine ⟨731131369849505570457238213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974841826466007427276317617 731131369849505570457238213)
          ·
            refine ⟨137087131846782294460732165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 731131369849505570457238213 137087131846782294460732165)
            ·
              refine ⟨25703837221271680211387281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137087131846782294460732165 25703837221271680211387281)
              ·
                refine ⟨19277877915953760158540461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25703837221271680211387281 19277877915953760158540461)
                ·
                  refine ⟨7229204218482660059452673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19277877915953760158540461 7229204218482660059452673)
                  ·
                    refine ⟨5421903163861995044589505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7229204218482660059452673 5421903163861995044589505)
                    ·
                      refine ⟨4066427372896496283442129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421903163861995044589505 4066427372896496283442129)
                      ·
                        rfl

theorem cell23_7919339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 2, 2].length) (baseStart_7919339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919339 prefixEnd_7919339 := by exact prefixLift 7919339
  have htrace : WordTrace (prefixWord ++ tailWord_7919339) baseStart_7919339 baseEnd_7919339 := by
    simpa [prefixWord, tailWord_7919339, baseEnd_7919339] using wordTrace_append hprefix tailTrace_7919339
  have hstable : (prefixWord ++ tailWord_7919339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919339).length < 2 ^ (prefixWord ++ tailWord_7919339).sum := by decide
  have hdescent : baseEnd_7919339 < baseStart_7919339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919345 : List Nat := [1, 2, 2, 2, 2, 4, 1, 9]
def baseStart_7919345 : Nat := 118140960795 + 7919345 * 2 ^ 59
def prefixEnd_7919345 : Nat := 4983230072969 + 3 ^ 40 * 7919345 * 2
def baseEnd_7919345 : Nat := 150608535325200861480263

theorem tailTrace_7919345 : CollatzResearch.WordTrace tailWord_7919345 prefixEnd_7919345 150608535325200861480263 := by
  unfold tailWord_7919345
  simp only [CollatzResearch.WordTrace]
  refine ⟨288842241494573056291775489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192561494329715370861183659 288842241494573056291775489)
  ·
    refine ⟨216631681120929792218831617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288842241494573056291775489 216631681120929792218831617)
    ·
      refine ⟨162473760840697344164123713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216631681120929792218831617 162473760840697344164123713)
      ·
        refine ⟨121855320630523008123092785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162473760840697344164123713 121855320630523008123092785)
        ·
          refine ⟨91391490472892256092319589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121855320630523008123092785 91391490472892256092319589)
          ·
            refine ⟨17135904463667298017309923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91391490472892256092319589 17135904463667298017309923)
            ·
              refine ⟨25703856695500947025964885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17135904463667298017309923 25703856695500947025964885)
              ·
                refine ⟨150608535325200861480263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25703856695500947025964885 150608535325200861480263)
                ·
                  rfl

theorem cell23_7919345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 9].length) (baseStart_7919345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919345 prefixEnd_7919345 := by exact prefixLift 7919345
  have htrace : WordTrace (prefixWord ++ tailWord_7919345) baseStart_7919345 baseEnd_7919345 := by
    simpa [prefixWord, tailWord_7919345, baseEnd_7919345] using wordTrace_append hprefix tailTrace_7919345
  have hstable : (prefixWord ++ tailWord_7919345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919345).length < 2 ^ (prefixWord ++ tailWord_7919345).sum := by decide
  have hdescent : baseEnd_7919345 < baseStart_7919345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919390 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7919390 : Nat := 118140960795 + 7919390 * 2 ^ 59
def prefixEnd_7919390 : Nat := 4983230072969 + 3 ^ 40 * 7919390 * 2
def baseEnd_7919390 : Nat := 4066453560409875583904395

theorem tailTrace_7919390 : CollatzResearch.WordTrace tailWord_7919390 prefixEnd_7919390 4066453560409875583904395 := by
  unfold tailWord_7919390
  simp only [CollatzResearch.WordTrace]
  refine ⟨36105485347426253622145453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192562588519606685984775749 36105485347426253622145453)
  ·
    refine ⟨13539557005284845108304545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36105485347426253622145453 13539557005284845108304545)
    ·
      refine ⟨10154667753963633831228409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13539557005284845108304545 10154667753963633831228409)
      ·
        refine ⟨7616000815472725373421307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10154667753963633831228409 7616000815472725373421307)
        ·
          refine ⟨11424001223209088060131961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616000815472725373421307 11424001223209088060131961)
          ·
            refine ⟨8568000917406816045098971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11424001223209088060131961 8568000917406816045098971)
            ·
              refine ⟨12852001376110224067648457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568000917406816045098971 12852001376110224067648457)
              ·
                refine ⟨9639001032082668050736343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12852001376110224067648457 9639001032082668050736343)
                ·
                  refine ⟨14458501548124002076104515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9639001032082668050736343 14458501548124002076104515)
                  ·
                    refine ⟨21687752322186003114156773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14458501548124002076104515 21687752322186003114156773)
                    ·
                      refine ⟨4066453560409875583904395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21687752322186003114156773 4066453560409875583904395)
                      ·
                        rfl

theorem cell23_7919390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7919390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919390 prefixEnd_7919390 := by exact prefixLift 7919390
  have htrace : WordTrace (prefixWord ++ tailWord_7919390) baseStart_7919390 baseEnd_7919390 := by
    simpa [prefixWord, tailWord_7919390, baseEnd_7919390] using wordTrace_append hprefix tailTrace_7919390
  have hstable : (prefixWord ++ tailWord_7919390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919390).length < 2 ^ (prefixWord ++ tailWord_7919390).sum := by decide
  have hdescent : baseEnd_7919390 < baseStart_7919390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919406 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_7919406 : Nat := 118140960795 + 7919406 * 2 ^ 59
def prefixEnd_7919406 : Nat := 4983230072969 + 3 ^ 40 * 7919406 * 2
def baseEnd_7919406 : Nat := 4066461776100347521304321

theorem tailTrace_7919406 : CollatzResearch.WordTrace tailWord_7919406 prefixEnd_7919406 4066461776100347521304321 := by
  unfold tailWord_7919406
  simp only [CollatzResearch.WordTrace]
  refine ⟨36105558293419007963718259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192562977564901375806497381 36105558293419007963718259)
  ·
    refine ⟨54158337440128511945577389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36105558293419007963718259 54158337440128511945577389)
    ·
      refine ⟨20309376540048191979591521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54158337440128511945577389 20309376540048191979591521)
      ·
        refine ⟨15232032405036143984693641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20309376540048191979591521 15232032405036143984693641)
        ·
          refine ⟨11424024303777107988520231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15232032405036143984693641 11424024303777107988520231)
          ·
            refine ⟨17136036455665661982780347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11424024303777107988520231 17136036455665661982780347)
            ·
              refine ⟨25704054683498492974170521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17136036455665661982780347 25704054683498492974170521)
              ·
                refine ⟨19278041012623869730627891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25704054683498492974170521 19278041012623869730627891)
                ·
                  refine ⟨28917061518935804595941837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19278041012623869730627891 28917061518935804595941837)
                  ·
                    refine ⟨10843898069600926723478189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28917061518935804595941837 10843898069600926723478189)
                    ·
                      refine ⟨4066461776100347521304321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843898069600926723478189 4066461776100347521304321)
                      ·
                        rfl

theorem cell23_7919406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_7919406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919406 prefixEnd_7919406 := by exact prefixLift 7919406
  have htrace : WordTrace (prefixWord ++ tailWord_7919406) baseStart_7919406 baseEnd_7919406 := by
    simpa [prefixWord, tailWord_7919406, baseEnd_7919406] using wordTrace_append hprefix tailTrace_7919406
  have hstable : (prefixWord ++ tailWord_7919406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919406).length < 2 ^ (prefixWord ++ tailWord_7919406).sum := by decide
  have hdescent : baseEnd_7919406 < baseStart_7919406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919415 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_7919415 : Nat := 118140960795 + 7919415 * 2 ^ 59
def prefixEnd_7919415 : Nat := 4983230072969 + 3 ^ 40 * 7919415 * 2
def baseEnd_7919415 : Nat := 4066466397426237986091779

theorem tailTrace_7919415 : CollatzResearch.WordTrace tailWord_7919415 prefixEnd_7919415 4066466397426237986091779 := by
  unfold tailWord_7919415
  simp only [CollatzResearch.WordTrace]
  refine ⟨288844794604319458246823699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192563196402879638831215799 288844794604319458246823699)
  ·
    refine ⟨433267191906479187370235549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288844794604319458246823699 433267191906479187370235549)
    ·
      refine ⟨162475196964929695263838331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433267191906479187370235549 162475196964929695263838331)
      ·
        refine ⟨243712795447394542895757497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162475196964929695263838331 243712795447394542895757497)
        ·
          refine ⟨182784596585545907171818123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243712795447394542895757497 182784596585545907171818123)
          ·
            refine ⟨274176894878318860757727185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182784596585545907171818123 274176894878318860757727185)
            ·
              refine ⟨205632671158739145568295389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274176894878318860757727185 205632671158739145568295389)
              ·
                refine ⟨77112251684527179588110771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205632671158739145568295389 77112251684527179588110771)
                ·
                  refine ⟨115668377526790769382166157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77112251684527179588110771 115668377526790769382166157)
                  ·
                    refine ⟨43375641572546538518312309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115668377526790769382166157 43375641572546538518312309)
                    ·
                      refine ⟨4066466397426237986091779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43375641572546538518312309 4066466397426237986091779)
                      ·
                        rfl

theorem cell23_7919415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_7919415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919415 prefixEnd_7919415 := by exact prefixLift 7919415
  have htrace : WordTrace (prefixWord ++ tailWord_7919415) baseStart_7919415 baseEnd_7919415 := by
    simpa [prefixWord, tailWord_7919415, baseEnd_7919415] using wordTrace_append hprefix tailTrace_7919415
  have hstable : (prefixWord ++ tailWord_7919415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919415).length < 2 ^ (prefixWord ++ tailWord_7919415).sum := by decide
  have hdescent : baseEnd_7919415 < baseStart_7919415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919432 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_7919432 : Nat := 118140960795 + 7919432 * 2 ^ 59
def prefixEnd_7919432 : Nat := 4983230072969 + 3 ^ 40 * 7919432 * 2
def baseEnd_7919432 : Nat := 4066475126597364419579201

theorem tailTrace_7919432 : CollatzResearch.WordTrace tailWord_7919432 prefixEnd_7919432 4066475126597364419579201 := by
  unfold tailWord_7919432
  simp only [CollatzResearch.WordTrace]
  refine ⟨144422707322628935075096275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192563609763505246766795033 144422707322628935075096275)
  ·
    refine ⟨216634060983943402612644413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144422707322628935075096275 216634060983943402612644413)
    ·
      refine ⟨81237772868978775979741655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216634060983943402612644413 81237772868978775979741655)
      ·
        refine ⟨121856659303468163969612483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81237772868978775979741655 121856659303468163969612483)
        ·
          refine ⟨182784988955202245954418725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121856659303468163969612483 182784988955202245954418725)
          ·
            refine ⟨34272185429100421116453511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182784988955202245954418725 34272185429100421116453511)
            ·
              refine ⟨51408278143650631674680267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34272185429100421116453511 51408278143650631674680267)
              ·
                refine ⟨77112417215475947512020401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51408278143650631674680267 77112417215475947512020401)
                ·
                  refine ⟨57834312911606960634015301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77112417215475947512020401 57834312911606960634015301)
                  ·
                    refine ⟨10843933670926305118877869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57834312911606960634015301 10843933670926305118877869)
                    ·
                      refine ⟨4066475126597364419579201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10843933670926305118877869 4066475126597364419579201)
                      ·
                        rfl

theorem cell23_7919432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_7919432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919432 prefixEnd_7919432 := by exact prefixLift 7919432
  have htrace : WordTrace (prefixWord ++ tailWord_7919432) baseStart_7919432 baseEnd_7919432 := by
    simpa [prefixWord, tailWord_7919432, baseEnd_7919432] using wordTrace_append hprefix tailTrace_7919432
  have hstable : (prefixWord ++ tailWord_7919432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919432).length < 2 ^ (prefixWord ++ tailWord_7919432).sum := by decide
  have hdescent : baseEnd_7919432 < baseStart_7919432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919442 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_7919442 : Nat := 118140960795 + 7919442 * 2 ^ 59
def prefixEnd_7919442 : Nat := 4983230072969 + 3 ^ 40 * 7919442 * 2
def baseEnd_7919442 : Nat := 4066480261403909380454155

theorem tailTrace_7919442 : CollatzResearch.WordTrace tailWord_7919442 prefixEnd_7919442 4066480261403909380454155 := by
  unfold tailWord_7919442
  simp only [CollatzResearch.WordTrace]
  refine ⟨72211444843805410464514145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192563852916814427905371053 72211444843805410464514145)
  ·
    refine ⟨54158583632854057848385609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72211444843805410464514145 54158583632854057848385609)
    ·
      refine ⟨40618937724640543386289207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54158583632854057848385609 40618937724640543386289207)
      ·
        refine ⟨60928406586960815079433811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40618937724640543386289207 60928406586960815079433811)
        ·
          refine ⟨91392609880441222619150717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60928406586960815079433811 91392609880441222619150717)
          ·
            refine ⟨34272228705165458482181519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91392609880441222619150717 34272228705165458482181519)
            ·
              refine ⟨51408343057748187723272279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34272228705165458482181519 51408343057748187723272279)
              ·
                refine ⟨77112514586622281584908419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51408343057748187723272279 77112514586622281584908419)
                ·
                  refine ⟨115668771879933422377362629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77112514586622281584908419 115668771879933422377362629)
                  ·
                    refine ⟨21687894727487516695755493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115668771879933422377362629 21687894727487516695755493)
                    ·
                      refine ⟨4066480261403909380454155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21687894727487516695755493 4066480261403909380454155)
                      ·
                        rfl

theorem cell23_7919442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_7919442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919442 prefixEnd_7919442 := by exact prefixLift 7919442
  have htrace : WordTrace (prefixWord ++ tailWord_7919442) baseStart_7919442 baseEnd_7919442 := by
    simpa [prefixWord, tailWord_7919442, baseEnd_7919442] using wordTrace_append hprefix tailTrace_7919442
  have hstable : (prefixWord ++ tailWord_7919442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919442).length < 2 ^ (prefixWord ++ tailWord_7919442).sum := by decide
  have hdescent : baseEnd_7919442 < baseStart_7919442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919469 : List Nat := [1, 5, 1, 1, 1, 1, 3, 5, 5]
def baseStart_7919469 : Nat := 118140960795 + 7919469 * 2 ^ 59
def prefixEnd_7919469 : Nat := 4983230072969 + 3 ^ 40 * 7919469 * 2
def baseEnd_7919469 : Nat := 451832680597953419424059

theorem tailTrace_7919469 : CollatzResearch.WordTrace tailWord_7919469 prefixEnd_7919469 451832680597953419424059 := by
  unfold tailWord_7919469
  simp only [CollatzResearch.WordTrace]
  refine ⟨288846764146123825469289461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192564509430749216979526307 288846764146123825469289461)
  ·
    refine ⟨27079384138699108637745887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288846764146123825469289461 27079384138699108637745887)
    ·
      refine ⟨40619076208048662956618831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27079384138699108637745887 40619076208048662956618831)
      ·
        refine ⟨60928614312072994434928247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40619076208048662956618831 60928614312072994434928247)
        ·
          refine ⟨91392921468109491652392371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60928614312072994434928247 91392921468109491652392371)
          ·
            refine ⟨137089382202164237478588557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91392921468109491652392371 137089382202164237478588557)
            ·
              refine ⟨51408518325811589054470709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137089382202164237478588557 51408518325811589054470709)
              ·
                refine ⟨4819548593044836473856629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51408518325811589054470709 4819548593044836473856629)
                ·
                  refine ⟨451832680597953419424059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4819548593044836473856629 451832680597953419424059)
                  ·
                    rfl

theorem cell23_7919469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_7919469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919469 prefixEnd_7919469 := by exact prefixLift 7919469
  have htrace : WordTrace (prefixWord ++ tailWord_7919469) baseStart_7919469 baseEnd_7919469 := by
    simpa [prefixWord, tailWord_7919469, baseEnd_7919469] using wordTrace_append hprefix tailTrace_7919469
  have hstable : (prefixWord ++ tailWord_7919469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919469).length < 2 ^ (prefixWord ++ tailWord_7919469).sum := by decide
  have hdescent : baseEnd_7919469 < baseStart_7919469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919482 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_7919482 : Nat := 118140960795 + 7919482 * 2 ^ 59
def prefixEnd_7919482 : Nat := 4983230072969 + 3 ^ 40 * 7919482 * 2
def baseEnd_7919482 : Nat := 1355500266876696407984657

theorem tailTrace_7919482 : CollatzResearch.WordTrace tailWord_7919482 prefixEnd_7919482 1355500266876696407984657 := by
  unfold tailWord_7919482
  simp only [CollatzResearch.WordTrace]
  refine ⟨72211809573769182172378175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192564825530051152459675133 72211809573769182172378175)
  ·
    refine ⟨108317714360653773258567263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72211809573769182172378175 108317714360653773258567263)
    ·
      refine ⟨162476571540980659887850895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108317714360653773258567263 162476571540980659887850895)
      ·
        refine ⟨243714857311470989831776343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162476571540980659887850895 243714857311470989831776343)
        ·
          refine ⟨365572285967206484747664515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243714857311470989831776343 365572285967206484747664515)
          ·
            refine ⟨548358428950809727121496773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365572285967206484747664515 548358428950809727121496773)
            ·
              refine ⟨102817205428276823835280645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 548358428950809727121496773 102817205428276823835280645)
              ·
                refine ⟨19278226017801904469115121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102817205428276823835280645 19278226017801904469115121)
                ·
                  refine ⟨14458669513351428351836341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19278226017801904469115121 14458669513351428351836341)
                  ·
                    refine ⟨1355500266876696407984657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14458669513351428351836341 1355500266876696407984657)
                    ·
                      rfl

theorem cell23_7919482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_7919482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919482 prefixEnd_7919482 := by exact prefixLift 7919482
  have htrace : WordTrace (prefixWord ++ tailWord_7919482) baseStart_7919482 baseEnd_7919482 := by
    simpa [prefixWord, tailWord_7919482, baseEnd_7919482] using wordTrace_append hprefix tailTrace_7919482
  have hstable : (prefixWord ++ tailWord_7919482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919482).length < 2 ^ (prefixWord ++ tailWord_7919482).sum := by decide
  have hdescent : baseEnd_7919482 < baseStart_7919482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919486 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_7919486 : Nat := 118140960795 + 7919486 * 2 ^ 59
def prefixEnd_7919486 : Nat := 4983230072969 + 3 ^ 40 * 7919486 * 2
def baseEnd_7919486 : Nat := 451833650505856356478217

theorem tailTrace_7919486 : CollatzResearch.WordTrace tailWord_7919486 prefixEnd_7919486 451833650505856356478217 := by
  unfold tailWord_7919486
  simp only [CollatzResearch.WordTrace]
  refine ⟨36105923023382779671582289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192564922791374824915105541 36105923023382779671582289)
  ·
    refine ⟨27079442267537084753686717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36105923023382779671582289 27079442267537084753686717)
    ·
      refine ⟨10154790850326406782632519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27079442267537084753686717 10154790850326406782632519)
      ·
        refine ⟨15232186275489610173948779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10154790850326406782632519 15232186275489610173948779)
        ·
          refine ⟨22848279413234415260923169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15232186275489610173948779 22848279413234415260923169)
          ·
            refine ⟨17136209559925811445692377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22848279413234415260923169 17136209559925811445692377)
            ·
              refine ⟨12852157169944358584269283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17136209559925811445692377 12852157169944358584269283)
              ·
                refine ⟨19278235754916537876403925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12852157169944358584269283 19278235754916537876403925)
                ·
                  refine ⟨451833650505856356478217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19278235754916537876403925 451833650505856356478217)
                  ·
                    rfl

theorem cell23_7919486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_7919486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919486 prefixEnd_7919486 := by exact prefixLift 7919486
  have htrace : WordTrace (prefixWord ++ tailWord_7919486) baseStart_7919486 baseEnd_7919486 := by
    simpa [prefixWord, tailWord_7919486, baseEnd_7919486] using wordTrace_append hprefix tailTrace_7919486
  have hstable : (prefixWord ++ tailWord_7919486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919486).length < 2 ^ (prefixWord ++ tailWord_7919486).sum := by decide
  have hdescent : baseEnd_7919486 < baseStart_7919486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919492 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_7919492 : Nat := 118140960795 + 7919492 * 2 ^ 59
def prefixEnd_7919492 : Nat := 4983230072969 + 3 ^ 40 * 7919492 * 2
def baseEnd_7919492 : Nat := 4066505935436634184828925

theorem tailTrace_7919492 : CollatzResearch.WordTrace tailWord_7919492 prefixEnd_7919492 4066505935436634184828925 := by
  unfold tailWord_7919492
  simp only [CollatzResearch.WordTrace]
  refine ⟨144423801512520250198688365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192565068683360333598251153 144423801512520250198688365)
  ·
    refine ⟨54158925567195093824508137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144423801512520250198688365 54158925567195093824508137)
    ·
      refine ⟨40619194175396320368381103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54158925567195093824508137 40619194175396320368381103)
      ·
        refine ⟨60928791263094480552571655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40619194175396320368381103 60928791263094480552571655)
        ·
          refine ⟨91393186894641720828857483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60928791263094480552571655 91393186894641720828857483)
          ·
            refine ⟨137089780341962581243286225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91393186894641720828857483 137089780341962581243286225)
            ·
              refine ⟨102817335256471935932464669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137089780341962581243286225 102817335256471935932464669)
              ·
                refine ⟨38556500721176975974674251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102817335256471935932464669 38556500721176975974674251)
                ·
                  refine ⟨57834751081765463962011377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38556500721176975974674251 57834751081765463962011377)
                  ·
                    refine ⟨43376063311324097971508533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57834751081765463962011377 43376063311324097971508533)
                    ·
                      refine ⟨4066505935436634184828925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43376063311324097971508533 4066505935436634184828925)
                      ·
                        rfl

theorem cell23_7919492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_7919492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919492 prefixEnd_7919492 := by exact prefixLift 7919492
  have htrace : WordTrace (prefixWord ++ tailWord_7919492) baseStart_7919492 baseEnd_7919492 := by
    simpa [prefixWord, tailWord_7919492, baseEnd_7919492] using wordTrace_append hprefix tailTrace_7919492
  have hstable : (prefixWord ++ tailWord_7919492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919492).length < 2 ^ (prefixWord ++ tailWord_7919492).sum := by decide
  have hdescent : baseEnd_7919492 < baseStart_7919492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919539 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 3]
def baseStart_7919539 : Nat := 118140960795 + 7919539 * 2 ^ 59
def prefixEnd_7919539 : Nat := 4983230072969 + 3 ^ 40 * 7919539 * 2
def baseEnd_7919539 : Nat := 4066530069027395500941209

theorem tailTrace_7919539 : CollatzResearch.WordTrace tailWord_7919539 prefixEnd_7919539 4066530069027395500941209 := by
  unfold tailWord_7919539
  simp only [CollatzResearch.WordTrace]
  refine ⟨288849317255870227424337671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192566211503913484949558447 288849317255870227424337671)
  ·
    refine ⟨433273975883805341136506507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288849317255870227424337671 433273975883805341136506507)
    ·
      refine ⟨649910963825708011704759761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433273975883805341136506507 649910963825708011704759761)
      ·
        refine ⟨487433222869281008778569821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649910963825708011704759761 487433222869281008778569821)
        ·
          refine ⟨182787458575980378291963683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487433222869281008778569821 182787458575980378291963683)
          ·
            refine ⟨274181187863970567437945525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182787458575980378291963683 274181187863970567437945525)
            ·
              refine ⟨25704486362247240697307393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274181187863970567437945525 25704486362247240697307393)
              ·
                refine ⟨19278364771685430522980545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25704486362247240697307393 19278364771685430522980545)
                ·
                  refine ⟨14458773578764072892235409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19278364771685430522980545 14458773578764072892235409)
                  ·
                    refine ⟨10844080184073054669176557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14458773578764072892235409 10844080184073054669176557)
                    ·
                      refine ⟨4066530069027395500941209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10844080184073054669176557 4066530069027395500941209)
                      ·
                        rfl

theorem cell23_7919539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 3].length) (baseStart_7919539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919539 prefixEnd_7919539 := by exact prefixLift 7919539
  have htrace : WordTrace (prefixWord ++ tailWord_7919539) baseStart_7919539 baseEnd_7919539 := by
    simpa [prefixWord, tailWord_7919539, baseEnd_7919539] using wordTrace_append hprefix tailTrace_7919539
  have hstable : (prefixWord ++ tailWord_7919539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919539).length < 2 ^ (prefixWord ++ tailWord_7919539).sum := by decide
  have hdescent : baseEnd_7919539 < baseStart_7919539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919562 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_7919562 : Nat := 118140960795 + 7919562 * 2 ^ 59
def prefixEnd_7919562 : Nat := 4983230072969 + 3 ^ 40 * 7919562 * 2
def baseEnd_7919562 : Nat := 4066541879082448910953603

theorem tailTrace_7919562 : CollatzResearch.WordTrace tailWord_7919562 prefixEnd_7919562 4066541879082448910953603 := by
  unfold tailWord_7919562
  simp only [CollatzResearch.WordTrace]
  refine ⟨72212539033696725588106235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192566770756524601568283293 72212539033696725588106235)
  ·
    refine ⟨108318808550545088382159353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72212539033696725588106235 108318808550545088382159353)
    ·
      refine ⟨81239106412908816286619515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108318808550545088382159353 81239106412908816286619515)
      ·
        refine ⟨121858659619363224429929273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81239106412908816286619515 121858659619363224429929273)
        ·
          refine ⟨91393994714522418322446955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121858659619363224429929273 91393994714522418322446955)
          ·
            refine ⟨137090992071783627483670433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91393994714522418322446955 137090992071783627483670433)
            ·
              refine ⟨102818244053837720612752825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137090992071783627483670433 102818244053837720612752825)
              ·
                refine ⟨77113683040378290459564619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102818244053837720612752825 77113683040378290459564619)
                ·
                  refine ⟨115670524560567435689346929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77113683040378290459564619 115670524560567435689346929)
                  ·
                    refine ⟨86752893420425576767010197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115670524560567435689346929 86752893420425576767010197)
                    ·
                      refine ⟨4066541879082448910953603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86752893420425576767010197 4066541879082448910953603)
                      ·
                        rfl

theorem cell23_7919562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_7919562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919562 prefixEnd_7919562 := by exact prefixLift 7919562
  have htrace : WordTrace (prefixWord ++ tailWord_7919562) baseStart_7919562 baseEnd_7919562 := by
    simpa [prefixWord, tailWord_7919562, baseEnd_7919562] using wordTrace_append hprefix tailTrace_7919562
  have hstable : (prefixWord ++ tailWord_7919562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919562).length < 2 ^ (prefixWord ++ tailWord_7919562).sum := by decide
  have hdescent : baseEnd_7919562 < baseStart_7919562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919609 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 4]
def baseStart_7919609 : Nat := 118140960795 + 7919609 * 2 ^ 59
def prefixEnd_7919609 : Nat := 4983230072969 + 3 ^ 40 * 7919609 * 2
def baseEnd_7919609 : Nat := 4066566012673210227065887

theorem tailTrace_7919609 : CollatzResearch.WordTrace tailWord_7919609 prefixEnd_7919609 4066566012673210227065887 := by
  unfold tailWord_7919609
  simp only [CollatzResearch.WordTrace]
  refine ⟨288851870365616629379385881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192567913577077752919590587 288851870365616629379385881)
  ·
    refine ⟨216638902774212472034539411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288851870365616629379385881 216638902774212472034539411)
    ·
      refine ⟨324958354161318708051809117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216638902774212472034539411 324958354161318708051809117)
      ·
        refine ⟨121859382810494515519428419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324958354161318708051809117 121859382810494515519428419)
        ·
          refine ⟨182789074215741773279142629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121859382810494515519428419 182789074215741773279142629)
          ·
            refine ⟨34272951415451582489839243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182789074215741773279142629 34272951415451582489839243)
            ·
              refine ⟨51409427123177373734758865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34272951415451582489839243 51409427123177373734758865)
              ·
                refine ⟨38557070342383030301069149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51409427123177373734758865 38557070342383030301069149)
                ·
                  refine ⟨14458901378393636362900931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38557070342383030301069149 14458901378393636362900931)
                  ·
                    refine ⟨21688352067590454544351397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14458901378393636362900931 21688352067590454544351397)
                    ·
                      refine ⟨4066566012673210227065887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21688352067590454544351397 4066566012673210227065887)
                      ·
                        rfl

theorem cell23_7919609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_7919609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919609 prefixEnd_7919609 := by exact prefixLift 7919609
  have htrace : WordTrace (prefixWord ++ tailWord_7919609) baseStart_7919609 baseEnd_7919609 := by
    simpa [prefixWord, tailWord_7919609, baseEnd_7919609] using wordTrace_append hprefix tailTrace_7919609
  have hstable : (prefixWord ++ tailWord_7919609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919609).length < 2 ^ (prefixWord ++ tailWord_7919609).sum := by decide
  have hdescent : baseEnd_7919609 < baseStart_7919609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919620 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7919620 : Nat := 118140960795 + 7919620 * 2 ^ 59
def prefixEnd_7919620 : Nat := 4983230072969 + 3 ^ 40 * 7919620 * 2
def baseEnd_7919620 : Nat := 4066571660960409684028337

theorem tailTrace_7919620 : CollatzResearch.WordTrace tailWord_7919620 prefixEnd_7919620 4066571660960409684028337 := by
  unfold tailWord_7919620
  simp only [CollatzResearch.WordTrace]
  refine ⟨144426135784288389129018157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192568181045717852172024209 144426135784288389129018157)
  ·
    refine ⟨54159800919108145923381809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144426135784288389129018157 54159800919108145923381809)
    ·
      refine ⟨40619850689331109442536357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54159800919108145923381809 40619850689331109442536357)
      ·
        refine ⟨7616222004249583020475567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40619850689331109442536357 7616222004249583020475567)
        ·
          refine ⟨11424333006374374530713351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616222004249583020475567 11424333006374374530713351)
          ·
            refine ⟨17136499509561561796070027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11424333006374374530713351 17136499509561561796070027)
            ·
              refine ⟨25704749264342342694105041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17136499509561561796070027 25704749264342342694105041)
              ·
                refine ⟨19278561948256757020578781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25704749264342342694105041 19278561948256757020578781)
                ·
                  refine ⟨7229460730596283882717043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19278561948256757020578781 7229460730596283882717043)
                  ·
                    refine ⟨10844191095894425824075565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7229460730596283882717043 10844191095894425824075565)
                    ·
                      refine ⟨4066571660960409684028337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10844191095894425824075565 4066571660960409684028337)
                      ·
                        rfl

theorem cell23_7919620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7919620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919620 prefixEnd_7919620 := by exact prefixLift 7919620
  have htrace : WordTrace (prefixWord ++ tailWord_7919620) baseStart_7919620 baseEnd_7919620 := by
    simpa [prefixWord, tailWord_7919620, baseEnd_7919620] using wordTrace_append hprefix tailTrace_7919620
  have hstable : (prefixWord ++ tailWord_7919620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919620).length < 2 ^ (prefixWord ++ tailWord_7919620).sum := by decide
  have hdescent : baseEnd_7919620 < baseStart_7919620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919649 : List Nat := [1, 2, 3, 2, 4, 1, 10]
def baseStart_7919649 : Nat := 118140960795 + 7919649 * 2 ^ 59
def prefixEnd_7919649 : Nat := 4983230072969 + 3 ^ 40 * 7919649 * 2
def baseEnd_7919649 : Nat := 50204772245671482352663

theorem tailTrace_7919649 : CollatzResearch.WordTrace tailWord_7919649 prefixEnd_7919649 50204772245671482352663 := by
  unfold tailWord_7919649
  simp only [CollatzResearch.WordTrace]
  refine ⟨288853329285471716210842001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192568886190314477473894667 288853329285471716210842001)
  ·
    refine ⟨216639996964103787158131501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288853329285471716210842001 216639996964103787158131501)
    ·
      refine ⟨81239998861538920184299313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216639996964103787158131501 81239998861538920184299313)
      ·
        refine ⟨60929999146154190138224485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81239998861538920184299313 60929999146154190138224485)
        ·
          refine ⟨11424374839903910650917091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60929999146154190138224485 11424374839903910650917091)
          ·
            refine ⟨17136562259855865976375637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11424374839903910650917091 17136562259855865976375637)
            ·
              refine ⟨50204772245671482352663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17136562259855865976375637 50204772245671482352663)
              ·
                rfl

theorem cell23_7919649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 10].length) (baseStart_7919649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919649 prefixEnd_7919649 := by exact prefixLift 7919649
  have htrace : WordTrace (prefixWord ++ tailWord_7919649) baseStart_7919649 baseEnd_7919649 := by
    simpa [prefixWord, tailWord_7919649, baseEnd_7919649] using wordTrace_append hprefix tailTrace_7919649
  have hstable : (prefixWord ++ tailWord_7919649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919649).length < 2 ^ (prefixWord ++ tailWord_7919649).sum := by decide
  have hdescent : baseEnd_7919649 < baseStart_7919649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919653 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_7919653 : Nat := 118140960795 + 7919653 * 2 ^ 59
def prefixEnd_7919653 : Nat := 4983230072969 + 3 ^ 40 * 7919653 * 2
def baseEnd_7919653 : Nat := 1355529535274002684971895

theorem tailTrace_7919653 : CollatzResearch.WordTrace tailWord_7919653 prefixEnd_7919653 1355529535274002684971895 := by
  unfold tailWord_7919653
  simp only [CollatzResearch.WordTrace]
  refine ⟨288853475177457224893987613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192568983451638149929325075 288853475177457224893987613)
  ·
    refine ⟨108320053191546459335245355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288853475177457224893987613 108320053191546459335245355)
    ·
      refine ⟨162480079787319689002868033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108320053191546459335245355 162480079787319689002868033)
      ·
        refine ⟨121860059840489766752151025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162480079787319689002868033 121860059840489766752151025)
        ·
          refine ⟨91395044880367325064113269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121860059840489766752151025 91395044880367325064113269)
          ·
            refine ⟨8568285457534436724760619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91395044880367325064113269 8568285457534436724760619)
            ·
              refine ⟨12852428186301655087140929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568285457534436724760619 12852428186301655087140929)
              ·
                refine ⟨9639321139726241315355697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12852428186301655087140929 9639321139726241315355697)
                ·
                  refine ⟨7229490854794680986516773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9639321139726241315355697 7229490854794680986516773)
                  ·
                    refine ⟨1355529535274002684971895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7229490854794680986516773 1355529535274002684971895)
                    ·
                      rfl

theorem cell23_7919653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_7919653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919653 prefixEnd_7919653 := by exact prefixLift 7919653
  have htrace : WordTrace (prefixWord ++ tailWord_7919653) baseStart_7919653 baseEnd_7919653 := by
    simpa [prefixWord, tailWord_7919653, baseEnd_7919653] using wordTrace_append hprefix tailTrace_7919653
  have hstable : (prefixWord ++ tailWord_7919653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919653).length < 2 ^ (prefixWord ++ tailWord_7919653).sum := by decide
  have hdescent : baseEnd_7919653 < baseStart_7919653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919670 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_7919670 : Nat := 118140960795 + 7919670 * 2 ^ 59
def prefixEnd_7919670 : Nat := 4983230072969 + 3 ^ 40 * 7919670 * 2
def baseEnd_7919670 : Nat := 1355532444997711496134369

theorem tailTrace_7919670 : CollatzResearch.WordTrace tailWord_7919670 prefixEnd_7919670 1355532444997711496134369 := by
  unfold tailWord_7919670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053380951149727299834779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192569396812263757864904309 18053380951149727299834779)
  ·
    refine ⟨27080071426724590949752169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18053380951149727299834779 27080071426724590949752169)
    ·
      refine ⟨20310053570043443212314127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27080071426724590949752169 20310053570043443212314127)
      ·
        refine ⟨30465080355065164818471191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20310053570043443212314127 30465080355065164818471191)
        ·
          refine ⟨45697620532597747227706787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30465080355065164818471191 45697620532597747227706787)
          ·
            refine ⟨68546430798896620841560181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45697620532597747227706787 68546430798896620841560181)
            ·
              refine ⟨6426227887396558203896267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68546430798896620841560181 6426227887396558203896267)
              ·
                refine ⟨9639341831094837305844401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426227887396558203896267 9639341831094837305844401)
                ·
                  refine ⟨7229506373321127979383301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9639341831094837305844401 7229506373321127979383301)
                  ·
                    refine ⟨1355532444997711496134369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7229506373321127979383301 1355532444997711496134369)
                    ·
                      rfl

theorem cell23_7919670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_7919670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919670 prefixEnd_7919670 := by exact prefixLift 7919670
  have htrace : WordTrace (prefixWord ++ tailWord_7919670) baseStart_7919670 baseEnd_7919670 := by
    simpa [prefixWord, tailWord_7919670, baseEnd_7919670] using wordTrace_append hprefix tailTrace_7919670
  have hstable : (prefixWord ++ tailWord_7919670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919670).length < 2 ^ (prefixWord ++ tailWord_7919670).sum := by decide
  have hdescent : baseEnd_7919670 < baseStart_7919670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919673 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 4]
def baseStart_7919673 : Nat := 118140960795 + 7919673 * 2 ^ 59
def prefixEnd_7919673 : Nat := 4983230072969 + 3 ^ 40 * 7919673 * 2
def baseEnd_7919673 : Nat := 4066598875435097976665593

theorem tailTrace_7919673 : CollatzResearch.WordTrace tailWord_7919673 prefixEnd_7919673 4066598875435097976665593 := by
  unfold tailWord_7919673
  simp only [CollatzResearch.WordTrace]
  refine ⟨288854204637384768309715673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192569469758256512206477115 288854204637384768309715673)
  ·
    refine ⟨216640653478038576232286755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288854204637384768309715673 216640653478038576232286755)
    ·
      refine ⟨324960980217057864348430133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216640653478038576232286755 324960980217057864348430133)
      ·
        refine ⟨30465091895349174782665325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 324960980217057864348430133 30465091895349174782665325)
        ·
          refine ⟨11424409460755940543499497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30465091895349174782665325 11424409460755940543499497)
          ·
            refine ⟨8568307095566955407624623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11424409460755940543499497 8568307095566955407624623)
            ·
              refine ⟨12852460643350433111436935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568307095566955407624623 12852460643350433111436935)
              ·
                refine ⟨19278690965025649667155403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12852460643350433111436935 19278690965025649667155403)
                ·
                  refine ⟨28918036447538474500733105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19278690965025649667155403 28918036447538474500733105)
                  ·
                    refine ⟨21688527335653855875549829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28918036447538474500733105 21688527335653855875549829)
                    ·
                      refine ⟨4066598875435097976665593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21688527335653855875549829 4066598875435097976665593)
                      ·
                        rfl

theorem cell23_7919673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_7919673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919673 prefixEnd_7919673 := by exact prefixLift 7919673
  have htrace : WordTrace (prefixWord ++ tailWord_7919673) baseStart_7919673 baseEnd_7919673 := by
    simpa [prefixWord, tailWord_7919673, baseEnd_7919673] using wordTrace_append hprefix tailTrace_7919673
  have hstable : (prefixWord ++ tailWord_7919673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919673).length < 2 ^ (prefixWord ++ tailWord_7919673).sum := by decide
  have hdescent : baseEnd_7919673 < baseStart_7919673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919693 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_7919693 : Nat := 118140960795 + 7919693 * 2 ^ 59
def prefixEnd_7919693 : Nat := 4983230072969 + 3 ^ 40 * 7919693 * 2
def baseEnd_7919693 : Nat := 4066609145048187898415501

theorem tailTrace_7919693 : CollatzResearch.WordTrace tailWord_7919693 prefixEnd_7919693 4066609145048187898415501 := by
  unfold tailWord_7919693
  simp only [CollatzResearch.WordTrace]
  refine ⟨288854934097312311725443733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192569956064874874483629155 288854934097312311725443733)
  ·
    refine ⟨13540075035811514612130175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 288854934097312311725443733 13540075035811514612130175)
    ·
      refine ⟨20310112553717271918195263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13540075035811514612130175 20310112553717271918195263)
      ·
        refine ⟨30465168830575907877292895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20310112553717271918195263 30465168830575907877292895)
        ·
          refine ⟨45697753245863861815939343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30465168830575907877292895 45697753245863861815939343)
          ·
            refine ⟨68546629868795792723909015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45697753245863861815939343 68546629868795792723909015)
            ·
              refine ⟨102819944803193689085863523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68546629868795792723909015 102819944803193689085863523)
              ·
                refine ⟨154229917204790533628795285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102819944803193689085863523 154229917204790533628795285)
                ·
                  refine ⟨7229527368974556263849779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154229917204790533628795285 7229527368974556263849779)
                  ·
                    refine ⟨10844291053461834395774669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7229527368974556263849779 10844291053461834395774669)
                    ·
                      refine ⟨4066609145048187898415501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10844291053461834395774669 4066609145048187898415501)
                      ·
                        rfl

theorem cell23_7919693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_7919693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919693 prefixEnd_7919693 := by exact prefixLift 7919693
  have htrace : WordTrace (prefixWord ++ tailWord_7919693) baseStart_7919693 baseEnd_7919693 := by
    simpa [prefixWord, tailWord_7919693, baseEnd_7919693] using wordTrace_append hprefix tailTrace_7919693
  have hstable : (prefixWord ++ tailWord_7919693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919693).length < 2 ^ (prefixWord ++ tailWord_7919693).sum := by decide
  have hdescent : baseEnd_7919693 < baseStart_7919693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919703 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 1, 3, 2]
def baseStart_7919703 : Nat := 118140960795 + 7919703 * 2 ^ 59
def prefixEnd_7919703 : Nat := 4983230072969 + 3 ^ 40 * 7919703 * 2
def baseEnd_7919703 : Nat := 4066614279854732859290455

theorem tailTrace_7919703 : CollatzResearch.WordTrace tailWord_7919703 prefixEnd_7919703 4066614279854732859290455 := by
  unfold tailWord_7919703
  simp only [CollatzResearch.WordTrace]
  refine ⟨288855298827276083433307763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192570199218184055622205175 288855298827276083433307763)
  ·
    refine ⟨433282948240914125149961645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288855298827276083433307763 433282948240914125149961645)
    ·
      refine ⟨162481105590342796931235617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433282948240914125149961645 162481105590342796931235617)
      ·
        refine ⟨121860829192757097698426713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162481105590342796931235617 121860829192757097698426713)
        ·
          refine ⟨91395621894567823273820035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121860829192757097698426713 91395621894567823273820035)
          ·
            refine ⟨137093432841851734910730053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91395621894567823273820035 137093432841851734910730053)
            ·
              refine ⟨25705018657847200295761885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137093432841851734910730053 25705018657847200295761885)
              ·
                refine ⟨9639381996692700110910707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25705018657847200295761885 9639381996692700110910707)
                ·
                  refine ⟨14459072995039050166366061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9639381996692700110910707 14459072995039050166366061)
                  ·
                    refine ⟨5422152373139643812387273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14459072995039050166366061 5422152373139643812387273)
                    ·
                      refine ⟨4066614279854732859290455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5422152373139643812387273 4066614279854732859290455)
                      ·
                        rfl

theorem cell23_7919703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_7919703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919703 prefixEnd_7919703 := by exact prefixLift 7919703
  have htrace : WordTrace (prefixWord ++ tailWord_7919703) baseStart_7919703 baseEnd_7919703 := by
    simpa [prefixWord, tailWord_7919703, baseEnd_7919703] using wordTrace_append hprefix tailTrace_7919703
  have hstable : (prefixWord ++ tailWord_7919703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919703).length < 2 ^ (prefixWord ++ tailWord_7919703).sum := by decide
  have hdescent : baseEnd_7919703 < baseStart_7919703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919719 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_7919719 : Nat := 118140960795 + 7919719 * 2 ^ 59
def prefixEnd_7919719 : Nat := 4983230072969 + 3 ^ 40 * 7919719 * 2
def baseEnd_7919719 : Nat := 4066622495545204796690381

theorem tailTrace_7919719 : CollatzResearch.WordTrace tailWord_7919719 prefixEnd_7919719 4066622495545204796690381 := by
  unfold tailWord_7919719
  simp only [CollatzResearch.WordTrace]
  refine ⟨288855882395218118165890211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192570588263478745443926807 288855882395218118165890211)
  ·
    refine ⟨433283823592827177248835317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288855882395218118165890211 433283823592827177248835317)
    ·
      refine ⟨40620358461827547867078311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 433283823592827177248835317 40620358461827547867078311)
      ·
        refine ⟨60930537692741321800617467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40620358461827547867078311 60930537692741321800617467)
        ·
          refine ⟨91395806539111982700926201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60930537692741321800617467 91395806539111982700926201)
          ·
            refine ⟨68546854904333987025694651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91395806539111982700926201 68546854904333987025694651)
            ·
              refine ⟨102820282356500980538541977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68546854904333987025694651 102820282356500980538541977)
              ·
                refine ⟨77115211767375735403906483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102820282356500980538541977 77115211767375735403906483)
                ·
                  refine ⟨115672817651063603105859725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77115211767375735403906483 115672817651063603105859725)
                  ·
                    refine ⟨43377306619148851164697397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115672817651063603105859725 43377306619148851164697397)
                    ·
                      refine ⟨4066622495545204796690381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43377306619148851164697397 4066622495545204796690381)
                      ·
                        rfl

theorem cell23_7919719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_7919719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919719 prefixEnd_7919719 := by exact prefixLift 7919719
  have htrace : WordTrace (prefixWord ++ tailWord_7919719) baseStart_7919719 baseEnd_7919719 := by
    simpa [prefixWord, tailWord_7919719, baseEnd_7919719] using wordTrace_append hprefix tailTrace_7919719
  have hstable : (prefixWord ++ tailWord_7919719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919719).length < 2 ^ (prefixWord ++ tailWord_7919719).sum := by decide
  have hdescent : baseEnd_7919719 < baseStart_7919719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919729 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_7919729 : Nat := 118140960795 + 7919729 * 2 ^ 59
def prefixEnd_7919729 : Nat := 4983230072969 + 3 ^ 40 * 7919729 * 2
def baseEnd_7919729 : Nat := 4066627630351749757565335

theorem tailTrace_7919729 : CollatzResearch.WordTrace tailWord_7919729 prefixEnd_7919729 4066627630351749757565335 := by
  unfold tailWord_7919729
  simp only [CollatzResearch.WordTrace]
  refine ⟨288856247125181889873754241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192570831416787926582502827 288856247125181889873754241)
  ·
    refine ⟨216642185343886417405315681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288856247125181889873754241 216642185343886417405315681)
    ·
      refine ⟨162481639007914813053986761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216642185343886417405315681 162481639007914813053986761)
      ·
        refine ⟨121861229255936109790490071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162481639007914813053986761 121861229255936109790490071)
        ·
          refine ⟨182791843883904164685735107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121861229255936109790490071 182791843883904164685735107)
          ·
            refine ⟨274187765825856247028602661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182791843883904164685735107 274187765825856247028602661)
            ·
              refine ⟨51410206092348046317862999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274187765825856247028602661 51410206092348046317862999)
              ·
                refine ⟨77115309138522069476794499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51410206092348046317862999 77115309138522069476794499)
                ·
                  refine ⟨115672963707783104215191749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77115309138522069476794499 115672963707783104215191749)
                  ·
                    refine ⟨21688680695209332040348453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115672963707783104215191749 21688680695209332040348453)
                    ·
                      refine ⟨4066627630351749757565335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21688680695209332040348453 4066627630351749757565335)
                      ·
                        rfl

theorem cell23_7919729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_7919729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919729 prefixEnd_7919729 := by exact prefixLift 7919729
  have htrace : WordTrace (prefixWord ++ tailWord_7919729) baseStart_7919729 baseEnd_7919729 := by
    simpa [prefixWord, tailWord_7919729, baseEnd_7919729] using wordTrace_append hprefix tailTrace_7919729
  have hstable : (prefixWord ++ tailWord_7919729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919729).length < 2 ^ (prefixWord ++ tailWord_7919729).sum := by decide
  have hdescent : baseEnd_7919729 < baseStart_7919729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919767 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 2, 2, 2]
def baseStart_7919767 : Nat := 118140960795 + 7919767 * 2 ^ 59
def prefixEnd_7919767 : Nat := 4983230072969 + 3 ^ 40 * 7919767 * 2
def baseEnd_7919767 : Nat := 4066647142616620608890161

theorem tailTrace_7919767 : CollatzResearch.WordTrace tailWord_7919767 prefixEnd_7919767 4066647142616620608890161 := by
  unfold tailWord_7919767
  simp only [CollatzResearch.WordTrace]
  refine ⟨288857633099044222363637555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192571755399362814909091703 288857633099044222363637555)
  ·
    refine ⟨433286449648566333545456333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288857633099044222363637555 433286449648566333545456333)
    ·
      refine ⟨162482418618212375079546125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433286449648566333545456333 162482418618212375079546125)
      ·
        refine ⟨60930906981829640654829797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162482418618212375079546125 60930906981829640654829797)
        ·
          refine ⟨11424545059093057622780587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60930906981829640654829797 11424545059093057622780587)
          ·
            refine ⟨17136817588639586434170881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11424545059093057622780587 17136817588639586434170881)
            ·
              refine ⟨12852613191479689825628161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17136817588639586434170881 12852613191479689825628161)
              ·
                refine ⟨9639459893609767369221121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12852613191479689825628161 9639459893609767369221121)
                ·
                  refine ⟨7229594920207325526915841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9639459893609767369221121 7229594920207325526915841)
                  ·
                    refine ⟨5422196190155494145186881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7229594920207325526915841 5422196190155494145186881)
                    ·
                      refine ⟨4066647142616620608890161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5422196190155494145186881 4066647142616620608890161)
                      ·
                        rfl

theorem cell23_7919767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_7919767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919767 prefixEnd_7919767 := by exact prefixLift 7919767
  have htrace : WordTrace (prefixWord ++ tailWord_7919767) baseStart_7919767 baseEnd_7919767 := by
    simpa [prefixWord, tailWord_7919767, baseEnd_7919767] using wordTrace_append hprefix tailTrace_7919767
  have hstable : (prefixWord ++ tailWord_7919767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919767).length < 2 ^ (prefixWord ++ tailWord_7919767).sum := by decide
  have hdescent : baseEnd_7919767 < baseStart_7919767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919773 : List Nat := [1, 4, 2, 1, 1, 4, 1, 4, 5]
def baseStart_7919773 : Nat := 118140960795 + 7919773 * 2 ^ 59
def prefixEnd_7919773 : Nat := 4983230072969 + 3 ^ 40 * 7919773 * 2
def baseEnd_7919773 : Nat := 451850024833394176157237

theorem tailTrace_7919773 : CollatzResearch.WordTrace tailWord_7919773 prefixEnd_7919773 451850024833394176157237 := by
  unfold tailWord_7919773
  simp only [CollatzResearch.WordTrace]
  refine ⟨288857851937022485388355973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192571901291348323592237315 288857851937022485388355973)
  ·
    refine ⟨54160847238191716010316745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288857851937022485388355973 54160847238191716010316745)
    ·
      refine ⟨40620635428643787007737559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54160847238191716010316745 40620635428643787007737559)
      ·
        refine ⟨60930953142965680511606339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40620635428643787007737559 60930953142965680511606339)
        ·
          refine ⟨91396429714448520767409509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60930953142965680511606339 91396429714448520767409509)
          ·
            refine ⟨17136830571459097643889283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91396429714448520767409509 17136830571459097643889283)
            ·
              refine ⟨25705245857188646465833925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17136830571459097643889283 25705245857188646465833925)
              ·
                refine ⟨4819733598222871212343861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25705245857188646465833925 4819733598222871212343861)
                ·
                  refine ⟨451850024833394176157237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4819733598222871212343861 451850024833394176157237)
                  ·
                    rfl

theorem cell23_7919773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_7919773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919773 prefixEnd_7919773 := by exact prefixLift 7919773
  have htrace : WordTrace (prefixWord ++ tailWord_7919773) baseStart_7919773 baseEnd_7919773 := by
    simpa [prefixWord, tailWord_7919773, baseEnd_7919773] using wordTrace_append hprefix tailTrace_7919773
  have hstable : (prefixWord ++ tailWord_7919773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919773).length < 2 ^ (prefixWord ++ tailWord_7919773).sum := by decide
  have hdescent : baseEnd_7919773 < baseStart_7919773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919790 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_7919790 : Nat := 118140960795 + 7919790 * 2 ^ 59
def prefixEnd_7919790 : Nat := 4983230072969 + 3 ^ 40 * 7919790 * 2
def baseEnd_7919790 : Nat := 451850994741297113211395

theorem tailTrace_7919790 : CollatzResearch.WordTrace tailWord_7919790 prefixEnd_7919790 451850994741297113211395 := by
  unfold tailWord_7919790
  simp only [CollatzResearch.WordTrace]
  refine ⟨36107308997245112161465603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192572314651973931527816549 36107308997245112161465603)
  ·
    refine ⟨54160963495867668242198405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36107308997245112161465603 54160963495867668242198405)
    ·
      refine ⟨10155180655475187795412201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54160963495867668242198405 10155180655475187795412201)
      ·
        refine ⟨7616385491606390846559151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10155180655475187795412201 7616385491606390846559151)
        ·
          refine ⟨11424578237409586269838727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616385491606390846559151 11424578237409586269838727)
          ·
            refine ⟨17136867356114379404758091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11424578237409586269838727 17136867356114379404758091)
            ·
              refine ⟨25705301034171569107137137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17136867356114379404758091 25705301034171569107137137)
              ·
                refine ⟨19278975775628676830352853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25705301034171569107137137 19278975775628676830352853)
                ·
                  refine ⟨451850994741297113211395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19278975775628676830352853 451850994741297113211395)
                  ·
                    rfl

theorem cell23_7919790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_7919790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919790 prefixEnd_7919790 := by exact prefixLift 7919790
  have htrace : WordTrace (prefixWord ++ tailWord_7919790) baseStart_7919790 baseEnd_7919790 := by
    simpa [prefixWord, tailWord_7919790, baseEnd_7919790] using wordTrace_append hprefix tailTrace_7919790
  have hstable : (prefixWord ++ tailWord_7919790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919790).length < 2 ^ (prefixWord ++ tailWord_7919790).sum := by decide
  have hdescent : baseEnd_7919790 < baseStart_7919790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919816 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 7, 4]
def baseStart_7919816 : Nat := 118140960795 + 7919816 * 2 ^ 59
def prefixEnd_7919816 : Nat := 4983230072969 + 3 ^ 40 * 7919816 * 2
def baseEnd_7919816 : Nat := 1355557434389563639059145

theorem tailTrace_7919816 : CollatzResearch.WordTrace tailWord_7919816 prefixEnd_7919816 1355557434389563639059145 := by
  unfold tailWord_7919816
  simp only [CollatzResearch.WordTrace]
  refine ⟨144429710137933351866085651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192572946850577802488114201 144429710137933351866085651)
  ·
    refine ⟨216644565206900027799128477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144429710137933351866085651 216644565206900027799128477)
    ·
      refine ⟨81241711952587510424673179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216644565206900027799128477 81241711952587510424673179)
      ·
        refine ⟨121862567928881265637009769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81241711952587510424673179 121862567928881265637009769)
        ·
          refine ⟨91396925946660949227757327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121862567928881265637009769 91396925946660949227757327)
          ·
            refine ⟨137095388919991423841635991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91396925946660949227757327 137095388919991423841635991)
            ·
              refine ⟨205643083379987135762453987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137095388919991423841635991 205643083379987135762453987)
              ·
                refine ⟨308464625069980703643680981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205643083379987135762453987 308464625069980703643680981)
                ·
                  refine ⟨7229639650077672741648773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 308464625069980703643680981 7229639650077672741648773)
                  ·
                    refine ⟨1355557434389563639059145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7229639650077672741648773 1355557434389563639059145)
                    ·
                      rfl

theorem cell23_7919816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_7919816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919816 prefixEnd_7919816 := by exact prefixLift 7919816
  have htrace : WordTrace (prefixWord ++ tailWord_7919816) baseStart_7919816 baseEnd_7919816 := by
    simpa [prefixWord, tailWord_7919816, baseEnd_7919816] using wordTrace_append hprefix tailTrace_7919816
  have hstable : (prefixWord ++ tailWord_7919816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919816).length < 2 ^ (prefixWord ++ tailWord_7919816).sum := by decide
  have hdescent : baseEnd_7919816 < baseStart_7919816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919819 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 6]
def baseStart_7919819 : Nat := 118140960795 + 7919819 * 2 ^ 59
def prefixEnd_7919819 : Nat := 4983230072969 + 3 ^ 40 * 7919819 * 2
def baseEnd_7919819 : Nat := 4066673843610654405439921

theorem tailTrace_7919819 : CollatzResearch.WordTrace tailWord_7919819 prefixEnd_7919819 4066673843610654405439921 := by
  unfold tailWord_7919819
  simp only [CollatzResearch.WordTrace]
  refine ⟨288859529694855835244530511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192573019796570556829687007 288859529694855835244530511)
  ·
    refine ⟨433289294542283752866795767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288859529694855835244530511 433289294542283752866795767)
    ·
      refine ⟨649933941813425629300193651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433289294542283752866795767 649933941813425629300193651)
      ·
        refine ⟨974900912720138443950290477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649933941813425629300193651 974900912720138443950290477)
        ·
          refine ⟨365587842270051916481358929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 974900912720138443950290477 365587842270051916481358929)
          ·
            refine ⟨274190881702538937361019197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365587842270051916481358929 274190881702538937361019197)
            ·
              refine ⟨102821580638452101510382199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274190881702538937361019197 102821580638452101510382199)
              ·
                refine ⟨154232370957678152265573299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102821580638452101510382199 154232370957678152265573299)
                ·
                  refine ⟨231348556436517228398359949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154232370957678152265573299 231348556436517228398359949)
                  ·
                    refine ⟨86755708663693960649384981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231348556436517228398359949 86755708663693960649384981)
                    ·
                      refine ⟨4066673843610654405439921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86755708663693960649384981 4066673843610654405439921)
                      ·
                        rfl

theorem cell23_7919819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_7919819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919819 prefixEnd_7919819 := by exact prefixLift 7919819
  have htrace : WordTrace (prefixWord ++ tailWord_7919819) baseStart_7919819 baseEnd_7919819 := by
    simpa [prefixWord, tailWord_7919819, baseEnd_7919819] using wordTrace_append hprefix tailTrace_7919819
  have hstable : (prefixWord ++ tailWord_7919819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919819).length < 2 ^ (prefixWord ++ tailWord_7919819).sum := by decide
  have hdescent : baseEnd_7919819 < baseStart_7919819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919916 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_7919916 : Nat := 118140960795 + 7919916 * 2 ^ 59
def prefixEnd_7919916 : Nat := 4983230072969 + 3 ^ 40 * 7919916 * 2
def baseEnd_7919916 : Nat := 4066723651234140525926975

theorem tailTrace_7919916 : CollatzResearch.WordTrace tailWord_7919916 prefixEnd_7919916 4066723651234140525926975 := by
  unfold tailWord_7919916
  simp only [CollatzResearch.WordTrace]
  refine ⟨144431533787752210405405801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192575378383669613873874401 144431533787752210405405801)
  ·
    refine ⟨108323650340814157804054351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144431533787752210405405801 108323650340814157804054351)
    ·
      refine ⟨162485475511221236706081527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108323650340814157804054351 162485475511221236706081527)
      ·
        refine ⟨243728213266831855059122291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162485475511221236706081527 243728213266831855059122291)
        ·
          refine ⟨365592319900247782588683437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243728213266831855059122291 365592319900247782588683437)
          ·
            refine ⟨137097119962592918470756289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365592319900247782588683437 137097119962592918470756289)
            ·
              refine ⟨102822839971944688853067217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137097119962592918470756289 102822839971944688853067217)
              ·
                refine ⟨77117129978958516639800413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102822839971944688853067217 77117129978958516639800413)
                ·
                  refine ⟨28918923742109443739925155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77117129978958516639800413 28918923742109443739925155)
                  ·
                    refine ⟨43378385613164165609887733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28918923742109443739925155 43378385613164165609887733)
                    ·
                      refine ⟨4066723651234140525926975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43378385613164165609887733 4066723651234140525926975)
                      ·
                        rfl

theorem cell23_7919916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_7919916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919916 prefixEnd_7919916 := by exact prefixLift 7919916
  have htrace : WordTrace (prefixWord ++ tailWord_7919916) baseStart_7919916 baseEnd_7919916 := by
    simpa [prefixWord, tailWord_7919916, baseEnd_7919916] using wordTrace_append hprefix tailTrace_7919916
  have hstable : (prefixWord ++ tailWord_7919916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919916).length < 2 ^ (prefixWord ++ tailWord_7919916).sum := by decide
  have hdescent : baseEnd_7919916 < baseStart_7919916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919953 : List Nat := [1, 2, 2, 1, 4, 4, 1, 8]
def baseStart_7919953 : Nat := 118140960795 + 7919953 * 2 ^ 59
def prefixEnd_7919953 : Nat := 4983230072969 + 3 ^ 40 * 7919953 * 2
def baseEnd_7919953 : Nat := 150620098148828032635715

theorem tailTrace_7919953 : CollatzResearch.WordTrace tailWord_7919953 prefixEnd_7919953 150620098148828032635715 := by
  unfold tailWord_7919953
  simp only [CollatzResearch.WordTrace]
  refine ⟨288864417076370376129908513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192576278050913584086605675 288864417076370376129908513)
  ·
    refine ⟨216648312807277782097431385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288864417076370376129908513 216648312807277782097431385)
    ·
      refine ⟨162486234605458336573073539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216648312807277782097431385 162486234605458336573073539)
      ·
        refine ⟨243729351908187504859610309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162486234605458336573073539 243729351908187504859610309)
        ·
          refine ⟨45699253482785157161176933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243729351908187504859610309 45699253482785157161176933)
          ·
            refine ⟨8568610028022216967720675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45699253482785157161176933 8568610028022216967720675)
            ·
              refine ⟨12852915042033325451581013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568610028022216967720675 12852915042033325451581013)
              ·
                refine ⟨150620098148828032635715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12852915042033325451581013 150620098148828032635715)
                ·
                  rfl

theorem cell23_7919953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 8].length) (baseStart_7919953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919953 prefixEnd_7919953 := by exact prefixLift 7919953
  have htrace : WordTrace (prefixWord ++ tailWord_7919953) baseStart_7919953 baseEnd_7919953 := by
    simpa [prefixWord, tailWord_7919953, baseEnd_7919953] using wordTrace_append hprefix tailTrace_7919953
  have hstable : (prefixWord ++ tailWord_7919953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919953).length < 2 ^ (prefixWord ++ tailWord_7919953).sum := by decide
  have hdescent : baseEnd_7919953 < baseStart_7919953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919970 : List Nat := [3, 3, 2, 1, 1, 3, 3, 7]
def baseStart_7919970 : Nat := 118140960795 + 7919970 * 2 ^ 59
def prefixEnd_7919970 : Nat := 4983230072969 + 3 ^ 40 * 7919970 * 2
def baseEnd_7919970 : Nat := 150620421451462344987101

theorem tailTrace_7919970 : CollatzResearch.WordTrace tailWord_7919970 prefixEnd_7919970 150620421451462344987101 := by
  unfold tailWord_7919970
  simp only [CollatzResearch.WordTrace]
  refine ⟨72216259279327197008319341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192576691411539192022184909 72216259279327197008319341)
  ·
    refine ⟨27081097229747698878119753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72216259279327197008319341 27081097229747698878119753)
    ·
      refine ⟨20310822922310774158589815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27081097229747698878119753 20310822922310774158589815)
      ·
        refine ⟨30466234383466161237884723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20310822922310774158589815 30466234383466161237884723)
        ·
          refine ⟨45699351575199241856827085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30466234383466161237884723 45699351575199241856827085)
          ·
            refine ⟨17137256840699715696310157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45699351575199241856827085 17137256840699715696310157)
            ·
              refine ⟨6426471315262393386116309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17137256840699715696310157 6426471315262393386116309)
              ·
                refine ⟨150620421451462344987101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6426471315262393386116309 150620421451462344987101)
                ·
                  rfl

theorem cell23_7919970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 7].length) (baseStart_7919970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919970 prefixEnd_7919970 := by exact prefixLift 7919970
  have htrace : WordTrace (prefixWord ++ tailWord_7919970) baseStart_7919970 baseEnd_7919970 := by
    simpa [prefixWord, tailWord_7919970, baseEnd_7919970] using wordTrace_append hprefix tailTrace_7919970
  have hstable : (prefixWord ++ tailWord_7919970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919970).length < 2 ^ (prefixWord ++ tailWord_7919970).sum := by decide
  have hdescent : baseEnd_7919970 < baseStart_7919970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919997 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_7919997 : Nat := 118140960795 + 7919997 * 2 ^ 59
def prefixEnd_7919997 : Nat := 4983230072969 + 3 ^ 40 * 7919997 * 2
def baseEnd_7919997 : Nat := 4066765243167154709014103

theorem tailTrace_7919997 : CollatzResearch.WordTrace tailWord_7919997 prefixEnd_7919997 4066765243167154709014103 := by
  unfold tailWord_7919997
  simp only [CollatzResearch.WordTrace]
  refine ⟨288866021888210971644510245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192577347925473981096340163 288866021888210971644510245)
  ·
    refine ⟨54162379104039557183345671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288866021888210971644510245 54162379104039557183345671)
    ·
      refine ⟨81243568656059335775018507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54162379104039557183345671 81243568656059335775018507)
      ·
        refine ⟨121865352984089003662527761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81243568656059335775018507 121865352984089003662527761)
        ·
          refine ⟨91399014738066752746895821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121865352984089003662527761 91399014738066752746895821)
          ·
            refine ⟨34274630526775032280085933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91399014738066752746895821 34274630526775032280085933)
            ·
              refine ⟨12852986447540637105032225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34274630526775032280085933 12852986447540637105032225)
              ·
                refine ⟨9639739835655477828774169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12852986447540637105032225 9639739835655477828774169)
                ·
                  refine ⟨7229804876741608371580627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9639739835655477828774169 7229804876741608371580627)
                  ·
                    refine ⟨10844707315112412557370941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7229804876741608371580627 10844707315112412557370941)
                    ·
                      refine ⟨4066765243167154709014103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10844707315112412557370941 4066765243167154709014103)
                      ·
                        rfl

theorem cell23_7919997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_7919997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919997 prefixEnd_7919997 := by exact prefixLift 7919997
  have htrace : WordTrace (prefixWord ++ tailWord_7919997) baseStart_7919997 baseEnd_7919997 := by
    simpa [prefixWord, tailWord_7919997, baseEnd_7919997] using wordTrace_append hprefix tailTrace_7919997
  have hstable : (prefixWord ++ tailWord_7919997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919997).length < 2 ^ (prefixWord ++ tailWord_7919997).sum := by decide
  have hdescent : baseEnd_7919997 < baseStart_7919997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920016 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_7920016 : Nat := 118140960795 + 7920016 * 2 ^ 59
def prefixEnd_7920016 : Nat := 4983230072969 + 3 ^ 40 * 7920016 * 2
def baseEnd_7920016 : Nat := 4066774999299590134676515

theorem tailTrace_7920016 : CollatzResearch.WordTrace tailWord_7920016 prefixEnd_7920016 4066774999299590134676515 := by
  unfold tailWord_7920016
  simp only [CollatzResearch.WordTrace]
  refine ⟨144433357437571068944725951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192577809916761425259634601 144433357437571068944725951)
  ·
    refine ⟨216650036156356603417088927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144433357437571068944725951 216650036156356603417088927)
    ·
      refine ⟨324975054234534905125633391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216650036156356603417088927 324975054234534905125633391)
      ·
        refine ⟨487462581351802357688450087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324975054234534905125633391 487462581351802357688450087)
        ·
          refine ⟨731193872027703536532675131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487462581351802357688450087 731193872027703536532675131)
          ·
            refine ⟨1096790808041555304799012697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731193872027703536532675131 1096790808041555304799012697)
            ·
              refine ⟨822593106031166478599259523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096790808041555304799012697 822593106031166478599259523)
              ·
                refine ⟨1233889659046749717898889285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822593106031166478599259523 1233889659046749717898889285)
                ·
                  refine ⟨231354311071265572106041741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233889659046749717898889285 231354311071265572106041741)
                  ·
                    refine ⟨86757866651724589539765653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231354311071265572106041741 86757866651724589539765653)
                    ·
                      refine ⟨4066774999299590134676515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86757866651724589539765653 4066774999299590134676515)
                      ·
                        rfl

theorem cell23_7920016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_7920016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920016 prefixEnd_7920016 := by exact prefixLift 7920016
  have htrace : WordTrace (prefixWord ++ tailWord_7920016) baseStart_7920016 baseEnd_7920016 := by
    simpa [prefixWord, tailWord_7920016, baseEnd_7920016] using wordTrace_append hprefix tailTrace_7920016
  have hstable : (prefixWord ++ tailWord_7920016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920016).length < 2 ^ (prefixWord ++ tailWord_7920016).sum := by decide
  have hdescent : baseEnd_7920016 < baseStart_7920016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920023 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 3]
def baseStart_7920023 : Nat := 118140960795 + 7920023 * 2 ^ 59
def prefixEnd_7920023 : Nat := 4983230072969 + 3 ^ 40 * 7920023 * 2
def baseEnd_7920023 : Nat := 4066778593664171607288983

theorem tailTrace_7920023 : CollatzResearch.WordTrace tailWord_7920023 prefixEnd_7920023 4066778593664171607288983 := by
  unfold tailWord_7920023
  simp only [CollatzResearch.WordTrace]
  refine ⟨288866970186116778084956723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192577980124077852056637815 288866970186116778084956723)
  ·
    refine ⟨433300455279175167127435085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288866970186116778084956723 433300455279175167127435085)
    ·
      refine ⟨162487670729690687672788157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433300455279175167127435085 162487670729690687672788157)
      ·
        refine ⟨60932876523634007877295559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162487670729690687672788157 60932876523634007877295559)
        ·
          refine ⟨91399314785451011815943339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60932876523634007877295559 91399314785451011815943339)
          ·
            refine ⟨137098972178176517723915009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91399314785451011815943339 137098972178176517723915009)
            ·
              refine ⟨102824229133632388292936257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137098972178176517723915009 102824229133632388292936257)
              ·
                refine ⟨77118171850224291219702193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102824229133632388292936257 77118171850224291219702193)
                ·
                  refine ⟨57838628887668218414776645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77118171850224291219702193 57838628887668218414776645)
                  ·
                    refine ⟨10844742916437790952770621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57838628887668218414776645 10844742916437790952770621)
                    ·
                      refine ⟨4066778593664171607288983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10844742916437790952770621 4066778593664171607288983)
                      ·
                        rfl

theorem cell23_7920023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_7920023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920023 prefixEnd_7920023 := by exact prefixLift 7920023
  have htrace : WordTrace (prefixWord ++ tailWord_7920023) baseStart_7920023 baseEnd_7920023 := by
    simpa [prefixWord, tailWord_7920023, baseEnd_7920023] using wordTrace_append hprefix tailTrace_7920023
  have hstable : (prefixWord ++ tailWord_7920023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920023).length < 2 ^ (prefixWord ++ tailWord_7920023).sum := by decide
  have hdescent : baseEnd_7920023 < baseStart_7920023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920024 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 1, 3, 2]
def baseStart_7920024 : Nat := 118140960795 + 7920024 * 2 ^ 59
def prefixEnd_7920024 : Nat := 4983230072969 + 3 ^ 40 * 7920024 * 2
def baseEnd_7920024 : Nat := 4066779107144826103376479

theorem tailTrace_7920024 : CollatzResearch.WordTrace tailWord_7920024 prefixEnd_7920024 4066779107144826103376479 := by
  unfold tailWord_7920024
  simp only [CollatzResearch.WordTrace]
  refine ⟨144433503329556577627871563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192578004439408770170495417 144433503329556577627871563)
  ·
    refine ⟨216650254994334866441807345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144433503329556577627871563 216650254994334866441807345)
    ·
      refine ⟨162487691245751149831355509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216650254994334866441807345 162487691245751149831355509)
      ·
        refine ⟨15233221054289170296689579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162487691245751149831355509 15233221054289170296689579)
        ·
          refine ⟨22849831581433755445034369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15233221054289170296689579 22849831581433755445034369)
          ·
            refine ⟨17137373686075316583775777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22849831581433755445034369 17137373686075316583775777)
            ·
              refine ⟨12853030264556487437831833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17137373686075316583775777 12853030264556487437831833)
              ·
                refine ⟨9639772698417365578373875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12853030264556487437831833 9639772698417365578373875)
                ·
                  refine ⟨14459659047626048367560813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9639772698417365578373875 14459659047626048367560813)
                  ·
                    refine ⟨5422372142859768137835305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14459659047626048367560813 5422372142859768137835305)
                    ·
                      refine ⟨4066779107144826103376479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5422372142859768137835305 4066779107144826103376479)
                      ·
                        rfl

theorem cell23_7920024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_7920024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920024 prefixEnd_7920024 := by exact prefixLift 7920024
  have htrace : WordTrace (prefixWord ++ tailWord_7920024) baseStart_7920024 baseEnd_7920024 := by
    simpa [prefixWord, tailWord_7920024, baseEnd_7920024] using wordTrace_append hprefix tailTrace_7920024
  have hstable : (prefixWord ++ tailWord_7920024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920024).length < 2 ^ (prefixWord ++ tailWord_7920024).sum := by decide
  have hdescent : baseEnd_7920024 < baseStart_7920024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920040 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7920040 : Nat := 118140960795 + 7920040 * 2 ^ 59
def prefixEnd_7920040 : Nat := 4983230072969 + 3 ^ 40 * 7920040 * 2
def baseEnd_7920040 : Nat := 4066787322835298040776405

theorem tailTrace_7920040 : CollatzResearch.WordTrace tailWord_7920040 prefixEnd_7920040 4066787322835298040776405 := by
  unfold tailWord_7920040
  simp only [CollatzResearch.WordTrace]
  refine ⟨144433795113527594994162787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192578393484703459992217049 144433795113527594994162787)
  ·
    refine ⟨216650692670291392491244181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144433795113527594994162787 216650692670291392491244181)
    ·
      refine ⟨10155501218919909023027071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 216650692670291392491244181 10155501218919909023027071)
      ·
        refine ⟨15233251828379863534540607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10155501218919909023027071 15233251828379863534540607)
        ·
          refine ⟨22849877742569795301810911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15233251828379863534540607 22849877742569795301810911)
          ·
            refine ⟨34274816613854692952716367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22849877742569795301810911 34274816613854692952716367)
            ·
              refine ⟨51412224920782039429074551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34274816613854692952716367 51412224920782039429074551)
              ·
                refine ⟨77118337381173059143611827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51412224920782039429074551 77118337381173059143611827)
                ·
                  refine ⟨115677506071759588715417741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77118337381173059143611827 115677506071759588715417741)
                  ·
                    refine ⟨43379064776909845768281653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115677506071759588715417741 43379064776909845768281653)
                    ·
                      refine ⟨4066787322835298040776405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43379064776909845768281653 4066787322835298040776405)
                      ·
                        rfl

theorem cell23_7920040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7920040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920040 prefixEnd_7920040 := by exact prefixLift 7920040
  have htrace : WordTrace (prefixWord ++ tailWord_7920040) baseStart_7920040 baseEnd_7920040 := by
    simpa [prefixWord, tailWord_7920040, baseEnd_7920040] using wordTrace_append hprefix tailTrace_7920040
  have hstable : (prefixWord ++ tailWord_7920040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920040).length < 2 ^ (prefixWord ++ tailWord_7920040).sum := by decide
  have hdescent : baseEnd_7920040 < baseStart_7920040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920060 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 7]
def baseStart_7920060 : Nat := 118140960795 + 7920060 * 2 ^ 59
def prefixEnd_7920060 : Nat := 4983230072969 + 3 ^ 40 * 7920060 * 2
def baseEnd_7920060 : Nat := 451866399160931995836257

theorem tailTrace_7920060 : CollatzResearch.WordTrace tailWord_7920060 prefixEnd_7920060 451866399160931995836257 := by
  unfold tailWord_7920060
  simp only [CollatzResearch.WordTrace]
  refine ⟨144434159843491366702026817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192578879791321822269369089 144434159843491366702026817)
  ·
    refine ⟨108325619882618525026520113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144434159843491366702026817 108325619882618525026520113)
    ·
      refine ⟨81244214911963893769890085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108325619882618525026520113 81244214911963893769890085)
      ·
        refine ⟨15233290295993230081854391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81244214911963893769890085 15233290295993230081854391)
        ·
          refine ⟨22849935443989845122781587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15233290295993230081854391 22849935443989845122781587)
          ·
            refine ⟨34274903165984767684172381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22849935443989845122781587 34274903165984767684172381)
            ·
              refine ⟨12853088687244287881564643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34274903165984767684172381 12853088687244287881564643)
              ·
                refine ⟨19279633030866431822346965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12853088687244287881564643 19279633030866431822346965)
                ·
                  refine ⟨451866399160931995836257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19279633030866431822346965 451866399160931995836257)
                  ·
                    rfl

theorem cell23_7920060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_7920060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920060 prefixEnd_7920060 := by exact prefixLift 7920060
  have htrace : WordTrace (prefixWord ++ tailWord_7920060) baseStart_7920060 baseEnd_7920060 := by
    simpa [prefixWord, tailWord_7920060, baseEnd_7920060] using wordTrace_append hprefix tailTrace_7920060
  have hstable : (prefixWord ++ tailWord_7920060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920060).length < 2 ^ (prefixWord ++ tailWord_7920060).sum := by decide
  have hdescent : baseEnd_7920060 < baseStart_7920060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920065 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7920065 : Nat := 118140960795 + 7920065 * 2 ^ 59
def prefixEnd_7920065 : Nat := 4983230072969 + 3 ^ 40 * 7920065 * 2
def baseEnd_7920065 : Nat := 4066800159851660442963791

theorem tailTrace_7920065 : CollatzResearch.WordTrace tailWord_7920065 prefixEnd_7920065 4066800159851660442963791 := by
  unfold tailWord_7920065
  simp only [CollatzResearch.WordTrace]
  refine ⟨288868502051964619257985649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192579001367976412838657099 288868502051964619257985649)
  ·
    refine ⟨216651376538973464443489237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288868502051964619257985649 216651376538973464443489237)
    ·
      refine ⟨5077766637632190572894279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 216651376538973464443489237 5077766637632190572894279)
      ·
        refine ⟨7616649956448285859341419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5077766637632190572894279 7616649956448285859341419)
        ·
          refine ⟨11424974934672428789012129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616649956448285859341419 11424974934672428789012129)
          ·
            refine ⟨8568731201004321591759097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11424974934672428789012129 8568731201004321591759097)
            ·
              refine ⟨6426548400753241193819323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8568731201004321591759097 6426548400753241193819323)
              ·
                refine ⟨9639822601129861790728985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426548400753241193819323 9639822601129861790728985)
                ·
                  refine ⟨7229866950847396343046739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9639822601129861790728985 7229866950847396343046739)
                  ·
                    refine ⟨10844800426271094514570109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7229866950847396343046739 10844800426271094514570109)
                    ·
                      refine ⟨4066800159851660442963791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10844800426271094514570109 4066800159851660442963791)
                      ·
                        rfl

theorem cell23_7920065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7920065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920065 prefixEnd_7920065 := by exact prefixLift 7920065
  have htrace : WordTrace (prefixWord ++ tailWord_7920065) baseStart_7920065 baseEnd_7920065 := by
    simpa [prefixWord, tailWord_7920065, baseEnd_7920065] using wordTrace_append hprefix tailTrace_7920065
  have hstable : (prefixWord ++ tailWord_7920065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920065).length < 2 ^ (prefixWord ++ tailWord_7920065).sum := by decide
  have hdescent : baseEnd_7920065 < baseStart_7920065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920071 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 2, 2, 2]
def baseStart_7920071 : Nat := 118140960795 + 7920071 * 2 ^ 59
def prefixEnd_7920071 : Nat := 4983230072969 + 3 ^ 40 * 7920071 * 2
def baseEnd_7920071 : Nat := 4066803240735587419488763

theorem tailTrace_7920071 : CollatzResearch.WordTrace tailWord_7920071 prefixEnd_7920071 4066803240735587419488763 := by
  unfold tailWord_7920071
  simp only [CollatzResearch.WordTrace]
  refine ⟨288868720889942882282704067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192579147259961921521802711 288868720889942882282704067)
  ·
    refine ⟨433303081334914323424056101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288868720889942882282704067 433303081334914323424056101)
    ·
      refine ⟨81244327750296435642010519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433303081334914323424056101 81244327750296435642010519)
      ·
        refine ⟨121866491625444653463015779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81244327750296435642010519 121866491625444653463015779)
        ·
          refine ⟨182799737438166980194523669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121866491625444653463015779 182799737438166980194523669)
          ·
            refine ⟨8568737692414077196618297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182799737438166980194523669 8568737692414077196618297)
            ·
              refine ⟨6426553269310557897463723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8568737692414077196618297 6426553269310557897463723)
              ·
                refine ⟨9639829903965836846195585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426553269310557897463723 9639829903965836846195585)
                ·
                  refine ⟨7229872427974377634646689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9639829903965836846195585 7229872427974377634646689)
                  ·
                    refine ⟨5422404320980783225985017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7229872427974377634646689 5422404320980783225985017)
                    ·
                      refine ⟨4066803240735587419488763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5422404320980783225985017 4066803240735587419488763)
                      ·
                        rfl

theorem cell23_7920071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_7920071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920071 prefixEnd_7920071 := by exact prefixLift 7920071
  have htrace : WordTrace (prefixWord ++ tailWord_7920071) baseStart_7920071 baseEnd_7920071 := by
    simpa [prefixWord, tailWord_7920071, baseEnd_7920071] using wordTrace_append hprefix tailTrace_7920071
  have hstable : (prefixWord ++ tailWord_7920071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920071).length < 2 ^ (prefixWord ++ tailWord_7920071).sum := by decide
  have hdescent : baseEnd_7920071 < baseStart_7920071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920090 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_7920090 : Nat := 118140960795 + 7920090 * 2 ^ 59
def prefixEnd_7920090 : Nat := 4983230072969 + 3 ^ 40 * 7920090 * 2
def baseEnd_7920090 : Nat := 1355604332289340948383725

theorem tailTrace_7920090 : CollatzResearch.WordTrace tailWord_7920090 prefixEnd_7920090 1355604332289340948383725 := by
  unfold tailWord_7920090
  simp only [CollatzResearch.WordTrace]
  refine ⟨72217353469218512131911431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192579609251249365685097149 72217353469218512131911431)
  ·
    refine ⟨108326030203827768197867147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72217353469218512131911431 108326030203827768197867147)
    ·
      refine ⟨162489045305741652296800721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108326030203827768197867147 162489045305741652296800721)
      ·
        refine ⟨121866783979306239222600541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162489045305741652296800721 121866783979306239222600541)
        ·
          refine ⟨45700043992239839708475203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121866783979306239222600541 45700043992239839708475203)
          ·
            refine ⟨68550065988359759562712805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45700043992239839708475203 68550065988359759562712805)
            ·
              refine ⟨12853137372817454918008651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68550065988359759562712805 12853137372817454918008651)
              ·
                refine ⟨19279706059226182377012977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12853137372817454918008651 19279706059226182377012977)
                ·
                  refine ⟨14459779544419636782759733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19279706059226182377012977 14459779544419636782759733)
                  ·
                    refine ⟨1355604332289340948383725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14459779544419636782759733 1355604332289340948383725)
                    ·
                      rfl

theorem cell23_7920090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_7920090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920090 prefixEnd_7920090 := by exact prefixLift 7920090
  have htrace : WordTrace (prefixWord ++ tailWord_7920090) baseStart_7920090 baseEnd_7920090 := by
    simpa [prefixWord, tailWord_7920090, baseEnd_7920090] using wordTrace_append hprefix tailTrace_7920090
  have hstable : (prefixWord ++ tailWord_7920090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920090).length < 2 ^ (prefixWord ++ tailWord_7920090).sum := by decide
  have hdescent : baseEnd_7920090 < baseStart_7920090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920113 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_7920113 : Nat := 118140960795 + 7920113 * 2 ^ 59
def prefixEnd_7920113 : Nat := 4983230072969 + 3 ^ 40 * 7920113 * 2
def baseEnd_7920113 : Nat := 4066824806923076255163569

theorem tailTrace_7920113 : CollatzResearch.WordTrace tailWord_7920113 prefixEnd_7920113 4066824806923076255163569 := by
  unfold tailWord_7920113
  simp only [CollatzResearch.WordTrace]
  refine ⟨288870252755790723455732993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192580168503860482303821995 288870252755790723455732993)
  ·
    refine ⟨216652689566843042591799745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288870252755790723455732993 216652689566843042591799745)
    ·
      refine ⟨162489517175132281943849809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216652689566843042591799745 162489517175132281943849809)
      ·
        refine ⟨121867137881349211457887357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162489517175132281943849809 121867137881349211457887357)
        ·
          refine ⟨45700176705505954296707759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121867137881349211457887357 45700176705505954296707759)
          ·
            refine ⟨68550265058258931445061639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45700176705505954296707759 68550265058258931445061639)
            ·
              refine ⟨102825397587388397167592459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68550265058258931445061639 102825397587388397167592459)
              ·
                refine ⟨154238096381082595751388689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102825397587388397167592459 154238096381082595751388689)
                ·
                  refine ⟨115678572285811946813541517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154238096381082595751388689 115678572285811946813541517)
                  ·
                    refine ⟨43379464607179480055078069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115678572285811946813541517 43379464607179480055078069)
                    ·
                      refine ⟨4066824806923076255163569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43379464607179480055078069 4066824806923076255163569)
                      ·
                        rfl

theorem cell23_7920113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_7920113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920113 prefixEnd_7920113 := by exact prefixLift 7920113
  have htrace : WordTrace (prefixWord ++ tailWord_7920113) baseStart_7920113 baseEnd_7920113 := by
    simpa [prefixWord, tailWord_7920113, baseEnd_7920113] using wordTrace_append hprefix tailTrace_7920113
  have hstable : (prefixWord ++ tailWord_7920113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920113).length < 2 ^ (prefixWord ++ tailWord_7920113).sum := by decide
  have hdescent : baseEnd_7920113 < baseStart_7920113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920120 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 3, 4]
def baseStart_7920120 : Nat := 118140960795 + 7920120 * 2 ^ 59
def prefixEnd_7920120 : Nat := 4983230072969 + 3 ^ 40 * 7920120 * 2
def baseEnd_7920120 : Nat := 1355609467095885909258679

theorem tailTrace_7920120 : CollatzResearch.WordTrace tailWord_7920120 prefixEnd_7920120 1355609467095885909258679 := by
  unfold tailWord_7920120
  simp only [CollatzResearch.WordTrace]
  refine ⟨144435254033382681825618907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192580338711176909100825209 144435254033382681825618907)
  ·
    refine ⟨216652881050074022738428361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144435254033382681825618907 216652881050074022738428361)
    ·
      refine ⟨162489660787555517053821271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216652881050074022738428361 162489660787555517053821271)
      ·
        refine ⟨243734491181333275580731907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162489660787555517053821271 243734491181333275580731907)
        ·
          refine ⟨365601736771999913371097861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243734491181333275580731907 365601736771999913371097861)
          ·
            refine ⟨68550325644749983757080849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365601736771999913371097861 68550325644749983757080849)
            ·
              refine ⟨51412744233562487817810637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68550325644749983757080849 51412744233562487817810637)
              ·
                refine ⟨19279779087585932931678989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51412744233562487817810637 19279779087585932931678989)
                ·
                  refine ⟨7229917157844724849379621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19279779087585932931678989 7229917157844724849379621)
                  ·
                    refine ⟨1355609467095885909258679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7229917157844724849379621 1355609467095885909258679)
                    ·
                      rfl

theorem cell23_7920120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_7920120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920120 prefixEnd_7920120 := by exact prefixLift 7920120
  have htrace : WordTrace (prefixWord ++ tailWord_7920120) baseStart_7920120 baseEnd_7920120 := by
    simpa [prefixWord, tailWord_7920120, baseEnd_7920120] using wordTrace_append hprefix tailTrace_7920120
  have hstable : (prefixWord ++ tailWord_7920120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920120).length < 2 ^ (prefixWord ++ tailWord_7920120).sum := by decide
  have hdescent : baseEnd_7920120 < baseStart_7920120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920141 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_7920141 : Nat := 118140960795 + 7920141 * 2 ^ 59
def prefixEnd_7920141 : Nat := 4983230072969 + 3 ^ 40 * 7920141 * 2
def baseEnd_7920141 : Nat := 1355613061460467381871147

theorem tailTrace_7920141 : CollatzResearch.WordTrace tailWord_7920141 prefixEnd_7920141 1355613061460467381871147 := by
  unfold tailWord_7920141
  simp only [CollatzResearch.WordTrace]
  refine ⟨288871273999689284237752277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192580849333126189491834851 288871273999689284237752277)
  ·
    refine ⟨6770420484367717599322319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 288871273999689284237752277 6770420484367717599322319)
    ·
      refine ⟨10155630726551576398983479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6770420484367717599322319 10155630726551576398983479)
      ·
        refine ⟨15233446089827364598475219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10155630726551576398983479 15233446089827364598475219)
        ·
          refine ⟨22850169134741046897712829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15233446089827364598475219 22850169134741046897712829)
          ·
            refine ⟨8568813425527892586642311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22850169134741046897712829 8568813425527892586642311)
            ·
              refine ⟨12853220138291838879963467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568813425527892586642311 12853220138291838879963467)
              ·
                refine ⟨19279830207437758319945201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12853220138291838879963467 19279830207437758319945201)
                ·
                  refine ⟨14459872655578318739958901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19279830207437758319945201 14459872655578318739958901)
                  ·
                    refine ⟨1355613061460467381871147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14459872655578318739958901 1355613061460467381871147)
                    ·
                      rfl

theorem cell23_7920141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_7920141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920141 prefixEnd_7920141 := by exact prefixLift 7920141
  have htrace : WordTrace (prefixWord ++ tailWord_7920141) baseStart_7920141 baseEnd_7920141 := by
    simpa [prefixWord, tailWord_7920141, baseEnd_7920141] using wordTrace_append hprefix tailTrace_7920141
  have hstable : (prefixWord ++ tailWord_7920141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920141).length < 2 ^ (prefixWord ++ tailWord_7920141).sum := by decide
  have hdescent : baseEnd_7920141 < baseStart_7920141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920170 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7920170 : Nat := 118140960795 + 7920170 * 2 ^ 59
def prefixEnd_7920170 : Nat := 4983230072969 + 3 ^ 40 * 7920170 * 2
def baseEnd_7920170 : Nat := 4066854075320382532150807

theorem tailTrace_7920170 : CollatzResearch.WordTrace tailWord_7920170 prefixEnd_7920170 4066854075320382532150807 := by
  unfold tailWord_7920170
  simp only [CollatzResearch.WordTrace]
  refine ⟨72218082929146055547639491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192581554477722814793705309 72218082929146055547639491)
  ·
    refine ⟨108327124393719083321459237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72218082929146055547639491 108327124393719083321459237)
    ·
      refine ⟨20311335823822328122773607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108327124393719083321459237 20311335823822328122773607)
      ·
        refine ⟨30467003735733492184160411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20311335823822328122773607 30467003735733492184160411)
        ·
          refine ⟨45700505603600238276240617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30467003735733492184160411 45700505603600238276240617)
          ·
            refine ⟨34275379202700178707180463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45700505603600238276240617 34275379202700178707180463)
            ·
              refine ⟨51413068804050268060770695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34275379202700178707180463 51413068804050268060770695)
              ·
                refine ⟨77119603206075402091156043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51413068804050268060770695 77119603206075402091156043)
                ·
                  refine ⟨115679404809113103136734065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77119603206075402091156043 115679404809113103136734065)
                  ·
                    refine ⟨86759553606834827352550549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115679404809113103136734065 86759553606834827352550549)
                    ·
                      refine ⟨4066854075320382532150807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86759553606834827352550549 4066854075320382532150807)
                      ·
                        rfl

theorem cell23_7920170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7920170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920170 prefixEnd_7920170 := by exact prefixLift 7920170
  have htrace : WordTrace (prefixWord ++ tailWord_7920170) baseStart_7920170 baseEnd_7920170 := by
    simpa [prefixWord, tailWord_7920170, baseEnd_7920170] using wordTrace_append hprefix tailTrace_7920170
  have hstable : (prefixWord ++ tailWord_7920170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920170).length < 2 ^ (prefixWord ++ tailWord_7920170).sum := by decide
  have hdescent : baseEnd_7920170 < baseStart_7920170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920177 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 3, 1, 3]
def baseStart_7920177 : Nat := 118140960795 + 7920177 * 2 ^ 59
def prefixEnd_7920177 : Nat := 4983230072969 + 3 ^ 40 * 7920177 * 2
def baseEnd_7920177 : Nat := 4066857669684964004763275

theorem tailTrace_7920177 : CollatzResearch.WordTrace tailWord_7920177 prefixEnd_7920177 4066857669684964004763275 := by
  unfold tailWord_7920177
  simp only [CollatzResearch.WordTrace]
  refine ⟨288872587027558862386062785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192581724685039241590708523 288872587027558862386062785)
  ·
    refine ⟨216654440270669146789547089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288872587027558862386062785 216654440270669146789547089)
    ·
      refine ⟨162490830203001860092160317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216654440270669146789547089 162490830203001860092160317)
      ·
        refine ⟨60934061326125697534560119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162490830203001860092160317 60934061326125697534560119)
        ·
          refine ⟨91401091989188546301840179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60934061326125697534560119 91401091989188546301840179)
          ·
            refine ⟨137101637983782819452760269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91401091989188546301840179 137101637983782819452760269)
            ·
              refine ⟨51413114243918557294785101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137101637983782819452760269 51413114243918557294785101)
              ·
                refine ⟨19279917841469458985544413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51413114243918557294785101 19279917841469458985544413)
                ·
                  refine ⟨7229969190551047119579155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19279917841469458985544413 7229969190551047119579155)
                  ·
                    refine ⟨10844953785826570679368733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7229969190551047119579155 10844953785826570679368733)
                    ·
                      refine ⟨4066857669684964004763275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10844953785826570679368733 4066857669684964004763275)
                      ·
                        rfl

theorem cell23_7920177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_7920177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920177 prefixEnd_7920177 := by exact prefixLift 7920177
  have htrace : WordTrace (prefixWord ++ tailWord_7920177) baseStart_7920177 baseEnd_7920177 := by
    simpa [prefixWord, tailWord_7920177, baseEnd_7920177] using wordTrace_append hprefix tailTrace_7920177
  have hstable : (prefixWord ++ tailWord_7920177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920177).length < 2 ^ (prefixWord ++ tailWord_7920177).sum := by decide
  have hdescent : baseEnd_7920177 < baseStart_7920177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920197 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_7920197 : Nat := 118140960795 + 7920197 * 2 ^ 59
def prefixEnd_7920197 : Nat := 4983230072969 + 3 ^ 40 * 7920197 * 2
def baseEnd_7920197 : Nat := 1355622646432684642171061

theorem tailTrace_7920197 : CollatzResearch.WordTrace tailWord_7920197 prefixEnd_7920197 1355622646432684642171061 := by
  unfold tailWord_7920197
  simp only [CollatzResearch.WordTrace]
  refine ⟨288873316487486405801790845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192582210991657603867860563 288873316487486405801790845)
  ·
    refine ⟨108327493682807402175671567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288873316487486405801790845 108327493682807402175671567)
    ·
      refine ⟨162491240524211103263507351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108327493682807402175671567 162491240524211103263507351)
      ·
        refine ⟨243736860786316654895261027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162491240524211103263507351 243736860786316654895261027)
        ·
          refine ⟨365605291179474982342891541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243736860786316654895261027 365605291179474982342891541)
          ·
            refine ⟨17137748024037889797323041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 365605291179474982342891541 17137748024037889797323041)
            ·
              refine ⟨12853311018028417347992281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17137748024037889797323041 12853311018028417347992281)
              ·
                refine ⟨9639983263521313010994211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12853311018028417347992281 9639983263521313010994211)
                ·
                  refine ⟨14459974895281969516491317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9639983263521313010994211 14459974895281969516491317)
                  ·
                    refine ⟨1355622646432684642171061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14459974895281969516491317 1355622646432684642171061)
                    ·
                      rfl

theorem cell23_7920197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_7920197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920197 prefixEnd_7920197 := by exact prefixLift 7920197
  have htrace : WordTrace (prefixWord ++ tailWord_7920197) baseStart_7920197 baseEnd_7920197 := by
    simpa [prefixWord, tailWord_7920197, baseEnd_7920197] using wordTrace_append hprefix tailTrace_7920197
  have hstable : (prefixWord ++ tailWord_7920197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920197).length < 2 ^ (prefixWord ++ tailWord_7920197).sum := by decide
  have hdescent : baseEnd_7920197 < baseStart_7920197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920200 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_7920200 : Nat := 118140960795 + 7920200 * 2 ^ 59
def prefixEnd_7920200 : Nat := 4983230072969 + 3 ^ 40 * 7920200 * 2
def baseEnd_7920200 : Nat := 4066869479740017414775669

theorem tailTrace_7920200 : CollatzResearch.WordTrace tailWord_7920200 prefixEnd_7920200 4066869479740017414775669 := by
  unfold tailWord_7920200
  simp only [CollatzResearch.WordTrace]
  refine ⟨144436712953237768657075027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192582283937650358209433369 144436712953237768657075027)
  ·
    refine ⟨216655069429856652985612541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144436712953237768657075027 216655069429856652985612541)
    ·
      refine ⟨81245651036196244869604703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216655069429856652985612541 81245651036196244869604703)
      ·
        refine ⟨121868476554294367304407055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81245651036196244869604703 121868476554294367304407055)
        ·
          refine ⟨182802714831441550956610583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121868476554294367304407055 182802714831441550956610583)
          ·
            refine ⟨274204072247162326434915875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182802714831441550956610583 274204072247162326434915875)
            ·
              refine ⟨411306108370743489652373813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274204072247162326434915875 411306108370743489652373813)
              ·
                refine ⟨38559947659757202154910045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411306108370743489652373813 38559947659757202154910045)
                ·
                  refine ⟨14459980372408950808091267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38559947659757202154910045 14459980372408950808091267)
                  ·
                    refine ⟨21689970558613426212136901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14459980372408950808091267 21689970558613426212136901)
                    ·
                      refine ⟨4066869479740017414775669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21689970558613426212136901 4066869479740017414775669)
                      ·
                        rfl

theorem cell23_7920200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_7920200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920200 prefixEnd_7920200 := by exact prefixLift 7920200
  have htrace : WordTrace (prefixWord ++ tailWord_7920200) baseStart_7920200 baseEnd_7920200 := by
    simpa [prefixWord, tailWord_7920200, baseEnd_7920200] using wordTrace_append hprefix tailTrace_7920200
  have hstable : (prefixWord ++ tailWord_7920200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920200).length < 2 ^ (prefixWord ++ tailWord_7920200).sum := by decide
  have hdescent : baseEnd_7920200 < baseStart_7920200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920210 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_7920210 : Nat := 118140960795 + 7920210 * 2 ^ 59
def prefixEnd_7920210 : Nat := 4983230072969 + 3 ^ 40 * 7920210 * 2
def baseEnd_7920210 : Nat := 1355624871515520791883541

theorem tailTrace_7920210 : CollatzResearch.WordTrace tailWord_7920210 prefixEnd_7920210 1355624871515520791883541 := by
  unfold tailWord_7920210
  simp only [CollatzResearch.WordTrace]
  refine ⟨72218447659109827255503521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192582527090959539348009389 72218447659109827255503521)
  ·
    refine ⟨54163835744332370441627641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72218447659109827255503521 54163835744332370441627641)
    ·
      refine ⟨40622876808249277831220731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54163835744332370441627641 40622876808249277831220731)
      ·
        refine ⟨60934315212373916746831097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40622876808249277831220731 60934315212373916746831097)
        ·
          refine ⟨45700736409280437560123323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60934315212373916746831097 45700736409280437560123323)
          ·
            refine ⟨68551104613920656340184985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45700736409280437560123323 68551104613920656340184985)
            ·
              refine ⟨51413328460440492255138739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68551104613920656340184985 51413328460440492255138739)
              ·
                refine ⟨77119992690660738382708109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51413328460440492255138739 77119992690660738382708109)
                ·
                  refine ⟨28919997258997776893515541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77119992690660738382708109 28919997258997776893515541)
                  ·
                    refine ⟨1355624871515520791883541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28919997258997776893515541 1355624871515520791883541)
                    ·
                      rfl

theorem cell23_7920210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_7920210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920210 prefixEnd_7920210 := by exact prefixLift 7920210
  have htrace : WordTrace (prefixWord ++ tailWord_7920210) baseStart_7920210 baseEnd_7920210 := by
    simpa [prefixWord, tailWord_7920210, baseEnd_7920210] using wordTrace_append hprefix tailTrace_7920210
  have hstable : (prefixWord ++ tailWord_7920210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920210).length < 2 ^ (prefixWord ++ tailWord_7920210).sum := by decide
  have hdescent : baseEnd_7920210 < baseStart_7920210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920222 : List Nat := [4, 4, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_7920222 : Nat := 118140960795 + 7920222 * 2 ^ 59
def prefixEnd_7920222 : Nat := 4983230072969 + 3 ^ 40 * 7920222 * 2
def baseEnd_7920222 : Nat := 1355626925438138776233523

theorem tailTrace_7920222 : CollatzResearch.WordTrace tailWord_7920222 prefixEnd_7920222 1355626925438138776233523 := by
  unfold tailWord_7920222
  simp only [CollatzResearch.WordTrace]
  refine ⟨36109278539049479383931365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192582818874930556714300613 36109278539049479383931365)
  ·
    refine ⟨6770489726071777384487131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36109278539049479383931365 6770489726071777384487131)
    ·
      refine ⟨10155734589107666076730697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6770489726071777384487131 10155734589107666076730697)
      ·
        refine ⟨7616800941830749557548023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10155734589107666076730697 7616800941830749557548023)
        ·
          refine ⟨11425201412746124336322035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616800941830749557548023 11425201412746124336322035)
          ·
            refine ⟨17137802119119186504483053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11425201412746124336322035 17137802119119186504483053)
            ·
              refine ⟨6426675794669694939181145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17137802119119186504483053 6426675794669694939181145)
              ·
                refine ⟨4820006846002271204385859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6426675794669694939181145 4820006846002271204385859)
                ·
                  refine ⟨7230010269003406806578789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820006846002271204385859 7230010269003406806578789)
                  ·
                    refine ⟨1355626925438138776233523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7230010269003406806578789 1355626925438138776233523)
                    ·
                      rfl

theorem cell23_7920222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_7920222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920222 prefixEnd_7920222 := by exact prefixLift 7920222
  have htrace : WordTrace (prefixWord ++ tailWord_7920222) baseStart_7920222 baseEnd_7920222 := by
    simpa [prefixWord, tailWord_7920222, baseEnd_7920222] using wordTrace_append hprefix tailTrace_7920222
  have hstable : (prefixWord ++ tailWord_7920222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920222).length < 2 ^ (prefixWord ++ tailWord_7920222).sum := by decide
  have hdescent : baseEnd_7920222 < baseStart_7920222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920227 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 2, 4]
def baseStart_7920227 : Nat := 118140960795 + 7920227 * 2 ^ 59
def prefixEnd_7920227 : Nat := 4983230072969 + 3 ^ 40 * 7920227 * 2
def baseEnd_7920227 : Nat := 1355627781239229603046015

theorem tailTrace_7920227 : CollatzResearch.WordTrace tailWord_7920227 prefixEnd_7920227 1355627781239229603046015 := by
  unfold tailWord_7920227
  simp only [CollatzResearch.WordTrace]
  refine ⟨288874410677377720925382935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192582940451585147283588623 288874410677377720925382935)
  ·
    refine ⟨433311616016066581388074403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288874410677377720925382935 433311616016066581388074403)
    ·
      refine ⟨649967424024099872082111605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433311616016066581388074403 649967424024099872082111605)
      ·
        refine ⟨60934446002259363007697963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 649967424024099872082111605 60934446002259363007697963)
        ·
          refine ⟨91401669003389044511546945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60934446002259363007697963 91401669003389044511546945)
          ·
            refine ⟨68551251752541783383660209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91401669003389044511546945 68551251752541783383660209)
            ·
              refine ⟨51413438814406337537745157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68551251752541783383660209 51413438814406337537745157)
              ·
                refine ⟨9640019777701188288327217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51413438814406337537745157 9640019777701188288327217)
                ·
                  refine ⟨7230014833275891216245413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9640019777701188288327217 7230014833275891216245413)
                  ·
                    refine ⟨1355627781239229603046015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7230014833275891216245413 1355627781239229603046015)
                    ·
                      rfl

theorem cell23_7920227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 4].length) (baseStart_7920227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920227 prefixEnd_7920227 := by exact prefixLift 7920227
  have htrace : WordTrace (prefixWord ++ tailWord_7920227) baseStart_7920227 baseEnd_7920227 := by
    simpa [prefixWord, tailWord_7920227, baseEnd_7920227] using wordTrace_append hprefix tailTrace_7920227
  have hstable : (prefixWord ++ tailWord_7920227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920227).length < 2 ^ (prefixWord ++ tailWord_7920227).sum := by decide
  have hdescent : baseEnd_7920227 < baseStart_7920227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920237 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_7920237 : Nat := 118140960795 + 7920237 * 2 ^ 59
def prefixEnd_7920237 : Nat := 4983230072969 + 3 ^ 40 * 7920237 * 2
def baseEnd_7920237 : Nat := 4066888478524233770012999

theorem tailTrace_7920237 : CollatzResearch.WordTrace tailWord_7920237 prefixEnd_7920237 4066888478524233770012999 := by
  unfold tailWord_7920237
  simp only [CollatzResearch.WordTrace]
  refine ⟨288874775407341492633246965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192583183604894328422164643 288874775407341492633246965)
  ·
    refine ⟨27082010194438264934366903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288874775407341492633246965 27082010194438264934366903)
    ·
      refine ⟨40623015291657397401550355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27082010194438264934366903 40623015291657397401550355)
      ·
        refine ⟨60934522937486096102325533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40623015291657397401550355 60934522937486096102325533)
        ·
          refine ⟨22850446101557286038372075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60934522937486096102325533 22850446101557286038372075)
          ·
            refine ⟨34275669152335929057558113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22850446101557286038372075 34275669152335929057558113)
            ·
              refine ⟨25706751864251946793168585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34275669152335929057558113 25706751864251946793168585)
              ·
                refine ⟨19280063898188960094876439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25706751864251946793168585 19280063898188960094876439)
                ·
                  refine ⟨28920095847283440142314659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19280063898188960094876439 28920095847283440142314659)
                  ·
                    refine ⟨43380143770925160213471989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28920095847283440142314659 43380143770925160213471989)
                    ·
                      refine ⟨4066888478524233770012999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43380143770925160213471989 4066888478524233770012999)
                      ·
                        rfl

theorem cell23_7920237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_7920237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920237 prefixEnd_7920237 := by exact prefixLift 7920237
  have htrace : WordTrace (prefixWord ++ tailWord_7920237) baseStart_7920237 baseEnd_7920237 := by
    simpa [prefixWord, tailWord_7920237, baseEnd_7920237] using wordTrace_append hprefix tailTrace_7920237
  have hstable : (prefixWord ++ tailWord_7920237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920237).length < 2 ^ (prefixWord ++ tailWord_7920237).sum := by decide
  have hdescent : baseEnd_7920237 < baseStart_7920237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920267 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 4, 1, 3]
def baseStart_7920267 : Nat := 118140960795 + 7920267 * 2 ^ 59
def prefixEnd_7920267 : Nat := 4983230072969 + 3 ^ 40 * 7920267 * 2
def baseEnd_7920267 : Nat := 4066903882943868652637861

theorem tailTrace_7920267 : CollatzResearch.WordTrace tailWord_7920267 prefixEnd_7920267 4066903882943868652637861 := by
  unfold tailWord_7920267
  simp only [CollatzResearch.WordTrace]
  refine ⟨288875869597232807756839055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192583913064821871837892703 288875869597232807756839055)
  ·
    refine ⟨433313804395849211635258583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288875869597232807756839055 433313804395849211635258583)
    ·
      refine ⟨649970706593773817452887875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433313804395849211635258583 649970706593773817452887875)
      ·
        refine ⟨974956059890660726179331813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649970706593773817452887875 974956059890660726179331813)
        ·
          refine ⟨182804261229498886158624715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 974956059890660726179331813 182804261229498886158624715)
          ·
            refine ⟨274206391844248329237937073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182804261229498886158624715 274206391844248329237937073)
            ·
              refine ⟨205654793883186246928452805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274206391844248329237937073 205654793883186246928452805)
              ·
                refine ⟨38560273853097421299084901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205654793883186246928452805 38560273853097421299084901)
                ·
                  refine ⟨7230051347455766493578419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38560273853097421299084901 7230051347455766493578419)
                  ·
                    refine ⟨10845077021183649740367629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7230051347455766493578419 10845077021183649740367629)
                    ·
                      refine ⟨4066903882943868652637861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10845077021183649740367629 4066903882943868652637861)
                      ·
                        rfl

theorem cell23_7920267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 1, 3].length) (baseStart_7920267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920267 prefixEnd_7920267 := by exact prefixLift 7920267
  have htrace : WordTrace (prefixWord ++ tailWord_7920267) baseStart_7920267 baseEnd_7920267 := by
    simpa [prefixWord, tailWord_7920267, baseEnd_7920267] using wordTrace_append hprefix tailTrace_7920267
  have hstable : (prefixWord ++ tailWord_7920267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920267).length < 2 ^ (prefixWord ++ tailWord_7920267).sum := by decide
  have hdescent : baseEnd_7920267 < baseStart_7920267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920301 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_7920301 : Nat := 118140960795 + 7920301 * 2 ^ 59
def prefixEnd_7920301 : Nat := 4983230072969 + 3 ^ 40 * 7920301 * 2
def baseEnd_7920301 : Nat := 4066921341286121519612705

theorem tailTrace_7920301 : CollatzResearch.WordTrace tailWord_7920301 prefixEnd_7920301 4066921341286121519612705 := by
  unfold tailWord_7920301
  simp only [CollatzResearch.WordTrace]
  refine ⟨288877109679109631563576757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192584739786073087709051171 288877109679109631563576757)
  ·
    refine ⟨27082229032416527959085321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288877109679109631563576757 27082229032416527959085321)
    ·
      refine ⟨20311671774312395969313991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27082229032416527959085321 20311671774312395969313991)
      ·
        refine ⟨30467507661468593953970987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20311671774312395969313991 30467507661468593953970987)
        ·
          refine ⟨45701261492202890930956481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30467507661468593953970987 45701261492202890930956481)
          ·
            refine ⟨34275946119152168198217361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45701261492202890930956481 34275946119152168198217361)
            ·
              refine ⟨25706959589364126148663021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34275946119152168198217361 25706959589364126148663021)
              ·
                refine ⟨9640109846011547305748633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25706959589364126148663021 9640109846011547305748633)
                ·
                  refine ⟨7230082384508660479311475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9640109846011547305748633 7230082384508660479311475)
                  ·
                    refine ⟨10845123576762990718967213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7230082384508660479311475 10845123576762990718967213)
                    ·
                      refine ⟨4066921341286121519612705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10845123576762990718967213 4066921341286121519612705)
                      ·
                        rfl

theorem cell23_7920301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_7920301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920301 prefixEnd_7920301 := by exact prefixLift 7920301
  have htrace : WordTrace (prefixWord ++ tailWord_7920301) baseStart_7920301 baseEnd_7920301 := by
    simpa [prefixWord, tailWord_7920301, baseEnd_7920301] using wordTrace_append hprefix tailTrace_7920301
  have hstable : (prefixWord ++ tailWord_7920301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920301).length < 2 ^ (prefixWord ++ tailWord_7920301).sum := by decide
  have hdescent : baseEnd_7920301 < baseStart_7920301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920328 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 1, 3, 2]
def baseStart_7920328 : Nat := 118140960795 + 7920328 * 2 ^ 59
def prefixEnd_7920328 : Nat := 4983230072969 + 3 ^ 40 * 7920328 * 2
def baseEnd_7920328 : Nat := 4066935205263792913975081

theorem tailTrace_7920328 : CollatzResearch.WordTrace tailWord_7920328 prefixEnd_7920328 4066935205263792913975081 := by
  unfold tailWord_7920328
  simp only [CollatzResearch.WordTrace]
  refine ⟨144439047225005907587404819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192585396300007876783206425 144439047225005907587404819)
  ·
    refine ⟨216658570837508861381107229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144439047225005907587404819 216658570837508861381107229)
    ·
      refine ⟨81246964064065823017915211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216658570837508861381107229 81246964064065823017915211)
      ·
        refine ⟨121870446096098734526872817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81246964064065823017915211 121870446096098734526872817)
        ·
          refine ⟨91402834572074050895154613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121870446096098734526872817 91402834572074050895154613)
          ·
            refine ⟨8569015741131942271420745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91402834572074050895154613 8569015741131942271420745)
            ·
              refine ⟨6426761805848956703565559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8569015741131942271420745 6426761805848956703565559)
              ·
                refine ⟨9640142708773435055348339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426761805848956703565559 9640142708773435055348339)
                ·
                  refine ⟨14460214063160152583022509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9640142708773435055348339 14460214063160152583022509)
                  ·
                    refine ⟨5422580273685057218633441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14460214063160152583022509 5422580273685057218633441)
                    ·
                      refine ⟨4066935205263792913975081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5422580273685057218633441 4066935205263792913975081)
                      ·
                        rfl

theorem cell23_7920328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_7920328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920328 prefixEnd_7920328 := by exact prefixLift 7920328
  have htrace : WordTrace (prefixWord ++ tailWord_7920328) baseStart_7920328 baseEnd_7920328 := by
    simpa [prefixWord, tailWord_7920328, baseEnd_7920328] using wordTrace_append hprefix tailTrace_7920328
  have hstable : (prefixWord ++ tailWord_7920328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920328).length < 2 ^ (prefixWord ++ tailWord_7920328).sum := by decide
  have hdescent : baseEnd_7920328 < baseStart_7920328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920424 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 5, 4]
def baseStart_7920424 : Nat := 118140960795 + 7920424 * 2 ^ 59
def prefixEnd_7920424 : Nat := 4983230072969 + 3 ^ 40 * 7920424 * 2
def baseEnd_7920424 : Nat := 1355661499802208179458213

theorem tailTrace_7920424 : CollatzResearch.WordTrace tailWord_7920424 prefixEnd_7920424 1355661499802208179458213 := by
  unfold tailWord_7920424
  simp only [CollatzResearch.WordTrace]
  refine ⟨144440797928832011785152163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192587730571776015713536217 144440797928832011785152163)
  ·
    refine ⟨216661196893248017677728245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144440797928832011785152163 216661196893248017677728245)
    ·
      refine ⟨20311987208742001657287023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216661196893248017677728245 20311987208742001657287023)
      ·
        refine ⟨30467980813113002485930535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20311987208742001657287023 30467980813113002485930535)
        ·
          refine ⟨45701971219669503728895803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30467980813113002485930535 45701971219669503728895803)
          ·
            refine ⟨68552956829504255593343705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45701971219669503728895803 68552956829504255593343705)
            ·
              refine ⟨51414717622128191695007779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68552956829504255593343705 51414717622128191695007779)
              ·
                refine ⟨77122076433192287542511669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51414717622128191695007779 77122076433192287542511669)
                ·
                  refine ⟨7230194665611776957110469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77122076433192287542511669 7230194665611776957110469)
                  ·
                    refine ⟨1355661499802208179458213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7230194665611776957110469 1355661499802208179458213)
                    ·
                      rfl

theorem cell23_7920424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_7920424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920424 prefixEnd_7920424 := by exact prefixLift 7920424
  have htrace : WordTrace (prefixWord ++ tailWord_7920424) baseStart_7920424 baseEnd_7920424 := by
    simpa [prefixWord, tailWord_7920424, baseEnd_7920424] using wordTrace_append hprefix tailTrace_7920424
  have hstable : (prefixWord ++ tailWord_7920424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920424).length < 2 ^ (prefixWord ++ tailWord_7920424).sum := by decide
  have hdescent : baseEnd_7920424 < baseStart_7920424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920484 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_7920484 : Nat := 118140960795 + 7920484 * 2 ^ 59
def prefixEnd_7920484 : Nat := 4983230072969 + 3 ^ 40 * 7920484 * 2
def baseEnd_7920484 : Nat := 1355671769415298101208121

theorem tailTrace_7920484 : CollatzResearch.WordTrace tailWord_7920484 prefixEnd_7920484 1355671769415298101208121 := by
  unfold tailWord_7920484
  simp only [CollatzResearch.WordTrace]
  refine ⟨144441892118723326908744253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192589189491631102544992337 144441892118723326908744253)
  ·
    refine ⟨54165709544521247590779095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144441892118723326908744253 54165709544521247590779095)
    ·
      refine ⟨81248564316781871386168643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54165709544521247590779095 81248564316781871386168643)
      ·
        refine ⟨121872846475172807079252965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81248564316781871386168643 121872846475172807079252965)
        ·
          refine ⟨22851158714094901327359931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121872846475172807079252965 22851158714094901327359931)
          ·
            refine ⟨34276738071142351991039897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22851158714094901327359931 34276738071142351991039897)
            ·
              refine ⟨25707553553356763993279923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34276738071142351991039897 25707553553356763993279923)
              ·
                refine ⟨38561330330035145989919885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25707553553356763993279923 38561330330035145989919885)
                ·
                  refine ⟨14460498873763179746219957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38561330330035145989919885 14460498873763179746219957)
                  ·
                    refine ⟨1355671769415298101208121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14460498873763179746219957 1355671769415298101208121)
                    ·
                      rfl

theorem cell23_7920484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_7920484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920484 prefixEnd_7920484 := by exact prefixLift 7920484
  have htrace : WordTrace (prefixWord ++ tailWord_7920484) baseStart_7920484 baseEnd_7920484 := by
    simpa [prefixWord, tailWord_7920484, baseEnd_7920484] using wordTrace_append hprefix tailTrace_7920484
  have hstable : (prefixWord ++ tailWord_7920484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920484).length < 2 ^ (prefixWord ++ tailWord_7920484).sum := by decide
  have hdescent : baseEnd_7920484 < baseStart_7920484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920491 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 2, 3, 2]
def baseStart_7920491 : Nat := 118140960795 + 7920491 * 2 ^ 59
def prefixEnd_7920491 : Nat := 4983230072969 + 3 ^ 40 * 7920491 * 2
def baseEnd_7920491 : Nat := 4067018902610475776236831

theorem tailTrace_7920491 : CollatzResearch.WordTrace tailWord_7920491 prefixEnd_7920491 4067018902610475776236831 := by
  unfold tailWord_7920491
  simp only [CollatzResearch.WordTrace]
  refine ⟨288884039548421294012993327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192589359698947529341995551 288884039548421294012993327)
  ·
    refine ⟨433326059322631941019489991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288884039548421294012993327 433326059322631941019489991)
    ·
      refine ⟨649989088983947911529234987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433326059322631941019489991 649989088983947911529234987)
      ·
        refine ⟨974983633475921867293852481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649989088983947911529234987 974983633475921867293852481)
        ·
          refine ⟨731237725106941400470389361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974983633475921867293852481 731237725106941400470389361)
          ·
            refine ⟨548428293830206050352792021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731237725106941400470389361 548428293830206050352792021)
            ·
              refine ⟨12853788136645454305143563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 548428293830206050352792021 12853788136645454305143563)
              ·
                refine ⟨19280682204968181457715345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12853788136645454305143563 19280682204968181457715345)
                ·
                  refine ⟨14460511653726136093286509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19280682204968181457715345 14460511653726136093286509)
                  ·
                    refine ⟨5422691870147301034982441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14460511653726136093286509 5422691870147301034982441)
                    ·
                      refine ⟨4067018902610475776236831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5422691870147301034982441 4067018902610475776236831)
                      ·
                        rfl

theorem cell23_7920491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 3, 2].length) (baseStart_7920491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920491 prefixEnd_7920491 := by exact prefixLift 7920491
  have htrace : WordTrace (prefixWord ++ tailWord_7920491) baseStart_7920491 baseEnd_7920491 := by
    simpa [prefixWord, tailWord_7920491, baseEnd_7920491] using wordTrace_append hprefix tailTrace_7920491
  have hstable : (prefixWord ++ tailWord_7920491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920491).length < 2 ^ (prefixWord ++ tailWord_7920491).sum := by decide
  have hdescent : baseEnd_7920491 < baseStart_7920491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920498 : List Nat := [3, 2, 1, 2, 1, 1, 3, 5, 1, 1, 3]
def baseStart_7920498 : Nat := 118140960795 + 7920498 * 2 ^ 59
def prefixEnd_7920498 : Nat := 4983230072969 + 3 ^ 40 * 7920498 * 2
def baseEnd_7920498 : Nat := 4067022496975057248849299

theorem tailTrace_7920498 : CollatzResearch.WordTrace tailWord_7920498 prefixEnd_7920498 4067022496975057248849299 := by
  unfold tailWord_7920498
  simp only [CollatzResearch.WordTrace]
  refine ⟨72221073714848983552124537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192589529906263956138998765 72221073714848983552124537)
  ·
    refine ⟨54165805286136737664093403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72221073714848983552124537 54165805286136737664093403)
    ·
      refine ⟨81248707929205106496140105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54165805286136737664093403 81248707929205106496140105)
      ·
        refine ⟨60936530946903829872105079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81248707929205106496140105 60936530946903829872105079)
        ·
          refine ⟨91404796420355744808157619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60936530946903829872105079 91404796420355744808157619)
          ·
            refine ⟨137107194630533617212236429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91404796420355744808157619 137107194630533617212236429)
            ·
              refine ⟨51415197986450106454588661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137107194630533617212236429 51415197986450106454588661)
              ·
                refine ⟨4820174811229697480117687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51415197986450106454588661 4820174811229697480117687)
                ·
                  refine ⟨7230262216844546220176531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820174811229697480117687 7230262216844546220176531)
                  ·
                    refine ⟨10845393325266819330264797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7230262216844546220176531 10845393325266819330264797)
                    ·
                      refine ⟨4067022496975057248849299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10845393325266819330264797 4067022496975057248849299)
                      ·
                        rfl

theorem cell23_7920498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_7920498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920498 prefixEnd_7920498 := by exact prefixLift 7920498
  have htrace : WordTrace (prefixWord ++ tailWord_7920498) baseStart_7920498 baseEnd_7920498 := by
    simpa [prefixWord, tailWord_7920498, baseEnd_7920498] using wordTrace_append hprefix tailTrace_7920498
  have hstable : (prefixWord ++ tailWord_7920498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920498).length < 2 ^ (prefixWord ++ tailWord_7920498).sum := by decide
  have hdescent : baseEnd_7920498 < baseStart_7920498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920501 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_7920501 : Nat := 118140960795 + 7920501 * 2 ^ 59
def prefixEnd_7920501 : Nat := 4983230072969 + 3 ^ 40 * 7920501 * 2
def baseEnd_7920501 : Nat := 1355674679139006912370595

theorem tailTrace_7920501 : CollatzResearch.WordTrace tailWord_7920501 prefixEnd_7920501 1355674679139006912370595 := by
  unfold tailWord_7920501
  simp only [CollatzResearch.WordTrace]
  refine ⟨288884404278385065720857357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192589602852256710480571571 288884404278385065720857357)
  ·
    refine ⟨108331651604394399645321509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288884404278385065720857357 108331651604394399645321509)
    ·
      refine ⟨20312184675823949933497783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108331651604394399645321509 20312184675823949933497783)
      ·
        refine ⟨30468277013735924900246675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20312184675823949933497783 30468277013735924900246675)
        ·
          refine ⟨45702415520603887350370013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30468277013735924900246675 45702415520603887350370013)
          ·
            refine ⟨17138405820226457756388755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45702415520603887350370013 17138405820226457756388755)
            ·
              refine ⟨25707608730339686634583133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17138405820226457756388755 25707608730339686634583133)
              ·
                refine ⟨9640353273877382487968675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25707608730339686634583133 9640353273877382487968675)
                ·
                  refine ⟨14460529910816073731953013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9640353273877382487968675 14460529910816073731953013)
                  ·
                    refine ⟨1355674679139006912370595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14460529910816073731953013 1355674679139006912370595)
                    ·
                      rfl

theorem cell23_7920501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_7920501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920501 prefixEnd_7920501 := by exact prefixLift 7920501
  have htrace : WordTrace (prefixWord ++ tailWord_7920501) baseStart_7920501 baseEnd_7920501 := by
    simpa [prefixWord, tailWord_7920501, baseEnd_7920501] using wordTrace_append hprefix tailTrace_7920501
  have hstable : (prefixWord ++ tailWord_7920501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920501).length < 2 ^ (prefixWord ++ tailWord_7920501).sum := by decide
  have hdescent : baseEnd_7920501 < baseStart_7920501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920524 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 5, 2, 3]
def baseStart_7920524 : Nat := 118140960795 + 7920524 * 2 ^ 59
def prefixEnd_7920524 : Nat := 4983230072969 + 3 ^ 40 * 7920524 * 2
def baseEnd_7920524 : Nat := 4067035847472074147124179

theorem tailTrace_7920524 : CollatzResearch.WordTrace tailWord_7920524 prefixEnd_7920524 4067035847472074147124179 := by
  unfold tailWord_7920524
  simp only [CollatzResearch.WordTrace]
  refine ⟨144442621578650870324472313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192590162104867827099296417 144442621578650870324472313)
  ·
    refine ⟨108331966183988152743354235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144442621578650870324472313 108331966183988152743354235)
    ·
      refine ⟨162497949275982229115031353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108331966183988152743354235 162497949275982229115031353)
      ·
        refine ⟨121873461956986671836273515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162497949275982229115031353 121873461956986671836273515)
        ·
          refine ⟨182810192935480007754410273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121873461956986671836273515 182810192935480007754410273)
          ·
            refine ⟨137107644701610005815807705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182810192935480007754410273 137107644701610005815807705)
            ·
              refine ⟨102830733526207504361855779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137107644701610005815807705 102830733526207504361855779)
              ·
                refine ⟨154246100289311256542783669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102830733526207504361855779 154246100289311256542783669)
                ·
                  refine ⟨14460571902122930300885969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154246100289311256542783669 14460571902122930300885969)
                  ·
                    refine ⟨10845428926592197725664477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14460571902122930300885969 10845428926592197725664477)
                    ·
                      refine ⟨4067035847472074147124179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10845428926592197725664477 4067035847472074147124179)
                      ·
                        rfl

theorem cell23_7920524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_7920524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920524 prefixEnd_7920524 := by exact prefixLift 7920524
  have htrace : WordTrace (prefixWord ++ tailWord_7920524) baseStart_7920524 baseEnd_7920524 := by
    simpa [prefixWord, tailWord_7920524, baseEnd_7920524] using wordTrace_append hprefix tailTrace_7920524
  have hstable : (prefixWord ++ tailWord_7920524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920524).length < 2 ^ (prefixWord ++ tailWord_7920524).sum := by decide
  have hdescent : baseEnd_7920524 < baseStart_7920524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920538 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4]
def baseStart_7920538 : Nat := 118140960795 + 7920538 * 2 ^ 59
def prefixEnd_7920538 : Nat := 4983230072969 + 3 ^ 40 * 7920538 * 2
def baseEnd_7920538 : Nat := 4067043036201237092349115

theorem tailTrace_7920538 : CollatzResearch.WordTrace tailWord_7920538 prefixEnd_7920538 4067043036201237092349115 := by
  unfold tailWord_7920538
  simp only [CollatzResearch.WordTrace]
  refine ⟨72221438444812755259988567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192590502519500680693302845 72221438444812755259988567)
  ·
    refine ⟨108332157667219132889982851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72221438444812755259988567 108332157667219132889982851)
    ·
      refine ⟨162498236500828699334974277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108332157667219132889982851 162498236500828699334974277)
      ·
        refine ⟨30468419343905381125307677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162498236500828699334974277 30468419343905381125307677)
        ·
          refine ⟨11425657253964517921990379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30468419343905381125307677 11425657253964517921990379)
          ·
            refine ⟨17138485880946776882985569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11425657253964517921990379 17138485880946776882985569)
            ·
              refine ⟨12853864410710082662239177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17138485880946776882985569 12853864410710082662239177)
              ·
                refine ⟨9640398308032561996679383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12853864410710082662239177 9640398308032561996679383)
                ·
                  refine ⟨14460597462048842995019075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9640398308032561996679383 14460597462048842995019075)
                  ·
                    refine ⟨21690896193073264492528613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14460597462048842995019075 21690896193073264492528613)
                    ·
                      refine ⟨4067043036201237092349115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21690896193073264492528613 4067043036201237092349115)
                      ·
                        rfl

theorem cell23_7920538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_7920538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920538 prefixEnd_7920538 := by exact prefixLift 7920538
  have htrace : WordTrace (prefixWord ++ tailWord_7920538) baseStart_7920538 baseEnd_7920538 := by
    simpa [prefixWord, tailWord_7920538, baseEnd_7920538] using wordTrace_append hprefix tailTrace_7920538
  have hstable : (prefixWord ++ tailWord_7920538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920538).length < 2 ^ (prefixWord ++ tailWord_7920538).sum := by decide
  have hdescent : baseEnd_7920538 < baseStart_7920538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920544 : List Nat := [2, 1, 1, 4, 1, 1, 6, 7]
def baseStart_7920544 : Nat := 118140960795 + 7920544 * 2 ^ 59
def prefixEnd_7920544 : Nat := 4983230072969 + 3 ^ 40 * 7920544 * 2
def baseEnd_7920544 : Nat := 150631337669820891439781

theorem tailTrace_7920544 : CollatzResearch.WordTrace tailWord_7920544 prefixEnd_7920544 150631337669820891439781 := by
  unfold tailWord_7920544
  simp only [CollatzResearch.WordTrace]
  refine ⟨144442986308614642032336343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192590648411486189376448457 144442986308614642032336343)
  ·
    refine ⟨216664479462921963048504515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144442986308614642032336343 216664479462921963048504515)
    ·
      refine ⟨324996719194382944572756773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216664479462921963048504515 324996719194382944572756773)
      ·
        refine ⟨60936884848946802107391895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324996719194382944572756773 60936884848946802107391895)
        ·
          refine ⟨91405327273420203161087843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60936884848946802107391895 91405327273420203161087843)
          ·
            refine ⟨137107990910130304741631765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91405327273420203161087843 137107990910130304741631765)
            ·
              refine ⟨6426937073912358034763989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137107990910130304741631765 6426937073912358034763989)
              ·
                refine ⟨150631337669820891439781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6426937073912358034763989 150631337669820891439781)
                ·
                  rfl

theorem cell23_7920544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 7].length) (baseStart_7920544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920544 prefixEnd_7920544 := by exact prefixLift 7920544
  have htrace : WordTrace (prefixWord ++ tailWord_7920544) baseStart_7920544 baseEnd_7920544 := by
    simpa [prefixWord, tailWord_7920544, baseEnd_7920544] using wordTrace_append hprefix tailTrace_7920544
  have hstable : (prefixWord ++ tailWord_7920544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920544).length < 2 ^ (prefixWord ++ tailWord_7920544).sum := by decide
  have hdescent : baseEnd_7920544 < baseStart_7920544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920561 : List Nat := [1, 2, 2, 4, 4, 1, 9]
def baseStart_7920561 : Nat := 118140960795 + 7920561 * 2 ^ 59
def prefixEnd_7920561 : Nat := 4983230072969 + 3 ^ 40 * 7920561 * 2
def baseEnd_7920561 : Nat := 50210553657485067930389

theorem tailTrace_7920561 : CollatzResearch.WordTrace tailWord_7920561 prefixEnd_7920561 50210553657485067930389 := by
  unfold tailWord_7920561
  simp only [CollatzResearch.WordTrace]
  refine ⟨288886592658167695968041537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192591061772111797312027691 288886592658167695968041537)
  ·
    refine ⟨216664944493625771976031153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288886592658167695968041537 216664944493625771976031153)
    ·
      refine ⟨162498708370219328982023365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216664944493625771976031153 162498708370219328982023365)
      ·
        refine ⟨30468507819416124184129381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162498708370219328982023365 30468507819416124184129381)
        ·
          refine ⟨5712845216140523284524259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30468507819416124184129381 5712845216140523284524259)
          ·
            refine ⟨8569267824210784926786389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712845216140523284524259 8569267824210784926786389)
            ·
              refine ⟨50210553657485067930389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8569267824210784926786389 50210553657485067930389)
              ·
                rfl

theorem cell23_7920561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 9].length) (baseStart_7920561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920561 prefixEnd_7920561 := by exact prefixLift 7920561
  have htrace : WordTrace (prefixWord ++ tailWord_7920561) baseStart_7920561 baseEnd_7920561 := by
    simpa [prefixWord, tailWord_7920561, baseEnd_7920561] using wordTrace_append hprefix tailTrace_7920561
  have hstable : (prefixWord ++ tailWord_7920561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920561).length < 2 ^ (prefixWord ++ tailWord_7920561).sum := by decide
  have hdescent : baseEnd_7920561 < baseStart_7920561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920566 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7920566 : Nat := 118140960795 + 7920566 * 2 ^ 59
def prefixEnd_7920566 : Nat := 4983230072969 + 3 ^ 40 * 7920566 * 2
def baseEnd_7920566 : Nat := 4067057413659562982798987

theorem tailTrace_7920566 : CollatzResearch.WordTrace tailWord_7920566 prefixEnd_7920566 4067057413659562982798987 := by
  unfold tailWord_7920566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18055423438946848863873347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192591183348766387881315701 18055423438946848863873347)
  ·
    refine ⟨27083135158420273295810021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18055423438946848863873347 27083135158420273295810021)
    ·
      refine ⟨5078087842203801242964379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27083135158420273295810021 5078087842203801242964379)
      ·
        refine ⟨7617131763305701864446569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078087842203801242964379 7617131763305701864446569)
        ·
          refine ⟨5712848822479276398334927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7617131763305701864446569 5712848822479276398334927)
          ·
            refine ⟨8569273233718914597502391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712848822479276398334927 8569273233718914597502391)
            ·
              refine ⟨12853909850578371896253587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569273233718914597502391 12853909850578371896253587)
              ·
                refine ⟨19280864775867557844380381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12853909850578371896253587 19280864775867557844380381)
                ·
                  refine ⟨7230324290950334191642643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19280864775867557844380381 7230324290950334191642643)
                  ·
                    refine ⟨10845486436425501287463965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7230324290950334191642643 10845486436425501287463965)
                    ·
                      refine ⟨4067057413659562982798987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10845486436425501287463965 4067057413659562982798987)
                      ·
                        rfl

theorem cell23_7920566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7920566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920566 prefixEnd_7920566 := by exact prefixLift 7920566
  have htrace : WordTrace (prefixWord ++ tailWord_7920566) baseStart_7920566 baseEnd_7920566 := by
    simpa [prefixWord, tailWord_7920566, baseEnd_7920566] using wordTrace_append hprefix tailTrace_7920566
  have hstable : (prefixWord ++ tailWord_7920566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920566).length < 2 ^ (prefixWord ++ tailWord_7920566).sum := by decide
  have hdescent : baseEnd_7920566 < baseStart_7920566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920574 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_7920574 : Nat := 118140960795 + 7920574 * 2 ^ 59
def prefixEnd_7920574 : Nat := 4983230072969 + 3 ^ 40 * 7920574 * 2
def baseEnd_7920574 : Nat := 1355687173834932983832983

theorem tailTrace_7920574 : CollatzResearch.WordTrace tailWord_7920574 prefixEnd_7920574 1355687173834932983832983 := by
  unfold tailWord_7920574
  simp only [CollatzResearch.WordTrace]
  refine ⟨36110883350890074898533097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192591377871413732792176517 36110883350890074898533097)
  ·
    refine ⟨27083162513167556173899823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36110883350890074898533097 27083162513167556173899823)
    ·
      refine ⟨40624743769751334260849735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27083162513167556173899823 40624743769751334260849735)
      ·
        refine ⟨60937115654627001391274603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40624743769751334260849735 60937115654627001391274603)
        ·
          refine ⟨91405673481940502086911905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60937115654627001391274603 91405673481940502086911905)
          ·
            refine ⟨68554255111455376565183929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91405673481940502086911905 68554255111455376565183929)
            ·
              refine ⟨51415691333591532423887947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68554255111455376565183929 51415691333591532423887947)
              ·
                refine ⟨77123537000387298635831921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51415691333591532423887947 77123537000387298635831921)
                ·
                  refine ⟨57842652750290473976873941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77123537000387298635831921 57842652750290473976873941)
                  ·
                    refine ⟨1355687173834932983832983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57842652750290473976873941 1355687173834932983832983)
                    ·
                      rfl

theorem cell23_7920574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_7920574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920574 prefixEnd_7920574 := by exact prefixLift 7920574
  have htrace : WordTrace (prefixWord ++ tailWord_7920574) baseStart_7920574 baseEnd_7920574 := by
    simpa [prefixWord, tailWord_7920574, baseEnd_7920574] using wordTrace_append hprefix tailTrace_7920574
  have hstable : (prefixWord ++ tailWord_7920574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920574).length < 2 ^ (prefixWord ++ tailWord_7920574).sum := by decide
  have hdescent : baseEnd_7920574 < baseStart_7920574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920588 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 2, 1, 3]
def baseStart_7920588 : Nat := 118140960795 + 7920588 * 2 ^ 59
def prefixEnd_7920588 : Nat := 4983230072969 + 3 ^ 40 * 7920588 * 2
def baseEnd_7920588 : Nat := 4067068710233961896723885

theorem tailTrace_7920588 : CollatzResearch.WordTrace tailWord_7920588 prefixEnd_7920588 4067068710233961896723885 := by
  unfold tailWord_7920588
  simp only [CollatzResearch.WordTrace]
  refine ⟨144443788714534939789637209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192591718286046586386182945 144443788714534939789637209)
  ·
    refine ⟨108332841535901204842227907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144443788714534939789637209 108332841535901204842227907)
    ·
      refine ⟨162499262303851807263341861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108332841535901204842227907 162499262303851807263341861)
      ·
        refine ⟨30468611681972213861876599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162499262303851807263341861 30468611681972213861876599)
        ·
          refine ⟨45702917522958320792814899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30468611681972213861876599 45702917522958320792814899)
          ·
            refine ⟨68554376284437481189222349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45702917522958320792814899 68554376284437481189222349)
            ·
              refine ⟨25707891106664055445958381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68554376284437481189222349 25707891106664055445958381)
              ·
                refine ⟨9640459164999020792234393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25707891106664055445958381 9640459164999020792234393)
                ·
                  refine ⟨7230344373749265594175795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9640459164999020792234393 7230344373749265594175795)
                  ·
                    refine ⟨10845516560623898391263693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7230344373749265594175795 10845516560623898391263693)
                    ·
                      refine ⟨4067068710233961896723885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10845516560623898391263693 4067068710233961896723885)
                      ·
                        rfl

theorem cell23_7920588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_7920588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920588 prefixEnd_7920588 := by exact prefixLift 7920588
  have htrace : WordTrace (prefixWord ++ tailWord_7920588) baseStart_7920588 baseEnd_7920588 := by
    simpa [prefixWord, tailWord_7920588, baseEnd_7920588] using wordTrace_append hprefix tailTrace_7920588
  have hstable : (prefixWord ++ tailWord_7920588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920588).length < 2 ^ (prefixWord ++ tailWord_7920588).sum := by decide
  have hdescent : baseEnd_7920588 < baseStart_7920588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920589 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7920589 : Nat := 118140960795 + 7920589 * 2 ^ 59
def prefixEnd_7920589 : Nat := 4983230072969 + 3 ^ 40 * 7920589 * 2
def baseEnd_7920589 : Nat := 4067069223714616392811381

theorem tailTrace_7920589 : CollatzResearch.WordTrace tailWord_7920589 prefixEnd_7920589 4067069223714616392811381 := by
  unfold tailWord_7920589
  simp only [CollatzResearch.WordTrace]
  refine ⟨288887613902066256750060821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192591742601377504500040547 288887613902066256750060821)
  ·
    refine ⟨13541606901659355785159101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 288887613902066256750060821 13541606901659355785159101)
    ·
      refine ⟨5078102588122258419434663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13541606901659355785159101 5078102588122258419434663)
      ·
        refine ⟨7617153882183387629151995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078102588122258419434663 7617153882183387629151995)
        ·
          refine ⟨11425730823275081443727993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617153882183387629151995 11425730823275081443727993)
          ·
            refine ⟨8569298117456311082795995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11425730823275081443727993 8569298117456311082795995)
            ·
              refine ⟨12853947176184466624193993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569298117456311082795995 12853947176184466624193993)
              ·
                refine ⟨9640460382138349968145495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12853947176184466624193993 9640460382138349968145495)
                ·
                  refine ⟨14460690573207524952218243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9640460382138349968145495 14460690573207524952218243)
                  ·
                    refine ⟨21691035859811287428327365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14460690573207524952218243 21691035859811287428327365)
                    ·
                      refine ⟨4067069223714616392811381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21691035859811287428327365 4067069223714616392811381)
                      ·
                        rfl

theorem cell23_7920589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7920589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920589 prefixEnd_7920589 := by exact prefixLift 7920589
  have htrace : WordTrace (prefixWord ++ tailWord_7920589) baseStart_7920589 baseEnd_7920589 := by
    simpa [prefixWord, tailWord_7920589, baseEnd_7920589] using wordTrace_append hprefix tailTrace_7920589
  have hstable : (prefixWord ++ tailWord_7920589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920589).length < 2 ^ (prefixWord ++ tailWord_7920589).sum := by decide
  have hdescent : baseEnd_7920589 < baseStart_7920589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920624 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_7920624 : Nat := 118140960795 + 7920624 * 2 ^ 59
def prefixEnd_7920624 : Nat := 4983230072969 + 3 ^ 40 * 7920624 * 2
def baseEnd_7920624 : Nat := 4067087195537523755873719

theorem tailTrace_7920624 : CollatzResearch.WordTrace tailWord_7920624 prefixEnd_7920624 4067087195537523755873719 := by
  unfold tailWord_7920624
  simp only [CollatzResearch.WordTrace]
  refine ⟨144444445228469728863792463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192592593637959638485056617 144444445228469728863792463)
  ·
    refine ⟨216666667842704593295688695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144444445228469728863792463 216666667842704593295688695)
    ·
      refine ⟨325000001764056889943533043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216666667842704593295688695 325000001764056889943533043)
      ·
        refine ⟨487500002646085334915299565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325000001764056889943533043 487500002646085334915299565)
        ·
          refine ⟨182812500992282000593237337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487500002646085334915299565 182812500992282000593237337)
          ·
            refine ⟨137109375744211500444928003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182812500992282000593237337 137109375744211500444928003)
            ·
              refine ⟨205664063616317250667392005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137109375744211500444928003 205664063616317250667392005)
              ·
                refine ⟨38562011928059484500136001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205664063616317250667392005 38562011928059484500136001)
                ·
                  refine ⟨28921508946044613375102001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38562011928059484500136001 28921508946044613375102001)
                  ·
                    refine ⟨21691131709533460031326501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28921508946044613375102001 21691131709533460031326501)
                    ·
                      refine ⟨4067087195537523755873719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21691131709533460031326501 4067087195537523755873719)
                      ·
                        rfl

theorem cell23_7920624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_7920624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920624 prefixEnd_7920624 := by exact prefixLift 7920624
  have htrace : WordTrace (prefixWord ++ tailWord_7920624) baseStart_7920624 baseEnd_7920624 := by
    simpa [prefixWord, tailWord_7920624, baseEnd_7920624] using wordTrace_append hprefix tailTrace_7920624
  have hstable : (prefixWord ++ tailWord_7920624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920624).length < 2 ^ (prefixWord ++ tailWord_7920624).sum := by decide
  have hdescent : baseEnd_7920624 < baseStart_7920624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920638 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7920638 : Nat := 118140960795 + 7920638 * 2 ^ 59
def prefixEnd_7920638 : Nat := 4983230072969 + 3 ^ 40 * 7920638 * 2
def baseEnd_7920638 : Nat := 1355698128088895567032885

theorem tailTrace_7920638 : CollatzResearch.WordTrace tailWord_7920638 prefixEnd_7920638 1355698128088895567032885 := by
  unfold tailWord_7920638
  simp only [CollatzResearch.WordTrace]
  refine ⟨36111175134861092264824321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192592934052592492079063045 36111175134861092264824321)
  ·
    refine ⟨27083381351145819198618241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36111175134861092264824321 27083381351145819198618241)
    ·
      refine ⟨20312536013359364398963681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27083381351145819198618241 20312536013359364398963681)
      ·
        refine ⟨15234402010019523299222761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20312536013359364398963681 15234402010019523299222761)
        ·
          refine ⟨11425801507514642474417071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15234402010019523299222761 11425801507514642474417071)
          ·
            refine ⟨17138702261271963711625607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11425801507514642474417071 17138702261271963711625607)
            ·
              refine ⟨25708053391907945567438411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17138702261271963711625607 25708053391907945567438411)
              ·
                refine ⟨38562080087861918351157617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25708053391907945567438411 38562080087861918351157617)
                ·
                  refine ⟨28921560065896438763368213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38562080087861918351157617 28921560065896438763368213)
                  ·
                    refine ⟨1355698128088895567032885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28921560065896438763368213 1355698128088895567032885)
                    ·
                      rfl

theorem cell23_7920638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7920638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920638 prefixEnd_7920638 := by exact prefixLift 7920638
  have htrace : WordTrace (prefixWord ++ tailWord_7920638) baseStart_7920638 baseEnd_7920638 := by
    simpa [prefixWord, tailWord_7920638, baseEnd_7920638] using wordTrace_append hprefix tailTrace_7920638
  have hstable : (prefixWord ++ tailWord_7920638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920638).length < 2 ^ (prefixWord ++ tailWord_7920638).sum := by decide
  have hdescent : baseEnd_7920638 < baseStart_7920638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920641 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_7920641 : Nat := 118140960795 + 7920641 * 2 ^ 59
def prefixEnd_7920641 : Nat := 4983230072969 + 3 ^ 40 * 7920641 * 2
def baseEnd_7920641 : Nat := 4067095924708650189361141

theorem tailTrace_7920641 : CollatzResearch.WordTrace tailWord_7920641 prefixEnd_7920641 4067095924708650189361141 := by
  unfold tailWord_7920641
  simp only [CollatzResearch.WordTrace]
  refine ⟨288889510497877869630953777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192593006998585246420635851 288889510497877869630953777)
  ·
    refine ⟨216667132873408402223215333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288889510497877869630953777 216667132873408402223215333)
    ·
      refine ⟨40625087413764075416852875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216667132873408402223215333 40625087413764075416852875)
      ·
        refine ⟨60937631120646113125279313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40625087413764075416852875 60937631120646113125279313)
        ·
          refine ⟨45703223340484584843959485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60937631120646113125279313 45703223340484584843959485)
          ·
            refine ⟨17138708752681719316484807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45703223340484584843959485 17138708752681719316484807)
            ·
              refine ⟨25708063129022578974727211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17138708752681719316484807 25708063129022578974727211)
              ·
                refine ⟨38562094693533868462090817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25708063129022578974727211 38562094693533868462090817)
                ·
                  refine ⟨28921571020150401346568113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38562094693533868462090817 28921571020150401346568113)
                  ·
                    refine ⟨21691178265112801009926085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28921571020150401346568113 21691178265112801009926085)
                    ·
                      refine ⟨4067095924708650189361141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21691178265112801009926085 4067095924708650189361141)
                      ·
                        rfl

theorem cell23_7920641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_7920641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920641 prefixEnd_7920641 := by exact prefixLift 7920641
  have htrace : WordTrace (prefixWord ++ tailWord_7920641) baseStart_7920641 baseEnd_7920641 := by
    simpa [prefixWord, tailWord_7920641, baseEnd_7920641] using wordTrace_append hprefix tailTrace_7920641
  have hstable : (prefixWord ++ tailWord_7920641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920641).length < 2 ^ (prefixWord ++ tailWord_7920641).sum := by decide
  have hdescent : baseEnd_7920641 < baseStart_7920641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920679 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_7920679 : Nat := 118140960795 + 7920679 * 2 ^ 59
def prefixEnd_7920679 : Nat := 4983230072969 + 3 ^ 40 * 7920679 * 2
def baseEnd_7920679 : Nat := 4067115436973521040685967

theorem tailTrace_7920679 : CollatzResearch.WordTrace tailWord_7920679 prefixEnd_7920679 4067115436973521040685967 := by
  unfold tailWord_7920679
  simp only [CollatzResearch.WordTrace]
  refine ⟨288890896471740202120837091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192593930981160134747224727 288890896471740202120837091)
  ·
    refine ⟨433336344707610303181255637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288890896471740202120837091 433336344707610303181255637)
    ·
      refine ⟨10156320579084616480810679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 433336344707610303181255637 10156320579084616480810679)
      ·
        refine ⟨15234480868626924721216019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156320579084616480810679 15234480868626924721216019)
        ·
          refine ⟨22851721302940387081824029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15234480868626924721216019 22851721302940387081824029)
          ·
            refine ⟨8569395488602645155684011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22851721302940387081824029 8569395488602645155684011)
            ·
              refine ⟨12854093232903967733526017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569395488602645155684011 12854093232903967733526017)
              ·
                refine ⟨9640569924677975800144513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12854093232903967733526017 9640569924677975800144513)
                ·
                  refine ⟨7230427443508481850108385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9640569924677975800144513 7230427443508481850108385)
                  ·
                    refine ⟨5422820582631361387581289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7230427443508481850108385 5422820582631361387581289)
                    ·
                      refine ⟨4067115436973521040685967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5422820582631361387581289 4067115436973521040685967)
                      ·
                        rfl

theorem cell23_7920679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_7920679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920679 prefixEnd_7920679 := by exact prefixLift 7920679
  have htrace : WordTrace (prefixWord ++ tailWord_7920679) baseStart_7920679 baseEnd_7920679 := by
    simpa [prefixWord, tailWord_7920679, baseEnd_7920679] using wordTrace_append hprefix tailTrace_7920679
  have hstable : (prefixWord ++ tailWord_7920679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920679).length < 2 ^ (prefixWord ++ tailWord_7920679).sum := by decide
  have hdescent : baseEnd_7920679 < baseStart_7920679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920701 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_7920701 : Nat := 118140960795 + 7920701 * 2 ^ 59
def prefixEnd_7920701 : Nat := 4983230072969 + 3 ^ 40 * 7920701 * 2
def baseEnd_7920701 : Nat := 4067126733547919954610865

theorem tailTrace_7920701 : CollatzResearch.WordTrace tailWord_7920701 prefixEnd_7920701 4067126733547919954610865 := by
  unfold tailWord_7920701
  simp only [CollatzResearch.WordTrace]
  refine ⟨288891698877660499878137957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192594465918440333252091971 288891698877660499878137957)
  ·
    refine ⟨54167193539561343727150867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288891698877660499878137957 54167193539561343727150867)
    ·
      refine ⟨81250790309342015590726301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54167193539561343727150867 81250790309342015590726301)
      ·
        refine ⟨30469046366003255846522363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81250790309342015590726301 30469046366003255846522363)
        ·
          refine ⟨45703569549004883769783545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30469046366003255846522363 45703569549004883769783545)
          ·
            refine ⟨34277677161753662827337659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45703569549004883769783545 34277677161753662827337659)
            ·
              refine ⟨51416515742630494241006489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34277677161753662827337659 51416515742630494241006489)
              ·
                refine ⟨38562386806972870680754867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51416515742630494241006489 38562386806972870680754867)
                ·
                  refine ⟨57843580210459306021132301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38562386806972870680754867 57843580210459306021132301)
                  ·
                    refine ⟨21691342578922239757924613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57843580210459306021132301 21691342578922239757924613)
                    ·
                      refine ⟨4067126733547919954610865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21691342578922239757924613 4067126733547919954610865)
                      ·
                        rfl

theorem cell23_7920701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_7920701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920701 prefixEnd_7920701 := by exact prefixLift 7920701
  have htrace : WordTrace (prefixWord ++ tailWord_7920701) baseStart_7920701 baseEnd_7920701 := by
    simpa [prefixWord, tailWord_7920701, baseEnd_7920701] using wordTrace_append hprefix tailTrace_7920701
  have hstable : (prefixWord ++ tailWord_7920701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920701).length < 2 ^ (prefixWord ++ tailWord_7920701).sum := by decide
  have hdescent : baseEnd_7920701 < baseStart_7920701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920721 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 1, 4, 3]
def baseStart_7920721 : Nat := 118140960795 + 7920721 * 2 ^ 59
def prefixEnd_7920721 : Nat := 4983230072969 + 3 ^ 40 * 7920721 * 2
def baseEnd_7920721 : Nat := 4067137003161009876360773

theorem tailTrace_7920721 : CollatzResearch.WordTrace tailWord_7920721 prefixEnd_7920721 4067137003161009876360773 := by
  unfold tailWord_7920721
  simp only [CollatzResearch.WordTrace]
  refine ⟨288892428337588043293866017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192594952225058695529244011 288892428337588043293866017)
  ·
    refine ⟨216669321253191032470399513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288892428337588043293866017 216669321253191032470399513)
    ·
      refine ⟨162501990939893274352799635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216669321253191032470399513 162501990939893274352799635)
      ·
        refine ⟨243752986409839911529199453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162501990939893274352799635 243752986409839911529199453)
        ·
          refine ⟨91407369903689966823449795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243752986409839911529199453 91407369903689966823449795)
          ·
            refine ⟨137111054855534950235174693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91407369903689966823449795 137111054855534950235174693)
            ·
              refine ⟨25708322785412803169095255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137111054855534950235174693 25708322785412803169095255)
              ·
                refine ⟨38562484178119204753642883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25708322785412803169095255 38562484178119204753642883)
                ·
                  refine ⟨57843726267178807130464325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38562484178119204753642883 57843726267178807130464325)
                  ·
                    refine ⟨10845698675096026336962061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57843726267178807130464325 10845698675096026336962061)
                    ·
                      refine ⟨4067137003161009876360773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10845698675096026336962061 4067137003161009876360773)
                      ·
                        rfl

theorem cell23_7920721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_7920721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920721 prefixEnd_7920721 := by exact prefixLift 7920721
  have htrace : WordTrace (prefixWord ++ tailWord_7920721) baseStart_7920721 baseEnd_7920721 := by
    simpa [prefixWord, tailWord_7920721, baseEnd_7920721] using wordTrace_append hprefix tailTrace_7920721
  have hstable : (prefixWord ++ tailWord_7920721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920721).length < 2 ^ (prefixWord ++ tailWord_7920721).sum := by decide
  have hdescent : baseEnd_7920721 < baseStart_7920721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920741 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 6]
def baseStart_7920741 : Nat := 118140960795 + 7920741 * 2 ^ 59
def prefixEnd_7920741 : Nat := 4983230072969 + 3 ^ 40 * 7920741 * 2
def baseEnd_7920741 : Nat := 451905252530455533123409

theorem tailTrace_7920741 : CollatzResearch.WordTrace tailWord_7920741 prefixEnd_7920741 451905252530455533123409 := by
  unfold tailWord_7920741
  simp only [CollatzResearch.WordTrace]
  refine ⟨288893157797515586709594077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192595438531677057806396051 288893157797515586709594077)
  ·
    refine ⟨108334934174068345016097779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288893157797515586709594077 108334934174068345016097779)
    ·
      refine ⟨162502401261102517524146669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108334934174068345016097779 162502401261102517524146669)
      ·
        refine ⟨60938400472913444071555001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162502401261102517524146669 60938400472913444071555001)
        ·
          refine ⟨45703800354685083053666251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60938400472913444071555001 45703800354685083053666251)
          ·
            refine ⟨68555700532027624580499377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45703800354685083053666251 68555700532027624580499377)
            ·
              refine ⟨51416775399020718435374533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68555700532027624580499377 51416775399020718435374533)
              ·
                refine ⟨9640645387316384706632725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51416775399020718435374533 9640645387316384706632725)
                ·
                  refine ⟨451905252530455533123409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9640645387316384706632725 451905252530455533123409)
                  ·
                    rfl

theorem cell23_7920741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_7920741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920741 prefixEnd_7920741 := by exact prefixLift 7920741
  have htrace : WordTrace (prefixWord ++ tailWord_7920741) baseStart_7920741 baseEnd_7920741 := by
    simpa [prefixWord, tailWord_7920741, baseEnd_7920741] using wordTrace_append hprefix tailTrace_7920741
  have hstable : (prefixWord ++ tailWord_7920741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920741).length < 2 ^ (prefixWord ++ tailWord_7920741).sum := by decide
  have hdescent : baseEnd_7920741 < baseStart_7920741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920758 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_7920758 : Nat := 118140960795 + 7920758 * 2 ^ 59
def prefixEnd_7920758 : Nat := 4983230072969 + 3 ^ 40 * 7920758 * 2
def baseEnd_7920758 : Nat := 451906222438358470177567

theorem tailTrace_7920758 : CollatzResearch.WordTrace tailWord_7920758 prefixEnd_7920758 451906222438358470177567 := by
  unfold tailWord_7920758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18055861114903374913310183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192595851892302665741975285 18055861114903374913310183)
  ·
    refine ⟨27083791672355062369965275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18055861114903374913310183 27083791672355062369965275)
    ·
      refine ⟨40625687508532593554947913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27083791672355062369965275 40625687508532593554947913)
      ·
        refine ⟨30469265631399445166210935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40625687508532593554947913 30469265631399445166210935)
        ·
          refine ⟨45703898447099167749316403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30469265631399445166210935 45703898447099167749316403)
          ·
            refine ⟨68555847670648751623974605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45703898447099167749316403 68555847670648751623974605)
            ·
              refine ⟨25708442876493281858990477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68555847670648751623974605 25708442876493281858990477)
              ·
                refine ⟨9640666078684980697121429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25708442876493281858990477 9640666078684980697121429)
                ·
                  refine ⟨451906222438358470177567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9640666078684980697121429 451906222438358470177567)
                  ·
                    rfl

theorem cell23_7920758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_7920758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920758 prefixEnd_7920758 := by exact prefixLift 7920758
  have htrace : WordTrace (prefixWord ++ tailWord_7920758) baseStart_7920758 baseEnd_7920758 := by
    simpa [prefixWord, tailWord_7920758, baseEnd_7920758] using wordTrace_append hprefix tailTrace_7920758
  have hstable : (prefixWord ++ tailWord_7920758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920758).length < 2 ^ (prefixWord ++ tailWord_7920758).sum := by decide
  have hdescent : baseEnd_7920758 < baseStart_7920758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920768 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 3, 1, 3]
def baseStart_7920768 : Nat := 118140960795 + 7920768 * 2 ^ 59
def prefixEnd_7920768 : Nat := 4983230072969 + 3 ^ 40 * 7920768 * 2
def baseEnd_7920768 : Nat := 4067161136751771192473057

theorem tailTrace_7920768 : CollatzResearch.WordTrace tailWord_7920768 prefixEnd_7920768 4067161136751771192473057 := by
  unfold tailWord_7920768
  simp only [CollatzResearch.WordTrace]
  refine ⟨144447071284208885160413479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192596095045611846880551305 144447071284208885160413479)
  ·
    refine ⟨216670606926313327740620219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144447071284208885160413479 216670606926313327740620219)
    ·
      refine ⟨325005910389469991610930329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216670606926313327740620219 325005910389469991610930329)
      ·
        refine ⟨243754432792102493708197747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325005910389469991610930329 243754432792102493708197747)
        ·
          refine ⟨365631649188153740562296621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243754432792102493708197747 365631649188153740562296621)
          ·
            refine ⟨137111868445557652710861233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365631649188153740562296621 137111868445557652710861233)
            ·
              refine ⟨102833901334168239533145925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137111868445557652710861233 102833901334168239533145925)
              ·
                refine ⟨19281356500156544912464861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102833901334168239533145925 19281356500156544912464861)
                ·
                  refine ⟨7230508687558704342174323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19281356500156544912464861 7230508687558704342174323)
                  ·
                    refine ⟨10845763031338056513261485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7230508687558704342174323 10845763031338056513261485)
                    ·
                      refine ⟨4067161136751771192473057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10845763031338056513261485 4067161136751771192473057)
                      ·
                        rfl

theorem cell23_7920768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_7920768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920768 prefixEnd_7920768 := by exact prefixLift 7920768
  have htrace : WordTrace (prefixWord ++ tailWord_7920768) baseStart_7920768 baseEnd_7920768 := by
    simpa [prefixWord, tailWord_7920768, baseEnd_7920768] using wordTrace_append hprefix tailTrace_7920768
  have hstable : (prefixWord ++ tailWord_7920768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920768).length < 2 ^ (prefixWord ++ tailWord_7920768).sum := by decide
  have hdescent : baseEnd_7920768 < baseStart_7920768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920771 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 3, 5]
def baseStart_7920771 : Nat := 118140960795 + 7920771 * 2 ^ 59
def prefixEnd_7920771 : Nat := 4983230072969 + 3 ^ 40 * 7920771 * 2
def baseEnd_7920771 : Nat := 1355720892397911560245181

theorem tailTrace_7920771 : CollatzResearch.WordTrace tailWord_7920771 prefixEnd_7920771 1355720892397911560245181 := by
  unfold tailWord_7920771
  simp only [CollatzResearch.WordTrace]
  refine ⟨288894251987406901833186167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192596167991604601222124111 288894251987406901833186167)
  ·
    refine ⟨433341377981110352749779251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288894251987406901833186167 433341377981110352749779251)
    ·
      refine ⟨650012066971665529124668877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433341377981110352749779251 650012066971665529124668877)
      ·
        refine ⟨243754525114374573421750829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 650012066971665529124668877 243754525114374573421750829)
        ·
          refine ⟨91407946917890465033156561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243754525114374573421750829 91407946917890465033156561)
          ·
            refine ⟨68555960188417848774867421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91407946917890465033156561 68555960188417848774867421)
            ·
              refine ⟨25708485070656693290575283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68555960188417848774867421 25708485070656693290575283)
              ·
                refine ⟨38562727605985039935862925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25708485070656693290575283 38562727605985039935862925)
                ·
                  refine ⟨14461022852244389975948597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38562727605985039935862925 14461022852244389975948597)
                  ·
                    refine ⟨1355720892397911560245181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14461022852244389975948597 1355720892397911560245181)
                    ·
                      rfl

theorem cell23_7920771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 5].length) (baseStart_7920771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920771 prefixEnd_7920771 := by exact prefixLift 7920771
  have htrace : WordTrace (prefixWord ++ tailWord_7920771) baseStart_7920771 baseEnd_7920771 := by
    simpa [prefixWord, tailWord_7920771, baseEnd_7920771] using wordTrace_append hprefix tailTrace_7920771
  have hstable : (prefixWord ++ tailWord_7920771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920771).length < 2 ^ (prefixWord ++ tailWord_7920771).sum := by decide
  have hdescent : baseEnd_7920771 < baseStart_7920771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920801 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 3, 6]
def baseStart_7920801 : Nat := 118140960795 + 7920801 * 2 ^ 59
def prefixEnd_7920801 : Nat := 4983230072969 + 3 ^ 40 * 7920801 * 2
def baseEnd_7920801 : Nat := 1355726027204456521120135

theorem tailTrace_7920801 : CollatzResearch.WordTrace tailWord_7920801 prefixEnd_7920801 1355726027204456521120135 := by
  unfold tailWord_7920801
  simp only [CollatzResearch.WordTrace]
  refine ⟨288895346177298216956778257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192596897451532144637852171 288895346177298216956778257)
  ·
    refine ⟨216671509632973662717583693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288895346177298216956778257 216671509632973662717583693)
    ·
      refine ⟨81251816112365123519093885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216671509632973662717583693 81251816112365123519093885)
      ·
        refine ⟨30469431042136921319660207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81251816112365123519093885 30469431042136921319660207)
        ·
          refine ⟨45704146563205381979490311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30469431042136921319660207 45704146563205381979490311)
          ·
            refine ⟨68556219844808072969235467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45704146563205381979490311 68556219844808072969235467)
            ·
              refine ⟨102834329767212109453853201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68556219844808072969235467 102834329767212109453853201)
              ·
                refine ⟨77125747325409082090389901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102834329767212109453853201 77125747325409082090389901)
                ·
                  refine ⟨28922155247028405783896213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77125747325409082090389901 28922155247028405783896213)
                  ·
                    refine ⟨1355726027204456521120135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28922155247028405783896213 1355726027204456521120135)
                    ·
                      rfl

theorem cell23_7920801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_7920801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920801 prefixEnd_7920801 := by exact prefixLift 7920801
  have htrace : WordTrace (prefixWord ++ tailWord_7920801) baseStart_7920801 baseEnd_7920801 := by
    simpa [prefixWord, tailWord_7920801, baseEnd_7920801] using wordTrace_append hprefix tailTrace_7920801
  have hstable : (prefixWord ++ tailWord_7920801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920801).length < 2 ^ (prefixWord ++ tailWord_7920801).sum := by decide
  have hdescent : baseEnd_7920801 < baseStart_7920801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920818 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_7920818 : Nat := 118140960795 + 7920818 * 2 ^ 59
def prefixEnd_7920818 : Nat := 4983230072969 + 3 ^ 40 * 7920818 * 2
def baseEnd_7920818 : Nat := 1355728936928165332282609

theorem tailTrace_7920818 : CollatzResearch.WordTrace tailWord_7920818 prefixEnd_7920818 1355728936928165332282609 := by
  unfold tailWord_7920818
  simp only [CollatzResearch.WordTrace]
  refine ⟨72223991554559157215036777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192597310812157752573431405 72223991554559157215036777)
  ·
    refine ⟨54167993665919367911277583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72223991554559157215036777 54167993665919367911277583)
    ·
      refine ⟨81251990498879051866916375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54167993665919367911277583 81251990498879051866916375)
      ·
        refine ⟨121877985748318577800374563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81251990498879051866916375 121877985748318577800374563)
        ·
          refine ⟨182816978622477866700561845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121877985748318577800374563 182816978622477866700561845)
          ·
            refine ⟨17139091745857300003177673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182816978622477866700561845 17139091745857300003177673)
            ·
              refine ⟨12854318809392975002383255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17139091745857300003177673 12854318809392975002383255)
              ·
                refine ⟨19281478214089462503574883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12854318809392975002383255 19281478214089462503574883)
                ·
                  refine ⟨28922217321134193755362325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19281478214089462503574883 28922217321134193755362325)
                  ·
                    refine ⟨1355728936928165332282609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28922217321134193755362325 1355728936928165332282609)
                    ·
                      rfl

theorem cell23_7920818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_7920818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920818 prefixEnd_7920818 := by exact prefixLift 7920818
  have htrace : WordTrace (prefixWord ++ tailWord_7920818) baseStart_7920818 baseEnd_7920818 := by
    simpa [prefixWord, tailWord_7920818, baseEnd_7920818] using wordTrace_append hprefix tailTrace_7920818
  have hstable : (prefixWord ++ tailWord_7920818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920818).length < 2 ^ (prefixWord ++ tailWord_7920818).sum := by decide
  have hdescent : baseEnd_7920818 < baseStart_7920818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920825 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 5, 2, 2]
def baseStart_7920825 : Nat := 118140960795 + 7920825 * 2 ^ 59
def prefixEnd_7920825 : Nat := 4983230072969 + 3 ^ 40 * 7920825 * 2
def baseEnd_7920825 : Nat := 4067190405149077469460295

theorem tailTrace_7920825 : CollatzResearch.WordTrace tailWord_7920825 prefixEnd_7920825 4067190405149077469460295 := by
  unfold tailWord_7920825
  simp only [CollatzResearch.WordTrace]
  refine ⟨288896221529211269055651929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192597481019474179370434619 288896221529211269055651929)
  ·
    refine ⟨216672166146908451791738947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288896221529211269055651929 216672166146908451791738947)
    ·
      refine ⟨325008249220362677687608421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216672166146908451791738947 325008249220362677687608421)
      ·
        refine ⟨60939046728818002066426579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325008249220362677687608421 60939046728818002066426579)
        ·
          refine ⟨91408570093227003099639869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60939046728818002066426579 91408570093227003099639869)
          ·
            refine ⟨34278213784960126162364951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91408570093227003099639869 34278213784960126162364951)
            ·
              refine ⟨51417320677440189243547427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34278213784960126162364951 51417320677440189243547427)
              ·
                refine ⟨77125981016160283865321141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51417320677440189243547427 77125981016160283865321141)
                ·
                  refine ⟨7230560720265026612373857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77125981016160283865321141 7230560720265026612373857)
                  ·
                    refine ⟨5422920540198769959280393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7230560720265026612373857 5422920540198769959280393)
                    ·
                      refine ⟨4067190405149077469460295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5422920540198769959280393 4067190405149077469460295)
                      ·
                        rfl

theorem cell23_7920825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_7920825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920825 prefixEnd_7920825 := by exact prefixLift 7920825
  have htrace : WordTrace (prefixWord ++ tailWord_7920825) baseStart_7920825 baseEnd_7920825 := by
    simpa [prefixWord, tailWord_7920825, baseEnd_7920825] using wordTrace_append hprefix tailTrace_7920825
  have hstable : (prefixWord ++ tailWord_7920825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920825).length < 2 ^ (prefixWord ++ tailWord_7920825).sum := by decide
  have hdescent : baseEnd_7920825 < baseStart_7920825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920841 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 2, 7, 3]
def baseStart_7920841 : Nat := 118140960795 + 7920841 * 2 ^ 59
def prefixEnd_7920841 : Nat := 4983230072969 + 3 ^ 40 * 7920841 * 2
def baseEnd_7920841 : Nat := 4067198620839549406860221

theorem tailTrace_7920841 : CollatzResearch.WordTrace tailWord_7920841 prefixEnd_7920841 4067198620839549406860221 := by
  unfold tailWord_7920841
  simp only [CollatzResearch.WordTrace]
  refine ⟨288896805097153303788234377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192597870064768869192156251 288896805097153303788234377)
  ·
    refine ⟨216672603822864977841175783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288896805097153303788234377 216672603822864977841175783)
    ·
      refine ⟨325008905734297466761763675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216672603822864977841175783 325008905734297466761763675)
      ·
        refine ⟨487513358601446200142645513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325008905734297466761763675 487513358601446200142645513)
        ·
          refine ⟨365635018951084650106984135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487513358601446200142645513 365635018951084650106984135)
          ·
            refine ⟨548452528426626975160476203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365635018951084650106984135 548452528426626975160476203)
            ·
              refine ⟨822678792639940462740714305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548452528426626975160476203 822678792639940462740714305)
              ·
                refine ⟨617009094479955347055535729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822678792639940462740714305 617009094479955347055535729)
                ·
                  refine ⟨462756820859966510291651797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617009094479955347055535729 462756820859966510291651797)
                  ·
                    refine ⟨10845862988905465084960589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 462756820859966510291651797 10845862988905465084960589)
                    ·
                      refine ⟨4067198620839549406860221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10845862988905465084960589 4067198620839549406860221)
                      ·
                        rfl

theorem cell23_7920841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7, 3].length) (baseStart_7920841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920841 prefixEnd_7920841 := by exact prefixLift 7920841
  have htrace : WordTrace (prefixWord ++ tailWord_7920841) baseStart_7920841 baseEnd_7920841 := by
    simpa [prefixWord, tailWord_7920841, baseEnd_7920841] using wordTrace_append hprefix tailTrace_7920841
  have hstable : (prefixWord ++ tailWord_7920841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920841).length < 2 ^ (prefixWord ++ tailWord_7920841).sum := by decide
  have hdescent : baseEnd_7920841 < baseStart_7920841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920842 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4]
def baseStart_7920842 : Nat := 118140960795 + 7920842 * 2 ^ 59
def prefixEnd_7920842 : Nat := 4983230072969 + 3 ^ 40 * 7920842 * 2
def baseEnd_7920842 : Nat := 4067199134320203902947717

theorem tailTrace_7920842 : CollatzResearch.WordTrace tailWord_7920842 prefixEnd_7920842 4067199134320203902947717 := by
  unfold tailWord_7920842
  simp only [CollatzResearch.WordTrace]
  refine ⟨72224210392537420239755195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192597894380099787306013853 72224210392537420239755195)
  ·
    refine ⟨108336315588806130359632793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72224210392537420239755195 108336315588806130359632793)
    ·
      refine ⟨81252236691604597769724595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108336315588806130359632793 81252236691604597769724595)
      ·
        refine ⟨121878355037406896654586893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81252236691604597769724595 121878355037406896654586893)
        ·
          refine ⟨45704383139027586245470085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121878355037406896654586893 45704383139027586245470085)
          ·
            refine ⟨8569571838567672421025641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45704383139027586245470085 8569571838567672421025641)
            ·
              refine ⟨6427178878925754315769231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8569571838567672421025641 6427178878925754315769231)
              ·
                refine ⟨9640768318388631473653847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427178878925754315769231 9640768318388631473653847)
                ·
                  refine ⟨14461152477582947210480771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9640768318388631473653847 14461152477582947210480771)
                  ·
                    refine ⟨21691728716374420815721157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14461152477582947210480771 21691728716374420815721157)
                    ·
                      refine ⟨4067199134320203902947717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21691728716374420815721157 4067199134320203902947717)
                      ·
                        rfl

theorem cell23_7920842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_7920842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920842 prefixEnd_7920842 := by exact prefixLift 7920842
  have htrace : WordTrace (prefixWord ++ tailWord_7920842) baseStart_7920842 baseEnd_7920842 := by
    simpa [prefixWord, tailWord_7920842, baseEnd_7920842] using wordTrace_append hprefix tailTrace_7920842
  have hstable : (prefixWord ++ tailWord_7920842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920842).length < 2 ^ (prefixWord ++ tailWord_7920842).sum := by decide
  have hdescent : baseEnd_7920842 < baseStart_7920842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920852 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_7920852 : Nat := 118140960795 + 7920852 * 2 ^ 59
def prefixEnd_7920852 : Nat := 4983230072969 + 3 ^ 40 * 7920852 * 2
def baseEnd_7920852 : Nat := 1355734756375582954607557

theorem tailTrace_7920852 : CollatzResearch.WordTrace tailWord_7920852 prefixEnd_7920852 1355734756375582954607557 := by
  unfold tailWord_7920852
  simp only [CollatzResearch.WordTrace]
  refine ⟨144448603150056726333442405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192598137533408968444589873 144448603150056726333442405)
  ·
    refine ⟨27084113090635636187520451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144448603150056726333442405 27084113090635636187520451)
    ·
      refine ⟨40626169635953454281280677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27084113090635636187520451 40626169635953454281280677)
      ·
        refine ⟨7617406806741272677740127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40626169635953454281280677 7617406806741272677740127)
        ·
          refine ⟨11426110210111909016610191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617406806741272677740127 11426110210111909016610191)
          ·
            refine ⟨17139165315167863524915287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11426110210111909016610191 17139165315167863524915287)
            ·
              refine ⟨25708747972751795287372931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17139165315167863524915287 25708747972751795287372931)
              ·
                refine ⟨38563121959127692931059397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25708747972751795287372931 38563121959127692931059397)
                ·
                  refine ⟨7230585367336442424573637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38563121959127692931059397 7230585367336442424573637)
                  ·
                    refine ⟨1355734756375582954607557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7230585367336442424573637 1355734756375582954607557)
                    ·
                      rfl

theorem cell23_7920852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_7920852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920852 prefixEnd_7920852 := by exact prefixLift 7920852
  have htrace : WordTrace (prefixWord ++ tailWord_7920852) baseStart_7920852 baseEnd_7920852 := by
    simpa [prefixWord, tailWord_7920852, baseEnd_7920852] using wordTrace_append hprefix tailTrace_7920852
  have hstable : (prefixWord ++ tailWord_7920852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920852).length < 2 ^ (prefixWord ++ tailWord_7920852).sum := by decide
  have hdescent : baseEnd_7920852 < baseStart_7920852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920875 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 1, 3, 3]
def baseStart_7920875 : Nat := 118140960795 + 7920875 * 2 ^ 59
def prefixEnd_7920875 : Nat := 4983230072969 + 3 ^ 40 * 7920875 * 2
def baseEnd_7920875 : Nat := 4067216079181802273835065

theorem tailTrace_7920875 : CollatzResearch.WordTrace tailWord_7920875 prefixEnd_7920875 4067216079181802273835065 := by
  unfold tailWord_7920875
  simp only [CollatzResearch.WordTrace]
  refine ⟨288898045179030127594972079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192598696786020085063314719 288898045179030127594972079)
  ·
    refine ⟨433347067768545191392458119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288898045179030127594972079 433347067768545191392458119)
    ·
      refine ⟨650020601652817787088687179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433347067768545191392458119 650020601652817787088687179)
      ·
        refine ⟨975030902479226680633030769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650020601652817787088687179 975030902479226680633030769)
        ·
          refine ⟨731273176859420010474773077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975030902479226680633030769 731273176859420010474773077)
          ·
            refine ⟨8569607541321328247751247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 731273176859420010474773077 8569607541321328247751247)
            ·
              refine ⟨12854411311981992371626871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569607541321328247751247 12854411311981992371626871)
              ·
                refine ⟨19281616967972988557440307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12854411311981992371626871 19281616967972988557440307)
                ·
                  refine ⟨28922425451959482836160461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19281616967972988557440307 28922425451959482836160461)
                  ·
                    refine ⟨10845909544484806063560173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28922425451959482836160461 10845909544484806063560173)
                    ·
                      refine ⟨4067216079181802273835065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10845909544484806063560173 4067216079181802273835065)
                      ·
                        rfl

theorem cell23_7920875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 3, 3].length) (baseStart_7920875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920875 prefixEnd_7920875 := by exact prefixLift 7920875
  have htrace : WordTrace (prefixWord ++ tailWord_7920875) baseStart_7920875 baseEnd_7920875 := by
    simpa [prefixWord, tailWord_7920875, baseEnd_7920875] using wordTrace_append hprefix tailTrace_7920875
  have hstable : (prefixWord ++ tailWord_7920875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920875).length < 2 ^ (prefixWord ++ tailWord_7920875).sum := by decide
  have hdescent : baseEnd_7920875 < baseStart_7920875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920882 : List Nat := [3, 2, 1, 3, 4, 1, 2, 7]
def baseStart_7920882 : Nat := 118140960795 + 7920882 * 2 ^ 59
def prefixEnd_7920882 : Nat := 4983230072969 + 3 ^ 40 * 7920882 * 2
def baseEnd_7920882 : Nat := 150637765686903101720279

theorem tailTrace_7920882 : CollatzResearch.WordTrace tailWord_7920882 prefixEnd_7920882 150637765686903101720279 := by
  unfold tailWord_7920882
  simp only [CollatzResearch.WordTrace]
  refine ⟨72224575122501191947619225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192598866993336511860317933 72224575122501191947619225)
  ·
    refine ⟨54168431341875893960714419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72224575122501191947619225 54168431341875893960714419)
    ·
      refine ⟨81252647012813840941071629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54168431341875893960714419 81252647012813840941071629)
      ·
        refine ⟨30469742629805190352901861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81252647012813840941071629 30469742629805190352901861)
        ·
          refine ⟨5713076743088473191169099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30469742629805190352901861 5713076743088473191169099)
          ·
            refine ⟨8569615114632709786753649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713076743088473191169099 8569615114632709786753649)
            ·
              refine ⟨6427211335974532340065237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8569615114632709786753649 6427211335974532340065237)
              ·
                refine ⟨150637765686903101720279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6427211335974532340065237 150637765686903101720279)
                ·
                  rfl

theorem cell23_7920882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 7].length) (baseStart_7920882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920882 prefixEnd_7920882 := by exact prefixLift 7920882
  have htrace : WordTrace (prefixWord ++ tailWord_7920882) baseStart_7920882 baseEnd_7920882 := by
    simpa [prefixWord, tailWord_7920882, baseEnd_7920882] using wordTrace_append hprefix tailTrace_7920882
  have hstable : (prefixWord ++ tailWord_7920882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920882).length < 2 ^ (prefixWord ++ tailWord_7920882).sum := by decide
  have hdescent : baseEnd_7920882 < baseStart_7920882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920926 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_7920926 : Nat := 118140960795 + 7920926 * 2 ^ 59
def prefixEnd_7920926 : Nat := 4983230072969 + 3 ^ 40 * 7920926 * 2
def baseEnd_7920926 : Nat := 4067242266695181574297331

theorem tailTrace_7920926 : CollatzResearch.WordTrace tailWord_7920926 prefixEnd_7920926 4067242266695181574297331 := by
  unfold tailWord_7920926
  simp only [CollatzResearch.WordTrace]
  refine ⟨36112488162730670413134829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192599936867896908870052421 36112488162730670413134829)
  ·
    refine ⟨13542183061024001404925561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36112488162730670413134829 13542183061024001404925561)
    ·
      refine ⟨10156637295768001053694171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13542183061024001404925561 10156637295768001053694171)
      ·
        refine ⟨15234955943652001580541257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156637295768001053694171 15234955943652001580541257)
        ·
          refine ⟨11426216957739001185405943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15234955943652001580541257 11426216957739001185405943)
          ·
            refine ⟨17139325436608501778108915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11426216957739001185405943 17139325436608501778108915)
            ·
              refine ⟨25708988154912752667163373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17139325436608501778108915 25708988154912752667163373)
              ·
                refine ⟨9640870558092282250186265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25708988154912752667163373 9640870558092282250186265)
                ·
                  refine ⟨7230652918569211687639699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9640870558092282250186265 7230652918569211687639699)
                  ·
                    refine ⟨10845979377853817531459549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7230652918569211687639699 10845979377853817531459549)
                    ·
                      refine ⟨4067242266695181574297331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10845979377853817531459549 4067242266695181574297331)
                      ·
                        rfl

theorem cell23_7920926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_7920926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920926 prefixEnd_7920926 := by exact prefixLift 7920926
  have htrace : WordTrace (prefixWord ++ tailWord_7920926) baseStart_7920926 baseEnd_7920926 := by
    simpa [prefixWord, tailWord_7920926, baseEnd_7920926] using wordTrace_append hprefix tailTrace_7920926
  have hstable : (prefixWord ++ tailWord_7920926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920926).length < 2 ^ (prefixWord ++ tailWord_7920926).sum := by decide
  have hdescent : baseEnd_7920926 < baseStart_7920926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920972 : List Nat := [2, 2, 1, 3, 2, 2, 4, 2, 5]
def baseStart_7920972 : Nat := 118140960795 + 7920972 * 2 ^ 59
def prefixEnd_7920972 : Nat := 4983230072969 + 3 ^ 40 * 7920972 * 2
def baseEnd_7920972 : Nat := 451918431867254266035791

theorem tailTrace_7920972 : CollatzResearch.WordTrace tailWord_7920972 prefixEnd_7920972 451918431867254266035791 := by
  unfold tailWord_7920972
  simp only [CollatzResearch.WordTrace]
  refine ⟨144450791529839356580626585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192601055373119142107502113 144450791529839356580626585)
  ·
    refine ⟨108338093647379517435469939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144450791529839356580626585 108338093647379517435469939)
    ·
      refine ⟨162507140471069276153204909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108338093647379517435469939 162507140471069276153204909)
      ·
        refine ⟨60940177676650978557451841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162507140471069276153204909 60940177676650978557451841)
        ·
          refine ⟨45705133257488233918088881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60940177676650978557451841 45705133257488233918088881)
          ·
            refine ⟨34278849943116175438566661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45705133257488233918088881 34278849943116175438566661)
            ·
              refine ⟨6427284364334282894731249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34278849943116175438566661 6427284364334282894731249)
              ·
                refine ⟨4820463273250712171048437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6427284364334282894731249 4820463273250712171048437)
                ·
                  refine ⟨451918431867254266035791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4820463273250712171048437 451918431867254266035791)
                  ·
                    rfl

theorem cell23_7920972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_7920972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920972 prefixEnd_7920972 := by exact prefixLift 7920972
  have htrace : WordTrace (prefixWord ++ tailWord_7920972) baseStart_7920972 baseEnd_7920972 := by
    simpa [prefixWord, tailWord_7920972, baseEnd_7920972] using wordTrace_append hprefix tailTrace_7920972
  have hstable : (prefixWord ++ tailWord_7920972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920972).length < 2 ^ (prefixWord ++ tailWord_7920972).sum := by decide
  have hdescent : baseEnd_7920972 < baseStart_7920972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7920989 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 7]
def baseStart_7920989 : Nat := 118140960795 + 7920989 * 2 ^ 59
def prefixEnd_7920989 : Nat := 4983230072969 + 3 ^ 40 * 7920989 * 2
def baseEnd_7920989 : Nat := 451919401775157203089949

theorem tailTrace_7920989 : CollatzResearch.WordTrace tailWord_7920989 prefixEnd_7920989 451919401775157203089949 := by
  unfold tailWord_7920989
  simp only [CollatzResearch.WordTrace]
  refine ⟨288902203100617125064622021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192601468733744750043081347 288902203100617125064622021)
  ·
    refine ⟨54169163081365710949616629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288902203100617125064622021 54169163081365710949616629)
    ·
      refine ⟨5078359038878035401526559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54169163081365710949616629 5078359038878035401526559)
      ·
        refine ⟨7617538558317053102289839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078359038878035401526559 7617538558317053102289839)
        ·
          refine ⟨11426307837475579653434759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617538558317053102289839 11426307837475579653434759)
          ·
            refine ⟨17139461756213369480152139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11426307837475579653434759 17139461756213369480152139)
            ·
              refine ⟨25709192634320054220228209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17139461756213369480152139 25709192634320054220228209)
              ·
                refine ⟨19281894475740040665171157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25709192634320054220228209 19281894475740040665171157)
                ·
                  refine ⟨451919401775157203089949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19281894475740040665171157 451919401775157203089949)
                  ·
                    rfl

theorem cell23_7920989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_7920989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7920989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7920989 prefixEnd_7920989 := by exact prefixLift 7920989
  have htrace : WordTrace (prefixWord ++ tailWord_7920989) baseStart_7920989 baseEnd_7920989 := by
    simpa [prefixWord, tailWord_7920989, baseEnd_7920989] using wordTrace_append hprefix tailTrace_7920989
  have hstable : (prefixWord ++ tailWord_7920989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7920989).length < 2 ^ (prefixWord ++ tailWord_7920989).sum := by decide
  have hdescent : baseEnd_7920989 < baseStart_7920989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7920989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921005 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_7921005 : Nat := 118140960795 + 7921005 * 2 ^ 59
def prefixEnd_7921005 : Nat := 4983230072969 + 3 ^ 40 * 7921005 * 2
def baseEnd_7921005 : Nat := 4067282831666886765209467

theorem tailTrace_7921005 : CollatzResearch.WordTrace tailWord_7921005 prefixEnd_7921005 4067282831666886765209467 := by
  unfold tailWord_7921005
  simp only [CollatzResearch.WordTrace]
  refine ⟨288902786668559159797204469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192601857779039439864802979 288902786668559159797204469)
  ·
    refine ⟨27084636250177421230987919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288902786668559159797204469 27084636250177421230987919)
    ·
      refine ⟨40626954375266131846481879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27084636250177421230987919 40626954375266131846481879)
      ·
        refine ⟨60940431562899197769722819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40626954375266131846481879 60940431562899197769722819)
        ·
          refine ⟨91410647344348796654584229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60940431562899197769722819 91410647344348796654584229)
          ·
            refine ⟨17139496377065399372734543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91410647344348796654584229 17139496377065399372734543)
            ·
              refine ⟨25709244565598099059101815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17139496377065399372734543 25709244565598099059101815)
              ·
                refine ⟨38563866848397148588652723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25709244565598099059101815 38563866848397148588652723)
                ·
                  refine ⟨57845800272595722882979085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38563866848397148588652723 57845800272595722882979085)
                  ·
                    refine ⟨21692175102223396081117157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57845800272595722882979085 21692175102223396081117157)
                    ·
                      refine ⟨4067282831666886765209467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21692175102223396081117157 4067282831666886765209467)
                      ·
                        rfl

theorem cell23_7921005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_7921005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921005 prefixEnd_7921005 := by exact prefixLift 7921005
  have htrace : WordTrace (prefixWord ++ tailWord_7921005) baseStart_7921005 baseEnd_7921005 := by
    simpa [prefixWord, tailWord_7921005, baseEnd_7921005] using wordTrace_append hprefix tailTrace_7921005
  have hstable : (prefixWord ++ tailWord_7921005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921005).length < 2 ^ (prefixWord ++ tailWord_7921005).sum := by decide
  have hdescent : baseEnd_7921005 < baseStart_7921005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921032 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 3, 4]
def baseStart_7921032 : Nat := 118140960795 + 7921032 * 2 ^ 59
def prefixEnd_7921032 : Nat := 4983230072969 + 3 ^ 40 * 7921032 * 2
def baseEnd_7921032 : Nat := 1355765565214852719857281

theorem tailTrace_7921032 : CollatzResearch.WordTrace tailWord_7921032 prefixEnd_7921032 1355765565214852719857281 := by
  unfold tailWord_7921032
  simp only [CollatzResearch.WordTrace]
  refine ⟨144451885719730671704218675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192602514292974228938958233 144451885719730671704218675)
  ·
    refine ⟨216677828579596007556328013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144451885719730671704218675 216677828579596007556328013)
    ·
      refine ⟨81254185717348502833623005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216677828579596007556328013 81254185717348502833623005)
      ·
        refine ⟨30470319644005688562608627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81254185717348502833623005 30470319644005688562608627)
        ·
          refine ⟨45705479466008532843912941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30470319644005688562608627 45705479466008532843912941)
          ·
            refine ⟨17139554799753199816467353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45705479466008532843912941 17139554799753199816467353)
            ·
              refine ⟨12854666099814899862350515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17139554799753199816467353 12854666099814899862350515)
              ·
                refine ⟨19281999149722349793525773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12854666099814899862350515 19281999149722349793525773)
                ·
                  refine ⟨7230749681145881172572165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19281999149722349793525773 7230749681145881172572165)
                  ·
                    refine ⟨1355765565214852719857281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7230749681145881172572165 1355765565214852719857281)
                    ·
                      rfl

theorem cell23_7921032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_7921032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921032 prefixEnd_7921032 := by exact prefixLift 7921032
  have htrace : WordTrace (prefixWord ++ tailWord_7921032) baseStart_7921032 baseEnd_7921032 := by
    simpa [prefixWord, tailWord_7921032, baseEnd_7921032] using wordTrace_append hprefix tailTrace_7921032
  have hstable : (prefixWord ++ tailWord_7921032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921032).length < 2 ^ (prefixWord ++ tailWord_7921032).sum := by decide
  have hdescent : baseEnd_7921032 < baseStart_7921032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921095 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_7921095 : Nat := 118140960795 + 7921095 * 2 ^ 59
def prefixEnd_7921095 : Nat := 4983230072969 + 3 ^ 40 * 7921095 * 2
def baseEnd_7921095 : Nat := 4067329044925791413084053

theorem tailTrace_7921095 : CollatzResearch.WordTrace tailWord_7921095 prefixEnd_7921095 4067329044925791413084053 := by
  unfold tailWord_7921095
  simp only [CollatzResearch.WordTrace]
  refine ⟨288906069238233105167980739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192604046158822070111987159 288906069238233105167980739)
  ·
    refine ⟨433359103857349657751971109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288906069238233105167980739 433359103857349657751971109)
    ·
      refine ⟨81254831973253060828494583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433359103857349657751971109 81254831973253060828494583)
      ·
        refine ⟨121882247959879591242741875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81254831973253060828494583 121882247959879591242741875)
        ·
          refine ⟨182823371939819386864112813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121882247959879591242741875 182823371939819386864112813)
          ·
            refine ⟨68558764477432270074042305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182823371939819386864112813 68558764477432270074042305)
            ·
              refine ⟨51419073358074202555531729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68558764477432270074042305 51419073358074202555531729)
              ·
                refine ⟨38564305018555651916648797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51419073358074202555531729 38564305018555651916648797)
                ·
                  refine ⟨14461614381958369468743299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38564305018555651916648797 14461614381958369468743299)
                  ·
                    refine ⟨21692421572937554203114949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14461614381958369468743299 21692421572937554203114949)
                    ·
                      refine ⟨4067329044925791413084053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21692421572937554203114949 4067329044925791413084053)
                      ·
                        rfl

theorem cell23_7921095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_7921095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921095 prefixEnd_7921095 := by exact prefixLift 7921095
  have htrace : WordTrace (prefixWord ++ tailWord_7921095) baseStart_7921095 baseEnd_7921095 := by
    simpa [prefixWord, tailWord_7921095, baseEnd_7921095] using wordTrace_append hprefix tailTrace_7921095
  have hstable : (prefixWord ++ tailWord_7921095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921095).length < 2 ^ (prefixWord ++ tailWord_7921095).sum := by decide
  have hdescent : baseEnd_7921095 < baseStart_7921095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921112 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 1, 1, 4]
def baseStart_7921112 : Nat := 118140960795 + 7921112 * 2 ^ 59
def prefixEnd_7921112 : Nat := 4983230072969 + 3 ^ 40 * 7921112 * 2
def baseEnd_7921112 : Nat := 4067337774096917846571475

theorem tailTrace_7921112 : CollatzResearch.WordTrace tailWord_7921112 prefixEnd_7921112 4067337774096917846571475 := by
  unfold tailWord_7921112
  simp only [CollatzResearch.WordTrace]
  refine ⟨144453344639585758535674795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192604459519447678047566393 144453344639585758535674795)
  ·
    refine ⟨216680016959378637803512193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144453344639585758535674795 216680016959378637803512193)
    ·
      refine ⟨162510012719533978352634145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216680016959378637803512193 162510012719533978352634145)
      ·
        refine ⟨121882509539650483764475609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162510012719533978352634145 121882509539650483764475609)
        ·
          refine ⟨91411882154737862823356707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121882509539650483764475609 91411882154737862823356707)
          ·
            refine ⟨137117823232106794235035061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91411882154737862823356707 137117823232106794235035061)
            ·
              refine ⟨12854795928010011959534537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137117823232106794235035061 12854795928010011959534537)
              ·
                refine ⟨9641096946007508969650903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12854795928010011959534537 9641096946007508969650903)
                ·
                  refine ⟨14461645419011263454476355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9641096946007508969650903 14461645419011263454476355)
                  ·
                    refine ⟨21692468128516895181714533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14461645419011263454476355 21692468128516895181714533)
                    ·
                      refine ⟨4067337774096917846571475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21692468128516895181714533 4067337774096917846571475)
                      ·
                        rfl

theorem cell23_7921112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_7921112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921112 prefixEnd_7921112 := by exact prefixLift 7921112
  have htrace : WordTrace (prefixWord ++ tailWord_7921112) baseStart_7921112 baseEnd_7921112 := by
    simpa [prefixWord, tailWord_7921112, baseEnd_7921112] using wordTrace_append hprefix tailTrace_7921112
  have hstable : (prefixWord ++ tailWord_7921112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921112).length < 2 ^ (prefixWord ++ tailWord_7921112).sum := by decide
  have hdescent : baseEnd_7921112 < baseStart_7921112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921145 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 5, 3, 3]
def baseStart_7921145 : Nat := 118140960795 + 7921145 * 2 ^ 59
def prefixEnd_7921145 : Nat := 4983230072969 + 3 ^ 40 * 7921145 * 2
def baseEnd_7921145 : Nat := 4067354718958516217458823

theorem tailTrace_7921145 : CollatzResearch.WordTrace tailWord_7921145 prefixEnd_7921145 4067354718958516217458823 := by
  unfold tailWord_7921145
  simp only [CollatzResearch.WordTrace]
  refine ⟨288907892888051963707300889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192605261925367975804867259 288907892888051963707300889)
  ·
    refine ⟨216680919666038972780475667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288907892888051963707300889 216680919666038972780475667)
    ·
      refine ⟨325021379499058459170713501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216680919666038972780475667 325021379499058459170713501)
      ·
        refine ⟨121883017312146922189017563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325021379499058459170713501 121883017312146922189017563)
        ·
          refine ⟨182824525968220383283526345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121883017312146922189017563 182824525968220383283526345)
          ·
            refine ⟨137118394476165287462644759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182824525968220383283526345 137118394476165287462644759)
            ·
              refine ⟨205677591714247931193967139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137118394476165287462644759 205677591714247931193967139)
              ·
                refine ⟨308516387571371896790950709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205677591714247931193967139 308516387571371896790950709)
                ·
                  refine ⟨28923411334816115324151629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 308516387571371896790950709 28923411334816115324151629)
                  ·
                    refine ⟨10846279250556043246556861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28923411334816115324151629 10846279250556043246556861)
                    ·
                      refine ⟨4067354718958516217458823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10846279250556043246556861 4067354718958516217458823)
                      ·
                        rfl

theorem cell23_7921145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_7921145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921145 prefixEnd_7921145 := by exact prefixLift 7921145
  have htrace : WordTrace (prefixWord ++ tailWord_7921145) baseStart_7921145 baseEnd_7921145 := by
    simpa [prefixWord, tailWord_7921145, baseEnd_7921145] using wordTrace_append hprefix tailTrace_7921145
  have hstable : (prefixWord ++ tailWord_7921145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921145).length < 2 ^ (prefixWord ++ tailWord_7921145).sum := by decide
  have hdescent : baseEnd_7921145 < baseStart_7921145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921146 : List Nat := [3, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2]
def baseStart_7921146 : Nat := 118140960795 + 7921146 * 2 ^ 59
def prefixEnd_7921146 : Nat := 4983230072969 + 3 ^ 40 * 7921146 * 2
def baseEnd_7921146 : Nat := 4067355232439170713546319

theorem tailTrace_7921146 : CollatzResearch.WordTrace tailWord_7921146 prefixEnd_7921146 4067355232439170713546319 := by
  unfold tailWord_7921146
  simp only [CollatzResearch.WordTrace]
  refine ⟨72226982340262085219521823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192605286240698893918724861 72226982340262085219521823)
  ·
    refine ⟨108340473510393127829282735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72226982340262085219521823 108340473510393127829282735)
    ·
      refine ⟨162510710265589691743924103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108340473510393127829282735 162510710265589691743924103)
      ·
        refine ⟨243766065398384537615886155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162510710265589691743924103 243766065398384537615886155)
        ·
          refine ⟨365649098097576806423829233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243766065398384537615886155 365649098097576806423829233)
          ·
            refine ⟨274236823573182604817871925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365649098097576806423829233 274236823573182604817871925)
            ·
              refine ⟨25709702209985869201675493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274236823573182604817871925 25709702209985869201675493)
              ·
                refine ⟨4820569164372350475314155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25709702209985869201675493 4820569164372350475314155)
                ·
                  refine ⟨7230853746558525712971233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820569164372350475314155 7230853746558525712971233)
                  ·
                    refine ⟨5423140309918894284728425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7230853746558525712971233 5423140309918894284728425)
                    ·
                      refine ⟨4067355232439170713546319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423140309918894284728425 4067355232439170713546319)
                      ·
                        rfl

theorem cell23_7921146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2].length) (baseStart_7921146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921146 prefixEnd_7921146 := by exact prefixLift 7921146
  have htrace : WordTrace (prefixWord ++ tailWord_7921146) baseStart_7921146 baseEnd_7921146 := by
    simpa [prefixWord, tailWord_7921146, baseEnd_7921146] using wordTrace_append hprefix tailTrace_7921146
  have hstable : (prefixWord ++ tailWord_7921146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921146).length < 2 ^ (prefixWord ++ tailWord_7921146).sum := by decide
  have hdescent : baseEnd_7921146 < baseStart_7921146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921162 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_7921162 : Nat := 118140960795 + 7921162 * 2 ^ 59
def prefixEnd_7921162 : Nat := 4983230072969 + 3 ^ 40 * 7921162 * 2
def baseEnd_7921162 : Nat := 4067363448129642650946245

theorem tailTrace_7921162 : CollatzResearch.WordTrace tailWord_7921162 prefixEnd_7921162 4067363448129642650946245 := by
  unfold tailWord_7921162
  simp only [CollatzResearch.WordTrace]
  refine ⟨72227128232247593902667435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192605675285993583740446493 72227128232247593902667435)
  ·
    refine ⟨108340692348371390854001153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72227128232247593902667435 108340692348371390854001153)
    ·
      refine ⟨81255519261278543140500865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108340692348371390854001153 81255519261278543140500865)
      ·
        refine ⟨60941639445958907355375649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81255519261278543140500865 60941639445958907355375649)
        ·
          refine ⟨45706229584469180516531737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60941639445958907355375649 45706229584469180516531737)
          ·
            refine ⟨34279672188351885387398803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45706229584469180516531737 34279672188351885387398803)
            ·
              refine ⟨51419508282527828081098205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34279672188351885387398803 51419508282527828081098205)
              ·
                refine ⟨19282315605947935530411827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51419508282527828081098205 19282315605947935530411827)
                ·
                  refine ⟨28923473408921903295617741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19282315605947935530411827 28923473408921903295617741)
                  ·
                    refine ⟨10846302528345713735856653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28923473408921903295617741 10846302528345713735856653)
                    ·
                      refine ⟨4067363448129642650946245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10846302528345713735856653 4067363448129642650946245)
                      ·
                        rfl

theorem cell23_7921162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_7921162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921162 prefixEnd_7921162 := by exact prefixLift 7921162
  have htrace : WordTrace (prefixWord ++ tailWord_7921162) baseStart_7921162 baseEnd_7921162 := by
    simpa [prefixWord, tailWord_7921162, baseEnd_7921162] using wordTrace_append hprefix tailTrace_7921162
  have hstable : (prefixWord ++ tailWord_7921162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921162).length < 2 ^ (prefixWord ++ tailWord_7921162).sum := by decide
  have hdescent : baseEnd_7921162 < baseStart_7921162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921213 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 2, 1, 3]
def baseStart_7921213 : Nat := 118140960795 + 7921213 * 2 ^ 59
def prefixEnd_7921213 : Nat := 4983230072969 + 3 ^ 40 * 7921213 * 2
def baseEnd_7921213 : Nat := 4067389635643021951408511

theorem tailTrace_7921213 : CollatzResearch.WordTrace tailWord_7921213 prefixEnd_7921213 4067389635643021951408511 := by
  unfold tailWord_7921213
  simp only [CollatzResearch.WordTrace]
  refine ⟨288910373051805611320776293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192606915367870407547184195 288910373051805611320776293)
  ·
    refine ⟨54170694947213552122645555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288910373051805611320776293 54170694947213552122645555)
    ·
      refine ⟨81256042420820328183968333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54170694947213552122645555 81256042420820328183968333)
      ·
        refine ⟨30471015907807623068988125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81256042420820328183968333 30471015907807623068988125)
        ·
          refine ⟨11426630965427858650870547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30471015907807623068988125 11426630965427858650870547)
          ·
            refine ⟨17139946448141787976305821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11426630965427858650870547 17139946448141787976305821)
            ·
              refine ⟨6427479918053170491114683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17139946448141787976305821 6427479918053170491114683)
              ·
                refine ⟨9641219877079755736672025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427479918053170491114683 9641219877079755736672025)
                ·
                  refine ⟨7230914907809816802504019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9641219877079755736672025 7230914907809816802504019)
                  ·
                    refine ⟨10846372361714725203756029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7230914907809816802504019 10846372361714725203756029)
                    ·
                      refine ⟨4067389635643021951408511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10846372361714725203756029 4067389635643021951408511)
                      ·
                        rfl

theorem cell23_7921213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_7921213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921213 prefixEnd_7921213 := by exact prefixLift 7921213
  have htrace : WordTrace (prefixWord ++ tailWord_7921213) baseStart_7921213 baseEnd_7921213 := by
    simpa [prefixWord, tailWord_7921213, baseEnd_7921213] using wordTrace_append hprefix tailTrace_7921213
  have hstable : (prefixWord ++ tailWord_7921213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921213).length < 2 ^ (prefixWord ++ tailWord_7921213).sum := by decide
  have hdescent : baseEnd_7921213 < baseStart_7921213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921270 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_7921270 : Nat := 118140960795 + 7921270 * 2 ^ 59
def prefixEnd_7921270 : Nat := 4983230072969 + 3 ^ 40 * 7921270 * 2
def baseEnd_7921270 : Nat := 4067418904040328228395749

theorem tailTrace_7921270 : CollatzResearch.WordTrace tailWord_7921270 prefixEnd_7921270 4067418904040328228395749 := by
  unfold tailWord_7921270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18057028250787444378475079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192608301341732740037067509 18057028250787444378475079)
  ·
    refine ⟨27085542376181166567712619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18057028250787444378475079 27085542376181166567712619)
    ·
      refine ⟨40628313564271749851568929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27085542376181166567712619 40628313564271749851568929)
      ·
        refine ⟨30471235173203812388676697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40628313564271749851568929 30471235173203812388676697)
        ·
          refine ⟨22853426379902859291507523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30471235173203812388676697 22853426379902859291507523)
          ·
            refine ⟨34280139569854288937261285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22853426379902859291507523 34280139569854288937261285)
            ·
              refine ⟨6427526169347679175736491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34280139569854288937261285 6427526169347679175736491)
              ·
                refine ⟨9641289254021518763604737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427526169347679175736491 9641289254021518763604737)
                ·
                  refine ⟨7230966940516139072703553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9641289254021518763604737 7230966940516139072703553)
                  ·
                    refine ⟨5423225205387104304527665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7230966940516139072703553 5423225205387104304527665)
                    ·
                      refine ⟨4067418904040328228395749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423225205387104304527665 4067418904040328228395749)
                      ·
                        rfl

theorem cell23_7921270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_7921270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921270 prefixEnd_7921270 := by exact prefixLift 7921270
  have htrace : WordTrace (prefixWord ++ tailWord_7921270) baseStart_7921270 baseEnd_7921270 := by
    simpa [prefixWord, tailWord_7921270, baseEnd_7921270] using wordTrace_append hprefix tailTrace_7921270
  have hstable : (prefixWord ++ tailWord_7921270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921270).length < 2 ^ (prefixWord ++ tailWord_7921270).sum := by decide
  have hdescent : baseEnd_7921270 < baseStart_7921270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921295 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_7921295 : Nat := 118140960795 + 7921295 * 2 ^ 59
def prefixEnd_7921295 : Nat := 4983230072969 + 3 ^ 40 * 7921295 * 2
def baseEnd_7921295 : Nat := 4067431741056690630583133

theorem tailTrace_7921295 : CollatzResearch.WordTrace tailWord_7921295 prefixEnd_7921295 4067431741056690630583133 := by
  unfold tailWord_7921295
  simp only [CollatzResearch.WordTrace]
  refine ⟨288913363837508539325261339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192608909225005692883507559 288913363837508539325261339)
  ·
    refine ⟨433370045756262808987892009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288913363837508539325261339 433370045756262808987892009)
    ·
      refine ⟨325027534317197106740919007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433370045756262808987892009 325027534317197106740919007)
      ·
        refine ⟨487541301475795660111378511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325027534317197106740919007 487541301475795660111378511)
        ·
          refine ⟨731311952213693490167067767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487541301475795660111378511 731311952213693490167067767)
          ·
            refine ⟨1096967928320540235250601651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731311952213693490167067767 1096967928320540235250601651)
            ·
              refine ⟨1645451892480810352875902477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096967928320540235250601651 1645451892480810352875902477)
              ·
                refine ⟨617044459680303882328463429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1645451892480810352875902477 617044459680303882328463429)
                ·
                  refine ⟨115695836190056977936586893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 617044459680303882328463429 115695836190056977936586893)
                  ·
                    refine ⟨43385938571271366726220085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115695836190056977936586893 43385938571271366726220085)
                    ·
                      refine ⟨4067431741056690630583133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43385938571271366726220085 4067431741056690630583133)
                      ·
                        rfl

theorem cell23_7921295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_7921295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921295 prefixEnd_7921295 := by exact prefixLift 7921295
  have htrace : WordTrace (prefixWord ++ tailWord_7921295) baseStart_7921295 baseEnd_7921295 := by
    simpa [prefixWord, tailWord_7921295, baseEnd_7921295] using wordTrace_append hprefix tailTrace_7921295
  have hstable : (prefixWord ++ tailWord_7921295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921295).length < 2 ^ (prefixWord ++ tailWord_7921295).sum := by decide
  have hdescent : baseEnd_7921295 < baseStart_7921295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921309 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_7921309 : Nat := 118140960795 + 7921309 * 2 ^ 59
def prefixEnd_7921309 : Nat := 4983230072969 + 3 ^ 40 * 7921309 * 2
def baseEnd_7921309 : Nat := 4067438929785853575808069

theorem tailTrace_7921309 : CollatzResearch.WordTrace tailWord_7921309 prefixEnd_7921309 4067438929785853575808069 := by
  unfold tailWord_7921309
  simp only [CollatzResearch.WordTrace]
  refine ⟨288913874459457819716270981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192609249639638546477513987 288913874459457819716270981)
  ·
    refine ⟨54171351461148341196800809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288913874459457819716270981 54171351461148341196800809)
    ·
      refine ⟨40628513595861255897600607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54171351461148341196800809 40628513595861255897600607)
      ·
        refine ⟨60942770393791883846400911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40628513595861255897600607 60942770393791883846400911)
        ·
          refine ⟨91414155590687825769601367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60942770393791883846400911 91414155590687825769601367)
          ·
            refine ⟨137121233386031738654402051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91414155590687825769601367 137121233386031738654402051)
            ·
              refine ⟨205681850079047607981603077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137121233386031738654402051 205681850079047607981603077)
              ·
                refine ⟨38565346889821426496550577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205681850079047607981603077 38565346889821426496550577)
                ·
                  refine ⟨28924010167366069872412933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38565346889821426496550577 28924010167366069872412933)
                  ·
                    refine ⟨5423251906381138101077425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28924010167366069872412933 5423251906381138101077425)
                    ·
                      refine ⟨4067438929785853575808069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423251906381138101077425 4067438929785853575808069)
                      ·
                        rfl

theorem cell23_7921309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_7921309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921309 prefixEnd_7921309 := by exact prefixLift 7921309
  have htrace : WordTrace (prefixWord ++ tailWord_7921309) baseStart_7921309 baseEnd_7921309 := by
    simpa [prefixWord, tailWord_7921309, baseEnd_7921309] using wordTrace_append hprefix tailTrace_7921309
  have hstable : (prefixWord ++ tailWord_7921309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921309).length < 2 ^ (prefixWord ++ tailWord_7921309).sum := by decide
  have hdescent : baseEnd_7921309 < baseStart_7921309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921383 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 6]
def baseStart_7921383 : Nat := 118140960795 + 7921383 * 2 ^ 59
def prefixEnd_7921383 : Nat := 4983230072969 + 3 ^ 40 * 7921383 * 2
def baseEnd_7921383 : Nat := 451941880817142920698081

theorem tailTrace_7921383 : CollatzResearch.WordTrace tailWord_7921383 prefixEnd_7921383 451941880817142920698081 := by
  unfold tailWord_7921383
  simp only [CollatzResearch.WordTrace]
  refine ⟨288916573461189730354464803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192611048974126486902976535 288916573461189730354464803)
  ·
    refine ⟨433374860191784595531697205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288916573461189730354464803 433374860191784595531697205)
    ·
      refine ⟨40628893142979805831096613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 433374860191784595531697205 40628893142979805831096613)
      ·
        refine ⟨7617917464308713593330615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40628893142979805831096613 7617917464308713593330615)
        ·
          refine ⟨11426876196463070389995923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617917464308713593330615 11426876196463070389995923)
          ·
            refine ⟨17140314294694605584993885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11426876196463070389995923 17140314294694605584993885)
            ·
              refine ⟨6427617860510477094372707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17140314294694605584993885 6427617860510477094372707)
              ·
                refine ⟨9641426790765715641559061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427617860510477094372707 9641426790765715641559061)
                ·
                  refine ⟨451941880817142920698081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9641426790765715641559061 451941880817142920698081)
                  ·
                    rfl

theorem cell23_7921383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 6].length) (baseStart_7921383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921383 prefixEnd_7921383 := by exact prefixLift 7921383
  have htrace : WordTrace (prefixWord ++ tailWord_7921383) baseStart_7921383 baseEnd_7921383 := by
    simpa [prefixWord, tailWord_7921383, baseEnd_7921383] using wordTrace_append hprefix tailTrace_7921383
  have hstable : (prefixWord ++ tailWord_7921383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921383).length < 2 ^ (prefixWord ++ tailWord_7921383).sum := by decide
  have hdescent : baseEnd_7921383 < baseStart_7921383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921392 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 1, 6]
def baseStart_7921392 : Nat := 118140960795 + 7921392 * 2 ^ 59
def prefixEnd_7921392 : Nat := 4983230072969 + 3 ^ 40 * 7921392 * 2
def baseEnd_7921392 : Nat := 1355827182893392250356729

theorem tailTrace_7921392 : CollatzResearch.WordTrace tailWord_7921392 prefixEnd_7921392 1355827182893392250356729 := by
  unfold tailWord_7921392
  simp only [CollatzResearch.WordTrace]
  refine ⟨144458450859078562445771215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192611267812104749927694953 144458450859078562445771215)
  ·
    refine ⟨216687676288617843668656823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144458450859078562445771215 216687676288617843668656823)
    ·
      refine ⟨325031514432926765502985235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216687676288617843668656823 325031514432926765502985235)
      ·
        refine ⟨487547271649390148254477853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325031514432926765502985235 487547271649390148254477853)
        ·
          refine ⟨182830226868521305595429195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487547271649390148254477853 182830226868521305595429195)
          ·
            refine ⟨274245340302781958393143793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182830226868521305595429195 274245340302781958393143793)
            ·
              refine ⟨205684005227086468794857845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274245340302781958393143793 205684005227086468794857845)
              ·
                refine ⟨19282875490039356449517923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205684005227086468794857845 19282875490039356449517923)
                ·
                  refine ⟨28924313235059034674276885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19282875490039356449517923 28924313235059034674276885)
                  ·
                    refine ⟨1355827182893392250356729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28924313235059034674276885 1355827182893392250356729)
                    ·
                      rfl

theorem cell23_7921392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_7921392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921392 prefixEnd_7921392 := by exact prefixLift 7921392
  have htrace : WordTrace (prefixWord ++ tailWord_7921392) baseStart_7921392 baseEnd_7921392 := by
    simpa [prefixWord, tailWord_7921392, baseEnd_7921392] using wordTrace_append hprefix tailTrace_7921392
  have hstable : (prefixWord ++ tailWord_7921392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921392).length < 2 ^ (prefixWord ++ tailWord_7921392).sum := by decide
  have hdescent : baseEnd_7921392 < baseStart_7921392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921399 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 4]
def baseStart_7921399 : Nat := 118140960795 + 7921399 * 2 ^ 59
def prefixEnd_7921399 : Nat := 4983230072969 + 3 ^ 40 * 7921399 * 2
def baseEnd_7921399 : Nat := 4067485143044758223682655

theorem tailTrace_7921399 : CollatzResearch.WordTrace tailWord_7921399 prefixEnd_7921399 4067485143044758223682655 := by
  unfold tailWord_7921399
  simp only [CollatzResearch.WordTrace]
  refine ⟨288917157029131765087047251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192611438019421176724698167 288917157029131765087047251)
  ·
    refine ⟨433375735543697647630570877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288917157029131765087047251 433375735543697647630570877)
    ·
      refine ⟨162515900828886617861464079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433375735543697647630570877 162515900828886617861464079)
      ·
        refine ⟨243773851243329926792196119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162515900828886617861464079 243773851243329926792196119)
        ·
          refine ⟨365660776864994890188294179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243773851243329926792196119 365660776864994890188294179)
          ·
            refine ⟨548491165297492335282441269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365660776864994890188294179 548491165297492335282441269)
            ·
              refine ⟨51421046746639906432728869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 548491165297492335282441269 51421046746639906432728869)
              ·
                refine ⟨9641446264994982456136663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51421046746639906432728869 9641446264994982456136663)
                ·
                  refine ⟨14462169397492473684204995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9641446264994982456136663 14462169397492473684204995)
                  ·
                    refine ⟨21693254096238710526307493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14462169397492473684204995 21693254096238710526307493)
                    ·
                      refine ⟨4067485143044758223682655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21693254096238710526307493 4067485143044758223682655)
                      ·
                        rfl

theorem cell23_7921399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_7921399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921399 prefixEnd_7921399 := by exact prefixLift 7921399
  have htrace : WordTrace (prefixWord ++ tailWord_7921399) baseStart_7921399 baseEnd_7921399 := by
    simpa [prefixWord, tailWord_7921399, baseEnd_7921399] using wordTrace_append hprefix tailTrace_7921399
  have hstable : (prefixWord ++ tailWord_7921399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921399).length < 2 ^ (prefixWord ++ tailWord_7921399).sum := by decide
  have hdescent : baseEnd_7921399 < baseStart_7921399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921402 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_7921402 : Nat := 118140960795 + 7921402 * 2 ^ 59
def prefixEnd_7921402 : Nat := 4983230072969 + 3 ^ 40 * 7921402 * 2
def baseEnd_7921402 : Nat := 4067486683486721711945141

theorem tailTrace_7921402 : CollatzResearch.WordTrace tailWord_7921402 prefixEnd_7921402 4067486683486721711945141 := by
  unfold tailWord_7921402
  simp only [CollatzResearch.WordTrace]
  refine ⟨72229316612030224149851615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192611510965413931066270973 72229316612030224149851615)
  ·
    refine ⟨108343974918045336224777423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72229316612030224149851615 108343974918045336224777423)
    ·
      refine ⟨162515962377068004337166135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108343974918045336224777423 162515962377068004337166135)
      ·
        refine ⟨243773943565602006505749203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162515962377068004337166135 243773943565602006505749203)
        ·
          refine ⟨365660915348403009758623805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243773943565602006505749203 365660915348403009758623805)
          ·
            refine ⟨137122843255651128659483927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365660915348403009758623805 137122843255651128659483927)
            ·
              refine ⟨205684264883476692989225891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137122843255651128659483927 205684264883476692989225891)
              ·
                refine ⟨308526397325215039483838837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205684264883476692989225891 308526397325215039483838837)
                ·
                  refine ⟨28924349749238909951609891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 308526397325215039483838837 28924349749238909951609891)
                  ·
                    refine ⟨43386524623858364927414837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28924349749238909951609891 43386524623858364927414837)
                    ·
                      refine ⟨4067486683486721711945141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43386524623858364927414837 4067486683486721711945141)
                      ·
                        rfl

theorem cell23_7921402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_7921402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921402 prefixEnd_7921402 := by exact prefixLift 7921402
  have htrace : WordTrace (prefixWord ++ tailWord_7921402) baseStart_7921402 baseEnd_7921402 := by
    simpa [prefixWord, tailWord_7921402, baseEnd_7921402] using wordTrace_append hprefix tailTrace_7921402
  have hstable : (prefixWord ++ tailWord_7921402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921402).length < 2 ^ (prefixWord ++ tailWord_7921402).sum := by decide
  have hdescent : baseEnd_7921402 < baseStart_7921402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921409 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 4, 4]
def baseStart_7921409 : Nat := 118140960795 + 7921409 * 2 ^ 59
def prefixEnd_7921409 : Nat := 4983230072969 + 3 ^ 40 * 7921409 * 2
def baseEnd_7921409 : Nat := 1355830092617101061519203

theorem tailTrace_7921409 : CollatzResearch.WordTrace tailWord_7921409 prefixEnd_7921409 1355830092617101061519203 := by
  unfold tailWord_7921409
  simp only [CollatzResearch.WordTrace]
  refine ⟨288917521759095536794911281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192611681172730357863274187 288917521759095536794911281)
  ·
    refine ⟨216688141319321652596183461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288917521759095536794911281 216688141319321652596183461)
    ·
      refine ⟨40629026497372809861784399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216688141319321652596183461 40629026497372809861784399)
      ·
        refine ⟨60943539746059214792676599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40629026497372809861784399 60943539746059214792676599)
        ·
          refine ⟨91415309619088822189014899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60943539746059214792676599 91415309619088822189014899)
          ·
            refine ⟨137122964428633233283522349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91415309619088822189014899 137122964428633233283522349)
            ·
              refine ⟨51421111660737462481320881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137122964428633233283522349 51421111660737462481320881)
              ·
                refine ⟨38565833745553096860990661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51421111660737462481320881 38565833745553096860990661)
                ·
                  refine ⟨7231093827291205661435749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38565833745553096860990661 7231093827291205661435749)
                  ·
                    refine ⟨1355830092617101061519203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7231093827291205661435749 1355830092617101061519203)
                    ·
                      rfl

theorem cell23_7921409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_7921409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921409 prefixEnd_7921409 := by exact prefixLift 7921409
  have htrace : WordTrace (prefixWord ++ tailWord_7921409) baseStart_7921409 baseEnd_7921409 := by
    simpa [prefixWord, tailWord_7921409, baseEnd_7921409] using wordTrace_append hprefix tailTrace_7921409
  have hstable : (prefixWord ++ tailWord_7921409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921409).length < 2 ^ (prefixWord ++ tailWord_7921409).sum := by decide
  have hdescent : baseEnd_7921409 < baseStart_7921409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921414 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7921414 : Nat := 118140960795 + 7921414 * 2 ^ 59
def prefixEnd_7921414 : Nat := 4983230072969 + 3 ^ 40 * 7921414 * 2
def baseEnd_7921414 : Nat := 4067492845254575664995087

theorem tailTrace_7921414 : CollatzResearch.WordTrace tailWord_7921414 prefixEnd_7921414 4067492845254575664995087 := by
  unfold tailWord_7921414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9028678253877419457776353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192611802749384948432562197 9028678253877419457776353)
  ·
    refine ⟨6771508690408064593332265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9028678253877419457776353 6771508690408064593332265)
    ·
      refine ⟨5078631517806048444999199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6771508690408064593332265 5078631517806048444999199)
      ·
        refine ⟨7617947276709072667498799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078631517806048444999199 7617947276709072667498799)
        ·
          refine ⟨11426920915063609001248199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617947276709072667498799 11426920915063609001248199)
          ·
            refine ⟨17140381372595413501872299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11426920915063609001248199 17140381372595413501872299)
            ·
              refine ⟨25710572058893120252808449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17140381372595413501872299 25710572058893120252808449)
              ·
                refine ⟨19282929044169840189606337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25710572058893120252808449 19282929044169840189606337)
                ·
                  refine ⟨14462196783127380142204753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19282929044169840189606337 14462196783127380142204753)
                  ·
                    refine ⟨10846647587345535106653565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14462196783127380142204753 10846647587345535106653565)
                    ·
                      refine ⟨4067492845254575664995087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10846647587345535106653565 4067492845254575664995087)
                      ·
                        rfl

theorem cell23_7921414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7921414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921414 prefixEnd_7921414 := by exact prefixLift 7921414
  have htrace : WordTrace (prefixWord ++ tailWord_7921414) baseStart_7921414 baseEnd_7921414 := by
    simpa [prefixWord, tailWord_7921414, baseEnd_7921414] using wordTrace_append hprefix tailTrace_7921414
  have hstable : (prefixWord ++ tailWord_7921414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921414).length < 2 ^ (prefixWord ++ tailWord_7921414).sum := by decide
  have hdescent : baseEnd_7921414 < baseStart_7921414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921421 : List Nat := [1, 7, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_7921421 : Nat := 118140960795 + 7921421 * 2 ^ 59
def prefixEnd_7921421 : Nat := 4983230072969 + 3 ^ 40 * 7921421 * 2
def baseEnd_7921421 : Nat := 1355832146539719045869185

theorem tailTrace_7921421 : CollatzResearch.WordTrace tailWord_7921421 prefixEnd_7921421 1355832146539719045869185 := by
  unfold tailWord_7921421
  simp only [CollatzResearch.WordTrace]
  refine ⟨288917959435052062844348117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192611972956701375229565411 288917959435052062844348117)
  ·
    refine ⟨6771514674259032722914409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 288917959435052062844348117 6771514674259032722914409)
    ·
      refine ⟨5078636005694274542185807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6771514674259032722914409 5078636005694274542185807)
      ·
        refine ⟨7617954008541411813278711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078636005694274542185807 7617954008541411813278711)
        ·
          refine ⟨11426931012812117719918067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617954008541411813278711 11426931012812117719918067)
          ·
            refine ⟨17140396519218176579877101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11426931012812117719918067 17140396519218176579877101)
            ·
              refine ⟨6427648694706816217453913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17140396519218176579877101 6427648694706816217453913)
              ·
                refine ⟨4820736521030112163090435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6427648694706816217453913 4820736521030112163090435)
                ·
                  refine ⟨7231104781545168244635653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820736521030112163090435 7231104781545168244635653)
                  ·
                    refine ⟨1355832146539719045869185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7231104781545168244635653 1355832146539719045869185)
                    ·
                      rfl

theorem cell23_7921421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_7921421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921421 prefixEnd_7921421 := by exact prefixLift 7921421
  have htrace : WordTrace (prefixWord ++ tailWord_7921421) baseStart_7921421 baseEnd_7921421 := by
    simpa [prefixWord, tailWord_7921421, baseEnd_7921421] using wordTrace_append hprefix tailTrace_7921421
  have hstable : (prefixWord ++ tailWord_7921421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921421).length < 2 ^ (prefixWord ++ tailWord_7921421).sum := by decide
  have hdescent : baseEnd_7921421 < baseStart_7921421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921422 : List Nat := [4, 1, 1, 2, 1, 1, 13]
def baseStart_7921422 : Nat := 118140960795 + 7921422 * 2 ^ 59
def prefixEnd_7921422 : Nat := 4983230072969 + 3 ^ 40 * 7921422 * 2
def baseEnd_7921422 : Nat := 50216011766664341156729

theorem tailTrace_7921422 : CollatzResearch.WordTrace tailWord_7921422 prefixEnd_7921422 50216011766664341156729 := by
  unfold tailWord_7921422
  simp only [CollatzResearch.WordTrace]
  refine ⟨36114749488506055001891815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192611997272032293343423013 36114749488506055001891815)
  ·
    refine ⟨54172124232759082502837723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36114749488506055001891815 54172124232759082502837723)
    ·
      refine ⟨81258186349138623754256585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54172124232759082502837723 81258186349138623754256585)
      ·
        refine ⟨60943639761853967815692439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81258186349138623754256585 60943639761853967815692439)
        ·
          refine ⟨91415459642780951723538659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60943639761853967815692439 91415459642780951723538659)
          ·
            refine ⟨137123189464171427585307989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91415459642780951723538659 137123189464171427585307989)
            ·
              refine ⟨50216011766664341156729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 137123189464171427585307989 50216011766664341156729)
              ·
                rfl

theorem cell23_7921422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 13].length) (baseStart_7921422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921422 prefixEnd_7921422 := by exact prefixLift 7921422
  have htrace : WordTrace (prefixWord ++ tailWord_7921422) baseStart_7921422 baseEnd_7921422 := by
    simpa [prefixWord, tailWord_7921422, baseEnd_7921422] using wordTrace_append hprefix tailTrace_7921422
  have hstable : (prefixWord ++ tailWord_7921422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921422).length < 2 ^ (prefixWord ++ tailWord_7921422).sum := by decide
  have hdescent : baseEnd_7921422 < baseStart_7921422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921466 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3]
def baseStart_7921466 : Nat := 118140960795 + 7921466 * 2 ^ 59
def prefixEnd_7921466 : Nat := 4983230072969 + 3 ^ 40 * 7921466 * 2
def baseEnd_7921466 : Nat := 4067519546248609461544847

theorem tailTrace_7921466 : CollatzResearch.WordTrace tailWord_7921466 prefixEnd_7921466 4067519546248609461544847 := by
  unfold tailWord_7921466
  simp only [CollatzResearch.WordTrace]
  refine ⟨72229900179972258882434063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192613067146592690353157501 72229900179972258882434063)
  ·
    refine ⟨108344850269958388323651095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72229900179972258882434063 108344850269958388323651095)
    ·
      refine ⟨162517275404937582485476643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108344850269958388323651095 162517275404937582485476643)
      ·
        refine ⟨243775913107406373728214965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162517275404937582485476643 243775913107406373728214965)
        ·
          refine ⟨22853991853819347537020153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243775913107406373728214965 22853991853819347537020153)
          ·
            refine ⟨17140493890364510652765115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22853991853819347537020153 17140493890364510652765115)
            ·
              refine ⟨25710740835546765979147673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17140493890364510652765115 25710740835546765979147673)
              ·
                refine ⟨19283055626660074484360755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25710740835546765979147673 19283055626660074484360755)
                ·
                  refine ⟨28924583439990111726541133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19283055626660074484360755 28924583439990111726541133)
                  ·
                    refine ⟨10846718789996291897452925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28924583439990111726541133 10846718789996291897452925)
                    ·
                      refine ⟨4067519546248609461544847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10846718789996291897452925 4067519546248609461544847)
                      ·
                        rfl

theorem cell23_7921466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_7921466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921466 prefixEnd_7921466 := by exact prefixLift 7921466
  have htrace : WordTrace (prefixWord ++ tailWord_7921466) baseStart_7921466 baseEnd_7921466 := by
    simpa [prefixWord, tailWord_7921466, baseEnd_7921466] using wordTrace_append hprefix tailTrace_7921466
  have hstable : (prefixWord ++ tailWord_7921466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921466).length < 2 ^ (prefixWord ++ tailWord_7921466).sum := by decide
  have hdescent : baseEnd_7921466 < baseStart_7921466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921470 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_7921470 : Nat := 118140960795 + 7921470 * 2 ^ 59
def prefixEnd_7921470 : Nat := 4983230072969 + 3 ^ 40 * 7921470 * 2
def baseEnd_7921470 : Nat := 4067521600171227445894829

theorem tailTrace_7921470 : CollatzResearch.WordTrace tailWord_7921470 prefixEnd_7921470 4067521600171227445894829 := by
  unfold tailWord_7921470
  simp only [CollatzResearch.WordTrace]
  refine ⟨36114968326484318026610233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192613164407916362808587909 36114968326484318026610233)
  ·
    refine ⟨27086226244863238519957675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36114968326484318026610233 27086226244863238519957675)
    ·
      refine ⟨40629339367294857779936513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27086226244863238519957675 40629339367294857779936513)
      ·
        refine ⟨30472004525471143334952385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40629339367294857779936513 30472004525471143334952385)
        ·
          refine ⟨22854003394103357501214289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30472004525471143334952385 22854003394103357501214289)
          ·
            refine ⟨17140502545577518125910717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22854003394103357501214289 17140502545577518125910717)
            ·
              refine ⟨6427688454591569297216519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17140502545577518125910717 6427688454591569297216519)
              ·
                refine ⟨9641532681887353945824779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427688454591569297216519 9641532681887353945824779)
                ·
                  refine ⟨14462299022831030918737169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9641532681887353945824779 14462299022831030918737169)
                  ·
                    refine ⟨10846724267123273189052877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14462299022831030918737169 10846724267123273189052877)
                    ·
                      refine ⟨4067521600171227445894829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10846724267123273189052877 4067521600171227445894829)
                      ·
                        rfl

theorem cell23_7921470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_7921470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921470 prefixEnd_7921470 := by exact prefixLift 7921470
  have htrace : WordTrace (prefixWord ++ tailWord_7921470) baseStart_7921470 baseEnd_7921470 := by
    simpa [prefixWord, tailWord_7921470, baseEnd_7921470] using wordTrace_append hprefix tailTrace_7921470
  have hstable : (prefixWord ++ tailWord_7921470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921470).length < 2 ^ (prefixWord ++ tailWord_7921470).sum := by decide
  have hdescent : baseEnd_7921470 < baseStart_7921470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921484 : List Nat := [2, 2, 1, 3, 4, 2, 2, 2, 1, 2, 2]
def baseStart_7921484 : Nat := 118140960795 + 7921484 * 2 ^ 59
def prefixEnd_7921484 : Nat := 4983230072969 + 3 ^ 40 * 7921484 * 2
def baseEnd_7921484 : Nat := 4067528788900390391119765

theorem tailTrace_7921484 : CollatzResearch.WordTrace tailWord_7921484 prefixEnd_7921484 4067528788900390391119765 := by
  unfold tailWord_7921484
  simp only [CollatzResearch.WordTrace]
  refine ⟨144460128616911912301945753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192613504822549216402594337 144460128616911912301945753)
  ·
    refine ⟨108345096462683934226459315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144460128616911912301945753 108345096462683934226459315)
    ·
      refine ⟨162517644694025901339688973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108345096462683934226459315 162517644694025901339688973)
      ·
        refine ⟨60944116760259713002383365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162517644694025901339688973 60944116760259713002383365)
        ·
          refine ⟨11427021892548696187946881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60944116760259713002383365 11427021892548696187946881)
          ·
            refine ⟨8570266419411522140960161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11427021892548696187946881 8570266419411522140960161)
            ·
              refine ⟨6427699814558641605720121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8570266419411522140960161 6427699814558641605720121)
              ·
                refine ⟨4820774860918981204290091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6427699814558641605720121 4820774860918981204290091)
                ·
                  refine ⟨7231162291378471806435137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820774860918981204290091 7231162291378471806435137)
                  ·
                    refine ⟨5423371718533853854826353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7231162291378471806435137 5423371718533853854826353)
                    ·
                      refine ⟨4067528788900390391119765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423371718533853854826353 4067528788900390391119765)
                      ·
                        rfl

theorem cell23_7921484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_7921484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921484 prefixEnd_7921484 := by exact prefixLift 7921484
  have htrace : WordTrace (prefixWord ++ tailWord_7921484) baseStart_7921484 baseEnd_7921484 := by
    simpa [prefixWord, tailWord_7921484, baseEnd_7921484] using wordTrace_append hprefix tailTrace_7921484
  have hstable : (prefixWord ++ tailWord_7921484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921484).length < 2 ^ (prefixWord ++ tailWord_7921484).sum := by decide
  have hdescent : baseEnd_7921484 < baseStart_7921484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921489 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_7921489 : Nat := 118140960795 + 7921489 * 2 ^ 59
def prefixEnd_7921489 : Nat := 4983230072969 + 3 ^ 40 * 7921489 * 2
def baseEnd_7921489 : Nat := 4067531356303662871557241

theorem tailTrace_7921489 : CollatzResearch.WordTrace tailWord_7921489 prefixEnd_7921489 4067531356303662871557241 := by
  unfold tailWord_7921489
  simp only [CollatzResearch.WordTrace]
  refine ⟨288920439598805710457823521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192613626399203806971882347 288920439598805710457823521)
  ·
    refine ⟨216690329699104282843367641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288920439598805710457823521 216690329699104282843367641)
    ·
      refine ⟨162517747274328212132525731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216690329699104282843367641 162517747274328212132525731)
      ·
        refine ⟨243776620911492318198788597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162517747274328212132525731 243776620911492318198788597)
        ·
          refine ⟨22854058210452404831136431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243776620911492318198788597 22854058210452404831136431)
          ·
            refine ⟨34281087315678607246704647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22854058210452404831136431 34281087315678607246704647)
            ·
              refine ⟨51421630973517910870056971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34281087315678607246704647 51421630973517910870056971)
              ·
                refine ⟨77132446460276866305085457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51421630973517910870056971 77132446460276866305085457)
                ·
                  refine ⟨57849334845207649728814093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77132446460276866305085457 57849334845207649728814093)
                  ·
                    refine ⟨21693500566952868648305285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57849334845207649728814093 21693500566952868648305285)
                    ·
                      refine ⟨4067531356303662871557241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21693500566952868648305285 4067531356303662871557241)
                      ·
                        rfl

theorem cell23_7921489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_7921489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921489 prefixEnd_7921489 := by exact prefixLift 7921489
  have htrace : WordTrace (prefixWord ++ tailWord_7921489) baseStart_7921489 baseEnd_7921489 := by
    simpa [prefixWord, tailWord_7921489, baseEnd_7921489] using wordTrace_append hprefix tailTrace_7921489
  have hstable : (prefixWord ++ tailWord_7921489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921489).length < 2 ^ (prefixWord ++ tailWord_7921489).sum := by decide
  have hdescent : baseEnd_7921489 < baseStart_7921489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921509 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 4, 4, 3]
def baseStart_7921509 : Nat := 118140960795 + 7921509 * 2 ^ 59
def prefixEnd_7921509 : Nat := 4983230072969 + 3 ^ 40 * 7921509 * 2
def baseEnd_7921509 : Nat := 4067541625916752793307149

theorem tailTrace_7921509 : CollatzResearch.WordTrace tailWord_7921509 prefixEnd_7921509 4067541625916752793307149 := by
  unfold tailWord_7921509
  simp only [CollatzResearch.WordTrace]
  refine ⟨288921169058733253873551581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192614112705822169249034387 288921169058733253873551581)
  ·
    refine ⟨108345438397024970202581843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288921169058733253873551581 108345438397024970202581843)
    ·
      refine ⟨162518157595537455303872765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108345438397024970202581843 162518157595537455303872765)
      ·
        refine ⟨60944309098326545738952287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162518157595537455303872765 60944309098326545738952287)
        ·
          refine ⟨91416463647489818608428431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60944309098326545738952287 91416463647489818608428431)
          ·
            refine ⟨137124695471234727912642647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91416463647489818608428431 137124695471234727912642647)
            ·
              refine ⟨205687043206852091868963971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137124695471234727912642647 205687043206852091868963971)
              ·
                refine ⟨308530564810278137803445957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205687043206852091868963971 308530564810278137803445957)
                ·
                  refine ⟨57849480901927150838146117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308530564810278137803445957 57849480901927150838146117)
                  ·
                    refine ⟨10846777669111340782152397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57849480901927150838146117 10846777669111340782152397)
                    ·
                      refine ⟨4067541625916752793307149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10846777669111340782152397 4067541625916752793307149)
                      ·
                        rfl

theorem cell23_7921509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_7921509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921509 prefixEnd_7921509 := by exact prefixLift 7921509
  have htrace : WordTrace (prefixWord ++ tailWord_7921509) baseStart_7921509 baseEnd_7921509 := by
    simpa [prefixWord, tailWord_7921509, baseEnd_7921509] using wordTrace_append hprefix tailTrace_7921509
  have hstable : (prefixWord ++ tailWord_7921509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921509).length < 2 ^ (prefixWord ++ tailWord_7921509).sum := by decide
  have hdescent : baseEnd_7921509 < baseStart_7921509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921540 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_7921540 : Nat := 118140960795 + 7921540 * 2 ^ 59
def prefixEnd_7921540 : Nat := 4983230072969 + 3 ^ 40 * 7921540 * 2
def baseEnd_7921540 : Nat := 4067557543817042172019507

theorem tailTrace_7921540 : CollatzResearch.WordTrace tailWord_7921540 prefixEnd_7921540 4067557543817042172019507 := by
  unfold tailWord_7921540
  simp only [CollatzResearch.WordTrace]
  refine ⟨144461149860810473083965037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192614866481080630778620049 144461149860810473083965037)
  ·
    refine ⟨54172931197803927406486889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144461149860810473083965037 54172931197803927406486889)
    ·
      refine ⟨40629698398352945554865167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54172931197803927406486889 40629698398352945554865167)
      ·
        refine ⟨60944547597529418332297751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40629698398352945554865167 60944547597529418332297751)
        ·
          refine ⟨91416821396294127498446627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60944547597529418332297751 91416821396294127498446627)
          ·
            refine ⟨137125232094441191247669941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91416821396294127498446627 137125232094441191247669941)
            ·
              refine ⟨12855490508853861679469057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137125232094441191247669941 12855490508853861679469057)
              ·
                refine ⟨9641617881640396259601793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12855490508853861679469057 9641617881640396259601793)
                ·
                  refine ⟨7231213411230297194701345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9641617881640396259601793 7231213411230297194701345)
                  ·
                    refine ⟨5423410058422722896026009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7231213411230297194701345 5423410058422722896026009)
                    ·
                      refine ⟨4067557543817042172019507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423410058422722896026009 4067557543817042172019507)
                      ·
                        rfl

theorem cell23_7921540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_7921540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921540 prefixEnd_7921540 := by exact prefixLift 7921540
  have htrace : WordTrace (prefixWord ++ tailWord_7921540) baseStart_7921540 baseEnd_7921540 := by
    simpa [prefixWord, tailWord_7921540, baseEnd_7921540] using wordTrace_append hprefix tailTrace_7921540
  have hstable : (prefixWord ++ tailWord_7921540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921540).length < 2 ^ (prefixWord ++ tailWord_7921540).sum := by decide
  have hdescent : baseEnd_7921540 < baseStart_7921540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921559 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 1, 7]
def baseStart_7921559 : Nat := 118140960795 + 7921559 * 2 ^ 59
def prefixEnd_7921559 : Nat := 4983230072969 + 3 ^ 40 * 7921559 * 2
def baseEnd_7921559 : Nat := 1355855766649825865893973

theorem tailTrace_7921559 : CollatzResearch.WordTrace tailWord_7921559 prefixEnd_7921559 1355855766649825865893973 := by
  unfold tailWord_7921559
  simp only [CollatzResearch.WordTrace]
  refine ⟨288922992708552112412871731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192615328472368074941914487 288922992708552112412871731)
  ·
    refine ⟨433384489062828168619307597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288922992708552112412871731 433384489062828168619307597)
    ·
      refine ⟨162519183398560563232240349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433384489062828168619307597 162519183398560563232240349)
      ·
        refine ⟨60944693774460211212090131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162519183398560563232240349 60944693774460211212090131)
        ·
          refine ⟨91417040661690316818135197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60944693774460211212090131 91417040661690316818135197)
          ·
            refine ⟨34281390248133868806800699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91417040661690316818135197 34281390248133868806800699)
            ·
              refine ⟨51422085372200803210201049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34281390248133868806800699 51422085372200803210201049)
              ·
                refine ⟨38566564029150602407650787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51422085372200803210201049 38566564029150602407650787)
                ·
                  refine ⟨57849846043725903611476181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38566564029150602407650787 57849846043725903611476181)
                  ·
                    refine ⟨1355855766649825865893973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57849846043725903611476181 1355855766649825865893973)
                    ·
                      rfl

theorem cell23_7921559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_7921559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921559 prefixEnd_7921559 := by exact prefixLift 7921559
  have htrace : WordTrace (prefixWord ++ tailWord_7921559) baseStart_7921559 baseEnd_7921559 := by
    simpa [prefixWord, tailWord_7921559, baseEnd_7921559] using wordTrace_append hprefix tailTrace_7921559
  have hstable : (prefixWord ++ tailWord_7921559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921559).length < 2 ^ (prefixWord ++ tailWord_7921559).sum := by decide
  have hdescent : baseEnd_7921559 < baseStart_7921559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921657 : List Nat := [1, 2, 1, 3, 1, 6, 2, 2, 1, 4]
def baseStart_7921657 : Nat := 118140960795 + 7921657 * 2 ^ 59
def prefixEnd_7921657 : Nat := 4983230072969 + 3 ^ 40 * 7921657 * 2
def baseEnd_7921657 : Nat := 1355872540351206071418823

theorem tailTrace_7921657 : CollatzResearch.WordTrace tailWord_7921657 prefixEnd_7921657 1355872540351206071418823 := by
  unfold tailWord_7921657
  simp only [CollatzResearch.WordTrace]
  refine ⟨288926567062197075149939225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192617711374798050099959483 288926567062197075149939225)
  ·
    refine ⟨216694925296647806362454419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288926567062197075149939225 216694925296647806362454419)
    ·
      refine ⟨325042387944971709543681629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216694925296647806362454419 325042387944971709543681629)
      ·
        refine ⟨121890895479364391078880611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325042387944971709543681629 121890895479364391078880611)
        ·
          refine ⟨182836343219046586618320917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121890895479364391078880611 182836343219046586618320917)
          ·
            refine ⟨8570453588392808747733793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182836343219046586618320917 8570453588392808747733793)
            ·
              refine ⟨6427840191294606560800345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8570453588392808747733793 6427840191294606560800345)
              ·
                refine ⟨4820880143470954920600259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6427840191294606560800345 4820880143470954920600259)
                ·
                  refine ⟨7231320215206432380900389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820880143470954920600259 7231320215206432380900389)
                  ·
                    refine ⟨1355872540351206071418823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7231320215206432380900389 1355872540351206071418823)
                    ·
                      rfl

theorem cell23_7921657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 1, 4].length) (baseStart_7921657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921657 prefixEnd_7921657 := by exact prefixLift 7921657
  have htrace : WordTrace (prefixWord ++ tailWord_7921657) baseStart_7921657 baseEnd_7921657 := by
    simpa [prefixWord, tailWord_7921657, baseEnd_7921657] using wordTrace_append hprefix tailTrace_7921657
  have hstable : (prefixWord ++ tailWord_7921657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921657).length < 2 ^ (prefixWord ++ tailWord_7921657).sum := by decide
  have hdescent : baseEnd_7921657 < baseStart_7921657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921684 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_7921684 : Nat := 118140960795 + 7921684 * 2 ^ 59
def prefixEnd_7921684 : Nat := 4983230072969 + 3 ^ 40 * 7921684 * 2
def baseEnd_7921684 : Nat := 4067631485031289608618845

theorem tailTrace_7921684 : CollatzResearch.WordTrace tailWord_7921684 prefixEnd_7921684 4067631485031289608618845 := by
  unfold tailWord_7921684
  simp only [CollatzResearch.WordTrace]
  refine ⟨144463775916549629380586053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192618367888732839174114737 144463775916549629380586053)
  ·
    refine ⟨27086957984353055508859885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144463775916549629380586053 27086957984353055508859885)
    ·
      refine ⟨10157609244132395815822457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27086957984353055508859885 10157609244132395815822457)
      ·
        refine ⟨7618206933099296861866843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10157609244132395815822457 7618206933099296861866843)
        ·
          refine ⟨11427310399648945292800265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618206933099296861866843 11427310399648945292800265)
          ·
            refine ⟨8570482799736708969600199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11427310399648945292800265 8570482799736708969600199)
            ·
              refine ⟨12855724199605063454400299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570482799736708969600199 12855724199605063454400299)
              ·
                refine ⟨19283586299407595181600449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12855724199605063454400299 19283586299407595181600449)
                ·
                  refine ⟨14462689724555696386200337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19283586299407595181600449 14462689724555696386200337)
                  ·
                    refine ⟨10847017293416772289650253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14462689724555696386200337 10847017293416772289650253)
                    ·
                      refine ⟨4067631485031289608618845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10847017293416772289650253 4067631485031289608618845)
                      ·
                        rfl

theorem cell23_7921684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_7921684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921684 prefixEnd_7921684 := by exact prefixLift 7921684
  have htrace : WordTrace (prefixWord ++ tailWord_7921684) baseStart_7921684 baseEnd_7921684 := by
    simpa [prefixWord, tailWord_7921684, baseEnd_7921684] using wordTrace_append hprefix tailTrace_7921684
  have hstable : (prefixWord ++ tailWord_7921684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921684).length < 2 ^ (prefixWord ++ tailWord_7921684).sum := by decide
  have hdescent : baseEnd_7921684 < baseStart_7921684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921690 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2]
def baseStart_7921690 : Nat := 118140960795 + 7921690 * 2 ^ 59
def prefixEnd_7921690 : Nat := 4983230072969 + 3 ^ 40 * 7921690 * 2
def baseEnd_7921690 : Nat := 4067634565915216585143817

theorem tailTrace_7921690 : CollatzResearch.WordTrace tailWord_7921690 prefixEnd_7921690 4067634565915216585143817 := by
  unfold tailWord_7921690
  simp only [CollatzResearch.WordTrace]
  refine ⟨72231942667769380446472631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192618513780718347857260349 72231942667769380446472631)
  ·
    refine ⟨108347914001654070669708947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72231942667769380446472631 108347914001654070669708947)
    ·
      refine ⟨162521871002481106004563421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108347914001654070669708947 162521871002481106004563421)
      ·
        refine ⟨60945701625930414751711283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162521871002481106004563421 60945701625930414751711283)
        ·
          refine ⟨91418552438895622127566925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60945701625930414751711283 91418552438895622127566925)
          ·
            refine ⟨34281957164585858297837597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91418552438895622127566925 34281957164585858297837597)
            ·
              refine ⟨12855733936719696861689099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34281957164585858297837597 12855733936719696861689099)
              ·
                refine ⟨19283600905079545292533649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12855733936719696861689099 19283600905079545292533649)
                ·
                  refine ⟨14462700678809658969400237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19283600905079545292533649 14462700678809658969400237)
                  ·
                    refine ⟨5423512754553622113525089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14462700678809658969400237 5423512754553622113525089)
                    ·
                      refine ⟨4067634565915216585143817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423512754553622113525089 4067634565915216585143817)
                      ·
                        rfl

theorem cell23_7921690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_7921690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921690 prefixEnd_7921690 := by exact prefixLift 7921690
  have htrace : WordTrace (prefixWord ++ tailWord_7921690) baseStart_7921690 baseEnd_7921690 := by
    simpa [prefixWord, tailWord_7921690, baseEnd_7921690] using wordTrace_append hprefix tailTrace_7921690
  have hstable : (prefixWord ++ tailWord_7921690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921690).length < 2 ^ (prefixWord ++ tailWord_7921690).sum := by decide
  have hdescent : baseEnd_7921690 < baseStart_7921690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921700 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_7921700 : Nat := 118140960795 + 7921700 * 2 ^ 59
def prefixEnd_7921700 : Nat := 4983230072969 + 3 ^ 40 * 7921700 * 2
def baseEnd_7921700 : Nat := 1355879900240587182006257

theorem tailTrace_7921700 : CollatzResearch.WordTrace tailWord_7921700 prefixEnd_7921700 1355879900240587182006257 := by
  unfold tailWord_7921700
  simp only [CollatzResearch.WordTrace]
  refine ⟨144464067700520646746877277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192618756934027528995836369 144464067700520646746877277)
  ·
    refine ⟨54174025387695242530078979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144464067700520646746877277 54174025387695242530078979)
    ·
      refine ⟨81261038081542863795118469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54174025387695242530078979 81261038081542863795118469)
      ·
        refine ⟨15236444640289286961584713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81261038081542863795118469 15236444640289286961584713)
        ·
          refine ⟨11427333480216965221188535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15236444640289286961584713 11427333480216965221188535)
          ·
            refine ⟨17141000220325447831782803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11427333480216965221188535 17141000220325447831782803)
            ·
              refine ⟨25711500330488171747674205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17141000220325447831782803 25711500330488171747674205)
              ·
                refine ⟨9641812623933064405377827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25711500330488171747674205 9641812623933064405377827)
                ·
                  refine ⟨14462718935899596608066741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9641812623933064405377827 14462718935899596608066741)
                  ·
                    refine ⟨1355879900240587182006257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14462718935899596608066741 1355879900240587182006257)
                    ·
                      rfl

theorem cell23_7921700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_7921700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921700 prefixEnd_7921700 := by exact prefixLift 7921700
  have htrace : WordTrace (prefixWord ++ tailWord_7921700) baseStart_7921700 baseEnd_7921700 := by
    simpa [prefixWord, tailWord_7921700, baseEnd_7921700] using wordTrace_append hprefix tailTrace_7921700
  have hstable : (prefixWord ++ tailWord_7921700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921700).length < 2 ^ (prefixWord ++ tailWord_7921700).sum := by decide
  have hdescent : baseEnd_7921700 < baseStart_7921700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921713 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 4, 4]
def baseStart_7921713 : Nat := 118140960795 + 7921713 * 2 ^ 59
def prefixEnd_7921713 : Nat := 4983230072969 + 3 ^ 40 * 7921713 * 2
def baseEnd_7921713 : Nat := 1355882125323423331718737

theorem tailTrace_7921713 : CollatzResearch.WordTrace tailWord_7921713 prefixEnd_7921713 1355882125323423331718737 := by
  unfold tailWord_7921713
  simp only [CollatzResearch.WordTrace]
  refine ⟨288928609549994196713977793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192619073033329464475985195 288928609549994196713977793)
  ·
    refine ⟨216696457162495647535483345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288928609549994196713977793 216696457162495647535483345)
    ·
      refine ⟨162522342871871735651612509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216696457162495647535483345 162522342871871735651612509)
      ·
        refine ⟨60945878576951900869354691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162522342871871735651612509 60945878576951900869354691)
        ·
          refine ⟨91418817865427851304032037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60945878576951900869354691 91418817865427851304032037)
          ·
            refine ⟨17141028349767722119506007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91418817865427851304032037 17141028349767722119506007)
            ·
              refine ⟨25711542524651583179259011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17141028349767722119506007 25711542524651583179259011)
              ·
                refine ⟨38567313786977374768888517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25711542524651583179259011 38567313786977374768888517)
                ·
                  refine ⟨7231371335058257769166597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38567313786977374768888517 7231371335058257769166597)
                  ·
                    refine ⟨1355882125323423331718737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7231371335058257769166597 1355882125323423331718737)
                    ·
                      rfl

theorem cell23_7921713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_7921713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921713 prefixEnd_7921713 := by exact prefixLift 7921713
  have htrace : WordTrace (prefixWord ++ tailWord_7921713) baseStart_7921713 baseEnd_7921713 := by
    simpa [prefixWord, tailWord_7921713, baseEnd_7921713] using wordTrace_append hprefix tailTrace_7921713
  have hstable : (prefixWord ++ tailWord_7921713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921713).length < 2 ^ (prefixWord ++ tailWord_7921713).sum := by decide
  have hdescent : baseEnd_7921713 < baseStart_7921713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921753 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 6, 1, 3]
def baseStart_7921753 : Nat := 118140960795 + 7921753 * 2 ^ 59
def prefixEnd_7921753 : Nat := 4983230072969 + 3 ^ 40 * 7921753 * 2
def baseEnd_7921753 : Nat := 4067666915196449838656027

theorem tailTrace_7921753 : CollatzResearch.WordTrace tailWord_7921753 prefixEnd_7921753 4067666915196449838656027 := by
  unfold tailWord_7921753
  simp only [CollatzResearch.WordTrace]
  refine ⟨288930068469849283545433913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192620045646566189030289275 288930068469849283545433913)
  ·
    refine ⟨216697551352386962659075435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288930068469849283545433913 216697551352386962659075435)
    ·
      refine ⟨325046327028580443988613153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216697551352386962659075435 325046327028580443988613153)
      ·
        refine ⟨243784745271435332991459865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325046327028580443988613153 243784745271435332991459865)
        ·
          refine ⟨182838558953576499743594899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243784745271435332991459865 182838558953576499743594899)
          ·
            refine ⟨274257838430364749615392349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182838558953576499743594899 274257838430364749615392349)
            ·
              refine ⟨102846689411386781105772131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274257838430364749615392349 102846689411386781105772131)
              ·
                refine ⟨154270034117080171658658197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102846689411386781105772131 154270034117080171658658197)
                ·
                  refine ⟨7231407849238133046499603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154270034117080171658658197 7231407849238133046499603)
                  ·
                    refine ⟨10847111773857199569749405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7231407849238133046499603 10847111773857199569749405)
                    ·
                      refine ⟨4067666915196449838656027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10847111773857199569749405 4067666915196449838656027)
                      ·
                        rfl

theorem cell23_7921753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_7921753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921753 prefixEnd_7921753 := by exact prefixLift 7921753
  have htrace : WordTrace (prefixWord ++ tailWord_7921753) baseStart_7921753 baseEnd_7921753 := by
    simpa [prefixWord, tailWord_7921753, baseEnd_7921753] using wordTrace_append hprefix tailTrace_7921753
  have hstable : (prefixWord ++ tailWord_7921753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921753).length < 2 ^ (prefixWord ++ tailWord_7921753).sum := by decide
  have hdescent : baseEnd_7921753 < baseStart_7921753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921757 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7921757 : Nat := 118140960795 + 7921757 * 2 ^ 59
def prefixEnd_7921757 : Nat := 4983230072969 + 3 ^ 40 * 7921757 * 2
def baseEnd_7921757 : Nat := 4067668969119067823006009

theorem tailTrace_7921757 : CollatzResearch.WordTrace tailWord_7921757 prefixEnd_7921757 4067668969119067823006009 := by
  unfold tailWord_7921757
  simp only [CollatzResearch.WordTrace]
  refine ⟨288930214361834792228579525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192620142907889861485719683 288930214361834792228579525)
  ·
    refine ⟨54174415192844023542858661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288930214361834792228579525 54174415192844023542858661)
    ·
      refine ⟨10157702848658254414285999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54174415192844023542858661 10157702848658254414285999)
      ·
        refine ⟨15236554272987381621428999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10157702848658254414285999 15236554272987381621428999)
        ·
          refine ⟨22854831409481072432143499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15236554272987381621428999 22854831409481072432143499)
          ·
            refine ⟨34282247114221608648215249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22854831409481072432143499 34282247114221608648215249)
            ·
              refine ⟨25711685335666206486161437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34282247114221608648215249 25711685335666206486161437)
              ·
                refine ⟨9641882000874827432310539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25711685335666206486161437 9641882000874827432310539)
                ·
                  refine ⟨14462823001312241148465809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9641882000874827432310539 14462823001312241148465809)
                  ·
                    refine ⟨10847117250984180861349357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14462823001312241148465809 10847117250984180861349357)
                    ·
                      refine ⟨4067668969119067823006009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10847117250984180861349357 4067668969119067823006009)
                      ·
                        rfl

theorem cell23_7921757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7921757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921757 prefixEnd_7921757 := by exact prefixLift 7921757
  have htrace : WordTrace (prefixWord ++ tailWord_7921757) baseStart_7921757 baseEnd_7921757 := by
    simpa [prefixWord, tailWord_7921757, baseEnd_7921757] using wordTrace_append hprefix tailTrace_7921757
  have hstable : (prefixWord ++ tailWord_7921757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921757).length < 2 ^ (prefixWord ++ tailWord_7921757).sum := by decide
  have hdescent : baseEnd_7921757 < baseStart_7921757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921797 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 1, 3, 2]
def baseStart_7921797 : Nat := 118140960795 + 7921797 * 2 ^ 59
def prefixEnd_7921797 : Nat := 4983230072969 + 3 ^ 40 * 7921797 * 2
def baseEnd_7921797 : Nat := 4067689508345247666505825

theorem tailTrace_7921797 : CollatzResearch.WordTrace tailWord_7921797 prefixEnd_7921797 4067689508345247666505825 := by
  unfold tailWord_7921797
  simp only [CollatzResearch.WordTrace]
  refine ⟨288931673281689879060035645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192621115521126586040023763 288931673281689879060035645)
  ·
    refine ⟨108349377480633704647513367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288931673281689879060035645 108349377480633704647513367)
    ·
      refine ⟨162524066220950556971270051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108349377480633704647513367 162524066220950556971270051)
      ·
        refine ⟨243786099331425835456905077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162524066220950556971270051 243786099331425835456905077)
        ·
          refine ⟨22854946812321172074084851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243786099331425835456905077 22854946812321172074084851)
          ·
            refine ⟨34282420218481758111127277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22854946812321172074084851 34282420218481758111127277)
            ·
              refine ⟨12855907581930659291672729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34282420218481758111127277 12855907581930659291672729)
              ·
                refine ⟨9641930686447994468754547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12855907581930659291672729 9641930686447994468754547)
                ·
                  refine ⟨14462896029671991703131821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9641930686447994468754547 14462896029671991703131821)
                  ·
                    refine ⟨5423586011126996888674433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14462896029671991703131821 5423586011126996888674433)
                    ·
                      refine ⟨4067689508345247666505825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423586011126996888674433 4067689508345247666505825)
                      ·
                        rfl

theorem cell23_7921797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_7921797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921797 prefixEnd_7921797 := by exact prefixLift 7921797
  have htrace : WordTrace (prefixWord ++ tailWord_7921797) baseStart_7921797 baseEnd_7921797 := by
    simpa [prefixWord, tailWord_7921797, baseEnd_7921797] using wordTrace_append hprefix tailTrace_7921797
  have hstable : (prefixWord ++ tailWord_7921797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921797).length < 2 ^ (prefixWord ++ tailWord_7921797).sum := by decide
  have hdescent : baseEnd_7921797 < baseStart_7921797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921878 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_7921878 : Nat := 118140960795 + 7921878 * 2 ^ 59
def prefixEnd_7921878 : Nat := 4983230072969 + 3 ^ 40 * 7921878 * 2
def baseEnd_7921878 : Nat := 4067731100278261849592953

theorem tailTrace_7921878 : CollatzResearch.WordTrace tailWord_7921878 prefixEnd_7921878 4067731100278261849592953 := by
  unfold tailWord_7921878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18058414224649776868358393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192623085062930953262489525 18058414224649776868358393)
  ·
    refine ⟨13543810668487332651268795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18058414224649776868358393 13543810668487332651268795)
    ·
      refine ⟨20315716002730998976903193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13543810668487332651268795 20315716002730998976903193)
      ·
        refine ⟨15236787002048249232677395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20315716002730998976903193 15236787002048249232677395)
        ·
          refine ⟨22855180503072373849016093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15236787002048249232677395 22855180503072373849016093)
          ·
            refine ⟨8570692688652140193381035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22855180503072373849016093 8570692688652140193381035)
            ·
              refine ⟨12856039032978210290071553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570692688652140193381035 12856039032978210290071553)
              ·
                refine ⟨9642029274733657717553665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12856039032978210290071553 9642029274733657717553665)
                ·
                  refine ⟨7231521956050243288165249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9642029274733657717553665 7231521956050243288165249)
                  ·
                    refine ⟨5423641467037682466123937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7231521956050243288165249 5423641467037682466123937)
                    ·
                      refine ⟨4067731100278261849592953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423641467037682466123937 4067731100278261849592953)
                      ·
                        rfl

theorem cell23_7921878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_7921878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921878 prefixEnd_7921878 := by exact prefixLift 7921878
  have htrace : WordTrace (prefixWord ++ tailWord_7921878) baseStart_7921878 baseEnd_7921878 := by
    simpa [prefixWord, tailWord_7921878, baseEnd_7921878] using wordTrace_append hprefix tailTrace_7921878
  have hstable : (prefixWord ++ tailWord_7921878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921878).length < 2 ^ (prefixWord ++ tailWord_7921878).sum := by decide
  have hdescent : baseEnd_7921878 < baseStart_7921878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921900 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 2, 4, 2]
def baseStart_7921900 : Nat := 118140960795 + 7921900 * 2 ^ 59
def prefixEnd_7921900 : Nat := 4983230072969 + 3 ^ 40 * 7921900 * 2
def baseEnd_7921900 : Nat := 4067742396852660763517851

theorem tailTrace_7921900 : CollatzResearch.WordTrace tailWord_7921900 prefixEnd_7921900 4067742396852660763517851 := by
  unfold tailWord_7921900
  simp only [CollatzResearch.WordTrace]
  refine ⟨144467715000158363825517577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192623620000211151767356769 144467715000158363825517577)
  ·
    refine ⟨108350786250118772869138183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144467715000158363825517577 108350786250118772869138183)
    ·
      refine ⟨162526179375178159303707275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108350786250118772869138183 162526179375178159303707275)
      ·
        refine ⟨243789269062767238955560913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162526179375178159303707275 243789269062767238955560913)
        ·
          refine ⟨182841951797075429216670685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243789269062767238955560913 182841951797075429216670685)
          ·
            refine ⟨68565731923903285956251507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182841951797075429216670685 68565731923903285956251507)
            ·
              refine ⟨102848597885854928934377261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68565731923903285956251507 102848597885854928934377261)
              ·
                refine ⟨38568224207195598350391473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102848597885854928934377261 38568224207195598350391473)
                ·
                  refine ⟨28926168155396698762793605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38568224207195598350391473 28926168155396698762793605)
                  ·
                    refine ⟨5423656529136881018023801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28926168155396698762793605 5423656529136881018023801)
                    ·
                      refine ⟨4067742396852660763517851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423656529136881018023801 4067742396852660763517851)
                      ·
                        rfl

theorem cell23_7921900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_7921900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921900 prefixEnd_7921900 := by exact prefixLift 7921900
  have htrace : WordTrace (prefixWord ++ tailWord_7921900) baseStart_7921900 baseEnd_7921900 := by
    simpa [prefixWord, tailWord_7921900, baseEnd_7921900] using wordTrace_append hprefix tailTrace_7921900
  have hstable : (prefixWord ++ tailWord_7921900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921900).length < 2 ^ (prefixWord ++ tailWord_7921900).sum := by decide
  have hdescent : baseEnd_7921900 < baseStart_7921900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7921944 : List Nat := [2, 1, 2, 3, 1, 2, 5, 2, 1, 4]
def baseStart_7921944 : Nat := 118140960795 + 7921944 * 2 ^ 59
def prefixEnd_7921944 : Nat := 4983230072969 + 3 ^ 40 * 7921944 * 2
def baseEnd_7921944 : Nat := 1355921663333819530455883

theorem tailTrace_7921944 : CollatzResearch.WordTrace tailWord_7921944 prefixEnd_7921944 1355921663333819530455883 := by
  unfold tailWord_7921944
  simp only [CollatzResearch.WordTrace]
  refine ⟨144468517406078661582818443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192624689874771548777091257 144468517406078661582818443)
  ·
    refine ⟨216702776109117992374227665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144468517406078661582818443 216702776109117992374227665)
    ·
      refine ⟨162527082081838494280670749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216702776109117992374227665 162527082081838494280670749)
      ·
        refine ⟨60947655780689435355251531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162527082081838494280670749 60947655780689435355251531)
        ·
          refine ⟨91421483671034153032877297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60947655780689435355251531 91421483671034153032877297)
          ·
            refine ⟨68566112753275614774657973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91421483671034153032877297 68566112753275614774657973)
            ·
              refine ⟨6428073070619588885124185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68566112753275614774657973 6428073070619588885124185)
              ·
                refine ⟨4821054802964691663843139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6428073070619588885124185 4821054802964691663843139)
                ·
                  refine ⟨7231582204447037495764709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821054802964691663843139 7231582204447037495764709)
                  ·
                    refine ⟨1355921663333819530455883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7231582204447037495764709 1355921663333819530455883)
                    ·
                      rfl

theorem cell23_7921944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_7921944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7921944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7921944 prefixEnd_7921944 := by exact prefixLift 7921944
  have htrace : WordTrace (prefixWord ++ tailWord_7921944) baseStart_7921944 baseEnd_7921944 := by
    simpa [prefixWord, tailWord_7921944, baseEnd_7921944] using wordTrace_append hprefix tailTrace_7921944
  have hstable : (prefixWord ++ tailWord_7921944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7921944).length < 2 ^ (prefixWord ++ tailWord_7921944).sum := by decide
  have hdescent : baseEnd_7921944 < baseStart_7921944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7921944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922001 : List Nat := [1, 2, 2, 1, 4, 2, 4, 2, 1, 1, 3]
def baseStart_7922001 : Nat := 118140960795 + 7922001 * 2 ^ 59
def prefixEnd_7922001 : Nat := 4983230072969 + 3 ^ 40 * 7922001 * 2
def baseEnd_7922001 : Nat := 4067794258398764868354887

theorem tailTrace_7922001 : CollatzResearch.WordTrace tailWord_7922001 prefixEnd_7922001 4067794258398764868354887 := by
  unfold tailWord_7922001
  simp only [CollatzResearch.WordTrace]
  refine ⟨288939113772950821900461857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192626075848633881266974571 288939113772950821900461857)
  ·
    refine ⟨216704335329713116425346393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288939113772950821900461857 216704335329713116425346393)
    ·
      refine ⟨162528251497284837319009795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216704335329713116425346393 162528251497284837319009795)
      ·
        refine ⟨243792377245927255978514693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162528251497284837319009795 243792377245927255978514693)
        ·
          refine ⟨45711070733611360495971505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243792377245927255978514693 45711070733611360495971505)
          ·
            refine ⟨34283303050208520371978629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45711070733611360495971505 34283303050208520371978629)
            ·
              refine ⟨6428119321914097569745993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34283303050208520371978629 6428119321914097569745993)
              ·
                refine ⟨4821089491435573177309495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6428119321914097569745993 4821089491435573177309495)
                ·
                  refine ⟨7231634237153359765964243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821089491435573177309495 7231634237153359765964243)
                  ·
                    refine ⟨10847451355730039648946365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7231634237153359765964243 10847451355730039648946365)
                    ·
                      refine ⟨4067794258398764868354887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10847451355730039648946365 4067794258398764868354887)
                      ·
                        rfl

theorem cell23_7922001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 1, 1, 3].length) (baseStart_7922001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922001 prefixEnd_7922001 := by exact prefixLift 7922001
  have htrace : WordTrace (prefixWord ++ tailWord_7922001) baseStart_7922001 baseEnd_7922001 := by
    simpa [prefixWord, tailWord_7922001, baseEnd_7922001] using wordTrace_append hprefix tailTrace_7922001
  have hstable : (prefixWord ++ tailWord_7922001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922001).length < 2 ^ (prefixWord ++ tailWord_7922001).sum := by decide
  have hdescent : baseEnd_7922001 < baseStart_7922001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922003 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 6]
def baseStart_7922003 : Nat := 118140960795 + 7922003 * 2 ^ 59
def prefixEnd_7922003 : Nat := 4983230072969 + 3 ^ 40 * 7922003 * 2
def baseEnd_7922003 : Nat := 4067795285360073860529877

theorem tailTrace_7922003 : CollatzResearch.WordTrace tailWord_7922003 prefixEnd_7922003 4067795285360073860529877 := by
  unfold tailWord_7922003
  simp only [CollatzResearch.WordTrace]
  refine ⟨288939186718943576242034663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192626124479295717494689775 288939186718943576242034663)
  ·
    refine ⟨433408780078415364363051995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288939186718943576242034663 433408780078415364363051995)
    ·
      refine ⟨650113170117623046544577993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433408780078415364363051995 650113170117623046544577993)
      ·
        refine ⟨487584877588217284908433495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650113170117623046544577993 487584877588217284908433495)
        ·
          refine ⟨731377316382325927362650243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487584877588217284908433495 731377316382325927362650243)
          ·
            refine ⟨1097065974573488891043975365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731377316382325927362650243 1097065974573488891043975365)
            ·
              refine ⟨205699870232529167070745381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1097065974573488891043975365 205699870232529167070745381)
              ·
                refine ⟨38568725668599218825764759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205699870232529167070745381 38568725668599218825764759)
                ·
                  refine ⟨57853088502898828238647139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38568725668599218825764759 57853088502898828238647139)
                  ·
                    refine ⟨86779632754348242357970709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57853088502898828238647139 86779632754348242357970709)
                    ·
                      refine ⟨4067795285360073860529877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86779632754348242357970709 4067795285360073860529877)
                      ·
                        rfl

theorem cell23_7922003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_7922003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922003 prefixEnd_7922003 := by exact prefixLift 7922003
  have htrace : WordTrace (prefixWord ++ tailWord_7922003) baseStart_7922003 baseEnd_7922003 := by
    simpa [prefixWord, tailWord_7922003, baseEnd_7922003] using wordTrace_append hprefix tailTrace_7922003
  have hstable : (prefixWord ++ tailWord_7922003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922003).length < 2 ^ (prefixWord ++ tailWord_7922003).sum := by decide
  have hdescent : baseEnd_7922003 < baseStart_7922003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922024 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_7922024 : Nat := 118140960795 + 7922024 * 2 ^ 59
def prefixEnd_7922024 : Nat := 4983230072969 + 3 ^ 40 * 7922024 * 2
def baseEnd_7922024 : Nat := 4067806068453818278367281

theorem tailTrace_7922024 : CollatzResearch.WordTrace tailWord_7922024 prefixEnd_7922024 4067806068453818278367281 := by
  unfold tailWord_7922024
  simp only [CollatzResearch.WordTrace]
  refine ⟨144469976325933748414274563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192626635101244997885699417 144469976325933748414274563)
  ·
    refine ⟨216704964488900622621411845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144469976325933748414274563 216704964488900622621411845)
    ·
      refine ⟨40632180841668866741514721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216704964488900622621411845 40632180841668866741514721)
      ·
        refine ⟨30474135631251650056136041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40632180841668866741514721 30474135631251650056136041)
        ·
          refine ⟨22855601723438737542102031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30474135631251650056136041 22855601723438737542102031)
          ·
            refine ⟨34283402585158106313153047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22855601723438737542102031 34283402585158106313153047)
            ·
              refine ⟨51425103877737159469729571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34283402585158106313153047 51425103877737159469729571)
              ·
                refine ⟨77137655816605739204594357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51425103877737159469729571 77137655816605739204594357)
                ·
                  refine ⟨7231655232806788050430721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77137655816605739204594357 7231655232806788050430721)
                  ·
                    refine ⟨5423741424605091037823041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7231655232806788050430721 5423741424605091037823041)
                    ·
                      refine ⟨4067806068453818278367281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423741424605091037823041 4067806068453818278367281)
                      ·
                        rfl

theorem cell23_7922024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_7922024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922024 prefixEnd_7922024 := by exact prefixLift 7922024
  have htrace : WordTrace (prefixWord ++ tailWord_7922024) baseStart_7922024 baseEnd_7922024 := by
    simpa [prefixWord, tailWord_7922024, baseEnd_7922024] using wordTrace_append hprefix tailTrace_7922024
  have hstable : (prefixWord ++ tailWord_7922024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922024).length < 2 ^ (prefixWord ++ tailWord_7922024).sum := by decide
  have hdescent : baseEnd_7922024 < baseStart_7922024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922037 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_7922037 : Nat := 118140960795 + 7922037 * 2 ^ 59
def prefixEnd_7922037 : Nat := 4983230072969 + 3 ^ 40 * 7922037 * 2
def baseEnd_7922037 : Nat := 4067812743702326727504721

theorem tailTrace_7922037 : CollatzResearch.WordTrace tailWord_7922037 prefixEnd_7922037 4067812743702326727504721 := by
  unfold tailWord_7922037
  simp only [CollatzResearch.WordTrace]
  refine ⟨288940426800820400048772365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192626951200546933365848243 288940426800820400048772365)
  ·
    refine ⟨108352660050307650018289637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288940426800820400048772365 108352660050307650018289637)
    ·
      refine ⟨20316123759432684378429307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108352660050307650018289637 20316123759432684378429307)
      ·
        refine ⟨30474185639149026567643961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20316123759432684378429307 30474185639149026567643961)
        ·
          refine ⟨22855639229361769925732971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30474185639149026567643961 22855639229361769925732971)
          ·
            refine ⟨34283458844042654888599457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22855639229361769925732971 34283458844042654888599457)
            ·
              refine ⟨25712594133031991166449593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34283458844042654888599457 25712594133031991166449593)
              ·
                refine ⟨19284445599773993374837195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25712594133031991166449593 19284445599773993374837195)
                ·
                  refine ⟨28926668399660990062255793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19284445599773993374837195 28926668399660990062255793)
                  ·
                    refine ⟨21695001299745742546691845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28926668399660990062255793 21695001299745742546691845)
                    ·
                      refine ⟨4067812743702326727504721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21695001299745742546691845 4067812743702326727504721)
                      ·
                        rfl

theorem cell23_7922037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_7922037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922037 prefixEnd_7922037 := by exact prefixLift 7922037
  have htrace : WordTrace (prefixWord ++ tailWord_7922037) baseStart_7922037 baseEnd_7922037 := by
    simpa [prefixWord, tailWord_7922037, baseEnd_7922037] using wordTrace_append hprefix tailTrace_7922037
  have hstable : (prefixWord ++ tailWord_7922037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922037).length < 2 ^ (prefixWord ++ tailWord_7922037).sum := by decide
  have hdescent : baseEnd_7922037 < baseStart_7922037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922038 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_7922038 : Nat := 118140960795 + 7922038 * 2 ^ 59
def prefixEnd_7922038 : Nat := 4983230072969 + 3 ^ 40 * 7922038 * 2
def baseEnd_7922038 : Nat := 1355937752394327074530739

theorem tailTrace_7922038 : CollatzResearch.WordTrace tailWord_7922038 prefixEnd_7922038 1355937752394327074530739 := by
  unfold tailWord_7922038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18058778954613548576222423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192626975515877851479705845 18058778954613548576222423)
  ·
    refine ⟨27088168431920322864333635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18058778954613548576222423 27088168431920322864333635)
    ·
      refine ⟨40632252647880484296500453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27088168431920322864333635 40632252647880484296500453)
      ·
        refine ⟨7618547371477590805593835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40632252647880484296500453 7618547371477590805593835)
        ·
          refine ⟨11427821057216386208390753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618547371477590805593835 11427821057216386208390753)
          ·
            refine ⟨8570865792912289656293065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11427821057216386208390753 8570865792912289656293065)
            ·
              refine ⟨6428149344684217242219799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8570865792912289656293065 6428149344684217242219799)
              ·
                refine ⟨9642224017026325863329699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428149344684217242219799 9642224017026325863329699)
                ·
                  refine ⟨14463336025539488794994549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9642224017026325863329699 14463336025539488794994549)
                  ·
                    refine ⟨1355937752394327074530739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14463336025539488794994549 1355937752394327074530739)
                    ·
                      rfl

theorem cell23_7922038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_7922038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922038 prefixEnd_7922038 := by exact prefixLift 7922038
  have htrace : WordTrace (prefixWord ++ tailWord_7922038) baseStart_7922038 baseEnd_7922038 := by
    simpa [prefixWord, tailWord_7922038, baseEnd_7922038] using wordTrace_append hprefix tailTrace_7922038
  have hstable : (prefixWord ++ tailWord_7922038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922038).length < 2 ^ (prefixWord ++ tailWord_7922038).sum := by decide
  have hdescent : baseEnd_7922038 < baseStart_7922038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922051 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 2, 4]
def baseStart_7922051 : Nat := 118140960795 + 7922051 * 2 ^ 59
def prefixEnd_7922051 : Nat := 4983230072969 + 3 ^ 40 * 7922051 * 2
def baseEnd_7922051 : Nat := 1355939977477163224243219

theorem tailTrace_7922051 : CollatzResearch.WordTrace tailWord_7922051 prefixEnd_7922051 1355939977477163224243219 := by
  unfold tailWord_7922051
  simp only [CollatzResearch.WordTrace]
  refine ⟨288940937422769680439782007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192627291615179786959854671 288940937422769680439782007)
  ·
    refine ⟨433411406134154520659673011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288940937422769680439782007 433411406134154520659673011)
    ·
      refine ⟨650117109201231780989509517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433411406134154520659673011 650117109201231780989509517)
      ·
        refine ⟨243793915950461917871066069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 650117109201231780989509517 243793915950461917871066069)
        ·
          refine ⟨5713919905088951200103111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 243793915950461917871066069 5713919905088951200103111)
          ·
            refine ⟨8570879857633426800154667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713919905088951200103111 8570879857633426800154667)
            ·
              refine ⟨12856319786450140200232001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570879857633426800154667 12856319786450140200232001)
              ·
                refine ⟨9642239839837605150174001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12856319786450140200232001 9642239839837605150174001)
                ·
                  refine ⟨7231679879878203862630501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9642239839837605150174001 7231679879878203862630501)
                  ·
                    refine ⟨1355939977477163224243219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7231679879878203862630501 1355939977477163224243219)
                    ·
                      rfl

theorem cell23_7922051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 2, 4].length) (baseStart_7922051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922051 prefixEnd_7922051 := by exact prefixLift 7922051
  have htrace : WordTrace (prefixWord ++ tailWord_7922051) baseStart_7922051 baseEnd_7922051 := by
    simpa [prefixWord, tailWord_7922051, baseEnd_7922051] using wordTrace_append hprefix tailTrace_7922051
  have hstable : (prefixWord ++ tailWord_7922051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922051).length < 2 ^ (prefixWord ++ tailWord_7922051).sum := by decide
  have hdescent : baseEnd_7922051 < baseStart_7922051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922058 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7922058 : Nat := 118140960795 + 7922058 * 2 ^ 59
def prefixEnd_7922058 : Nat := 4983230072969 + 3 ^ 40 * 7922058 * 2
def baseEnd_7922058 : Nat := 4067823526796071145342125

theorem tailTrace_7922058 : CollatzResearch.WordTrace tailWord_7922058 prefixEnd_7922058 4067823526796071145342125 := by
  unfold tailWord_7922058
  simp only [CollatzResearch.WordTrace]
  refine ⟨72235298183436080158821707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192627461822496213756857885 72235298183436080158821707)
  ·
    refine ⟨108352947275154120238232561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72235298183436080158821707 108352947275154120238232561)
    ·
      refine ⟨81264710456365590178674421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108352947275154120238232561 81264710456365590178674421)
      ·
        refine ⟨7618566605284274079250727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81264710456365590178674421 7618566605284274079250727)
        ·
          refine ⟨11427849907926411118876091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618566605284274079250727 11427849907926411118876091)
          ·
            refine ⟨17141774861889616678314137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11427849907926411118876091 17141774861889616678314137)
            ·
              refine ⟨12856331146417212508735603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17141774861889616678314137 12856331146417212508735603)
              ·
                refine ⟨19284496719625818763103405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12856331146417212508735603 19284496719625818763103405)
                ·
                  refine ⟨7231686269859682036163777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19284496719625818763103405 7231686269859682036163777)
                  ·
                    refine ⟨5423764702394761527122833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7231686269859682036163777 5423764702394761527122833)
                    ·
                      refine ⟨4067823526796071145342125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423764702394761527122833 4067823526796071145342125)
                      ·
                        rfl

theorem cell23_7922058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7922058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922058 prefixEnd_7922058 := by exact prefixLift 7922058
  have htrace : WordTrace (prefixWord ++ tailWord_7922058) baseStart_7922058 baseEnd_7922058 := by
    simpa [prefixWord, tailWord_7922058, baseEnd_7922058] using wordTrace_append hprefix tailTrace_7922058
  have hstable : (prefixWord ++ tailWord_7922058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922058).length < 2 ^ (prefixWord ++ tailWord_7922058).sum := by decide
  have hdescent : baseEnd_7922058 < baseStart_7922058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922074 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3]
def baseStart_7922074 : Nat := 118140960795 + 7922074 * 2 ^ 59
def prefixEnd_7922074 : Nat := 4983230072969 + 3 ^ 40 * 7922074 * 2
def baseEnd_7922074 : Nat := 4067831742486543082742051

theorem tailTrace_7922074 : CollatzResearch.WordTrace tailWord_7922074 prefixEnd_7922074 4067831742486543082742051 := by
  unfold tailWord_7922074
  simp only [CollatzResearch.WordTrace]
  refine ⟨72235444075421588841967319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192627850867790903578579517 72235444075421588841967319)
  ·
    refine ⟨108353166113132383262950979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72235444075421588841967319 108353166113132383262950979)
    ·
      refine ⟨162529749169698574894426469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108353166113132383262950979 162529749169698574894426469)
      ·
        refine ⟨30474327969318482792704963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162529749169698574894426469 30474327969318482792704963)
        ·
          refine ⟨45711491953977724189057445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30474327969318482792704963 45711491953977724189057445)
          ·
            refine ⟨8570904741370823285448271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45711491953977724189057445 8570904741370823285448271)
            ·
              refine ⟨12856357112056234928172407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570904741370823285448271 12856357112056234928172407)
              ·
                refine ⟨19284535668084352392258611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12856357112056234928172407 19284535668084352392258611)
                ·
                  refine ⟨28926803502126528588387917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19284535668084352392258611 28926803502126528588387917)
                  ·
                    refine ⟨10847551313297448220645469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28926803502126528588387917 10847551313297448220645469)
                    ·
                      refine ⟨4067831742486543082742051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10847551313297448220645469 4067831742486543082742051)
                      ·
                        rfl

theorem cell23_7922074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_7922074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922074 prefixEnd_7922074 := by exact prefixLift 7922074
  have htrace : WordTrace (prefixWord ++ tailWord_7922074) baseStart_7922074 baseEnd_7922074 := by
    simpa [prefixWord, tailWord_7922074, baseEnd_7922074] using wordTrace_append hprefix tailTrace_7922074
  have hstable : (prefixWord ++ tailWord_7922074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922074).length < 2 ^ (prefixWord ++ tailWord_7922074).sum := by decide
  have hdescent : baseEnd_7922074 < baseStart_7922074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922081 : List Nat := [1, 2, 3, 5, 2, 1, 2, 7]
def baseStart_7922081 : Nat := 118140960795 + 7922081 * 2 ^ 59
def prefixEnd_7922081 : Nat := 4983230072969 + 3 ^ 40 * 7922081 * 2
def baseEnd_7922081 : Nat := 150660568031523131679797

theorem tailTrace_7922081 : CollatzResearch.WordTrace tailWord_7922081 prefixEnd_7922081 150660568031523131679797 := by
  unfold tailWord_7922081
  simp only [CollatzResearch.WordTrace]
  refine ⟨288942031612660995563374097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192628021075107330375582731 288942031612660995563374097)
  ·
    refine ⟨216706523709495746672530573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288942031612660995563374097 216706523709495746672530573)
    ·
      refine ⟨81264946391060905002198965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216706523709495746672530573 81264946391060905002198965)
      ·
        refine ⟨7618588724161959843956153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81264946391060905002198965 7618588724161959843956153)
        ·
          refine ⟨5713941543121469882967115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7618588724161959843956153 5713941543121469882967115)
          ·
            refine ⟨8570912314682204824450673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713941543121469882967115 8570912314682204824450673)
            ·
              refine ⟨6428184236011653618338005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8570912314682204824450673 6428184236011653618338005)
              ·
                refine ⟨150660568031523131679797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6428184236011653618338005 150660568031523131679797)
                ·
                  rfl

theorem cell23_7922081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 7].length) (baseStart_7922081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922081 prefixEnd_7922081 := by exact prefixLift 7922081
  have htrace : WordTrace (prefixWord ++ tailWord_7922081) baseStart_7922081 baseEnd_7922081 := by
    simpa [prefixWord, tailWord_7922081, baseEnd_7922081] using wordTrace_append hprefix tailTrace_7922081
  have hstable : (prefixWord ++ tailWord_7922081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922081).length < 2 ^ (prefixWord ++ tailWord_7922081).sum := by decide
  have hdescent : baseEnd_7922081 < baseStart_7922081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922084 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 1, 3, 2]
def baseStart_7922084 : Nat := 118140960795 + 7922084 * 2 ^ 59
def prefixEnd_7922084 : Nat := 4983230072969 + 3 ^ 40 * 7922084 * 2
def baseEnd_7922084 : Nat := 4067836877293088043617005

theorem tailTrace_7922084 : CollatzResearch.WordTrace tailWord_7922084 prefixEnd_7922084 4067836877293088043617005 := by
  unfold tailWord_7922084
  simp only [CollatzResearch.WordTrace]
  refine ⟨144471070515825063537866653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192628094021100084717155537 144471070515825063537866653)
  ·
    refine ⟨54176651443434398826699995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144471070515825063537866653 54176651443434398826699995)
    ·
      refine ⟨81264977165151598240049993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54176651443434398826699995 81264977165151598240049993)
      ·
        refine ⟨60948732873863698680037495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81264977165151598240049993 60948732873863698680037495)
        ·
          refine ⟨91423099310795548020056243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60948732873863698680037495 91423099310795548020056243)
          ·
            refine ⟨137134648966193322030084365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91423099310795548020056243 137134648966193322030084365)
            ·
              refine ⟨51425493362322495761281637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137134648966193322030084365 51425493362322495761281637)
              ·
                refine ⟨9642280005435467955240307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51425493362322495761281637 9642280005435467955240307)
                ·
                  refine ⟨14463420008153201932860461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9642280005435467955240307 14463420008153201932860461)
                  ·
                    refine ⟨5423782503057450724822673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14463420008153201932860461 5423782503057450724822673)
                    ·
                      refine ⟨4067836877293088043617005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423782503057450724822673 4067836877293088043617005)
                      ·
                        rfl

theorem cell23_7922084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_7922084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922084 prefixEnd_7922084 := by exact prefixLift 7922084
  have htrace : WordTrace (prefixWord ++ tailWord_7922084) baseStart_7922084 baseEnd_7922084 := by
    simpa [prefixWord, tailWord_7922084, baseEnd_7922084] using wordTrace_append hprefix tailTrace_7922084
  have hstable : (prefixWord ++ tailWord_7922084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922084).length < 2 ^ (prefixWord ++ tailWord_7922084).sum := by decide
  have hdescent : baseEnd_7922084 < baseStart_7922084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922160 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_7922160 : Nat := 118140960795 + 7922160 * 2 ^ 59
def prefixEnd_7922160 : Nat := 4983230072969 + 3 ^ 40 * 7922160 * 2
def baseEnd_7922160 : Nat := 4067875901822829746266655

theorem tailTrace_7922160 : CollatzResearch.WordTrace tailWord_7922160 prefixEnd_7922160 4067875901822829746266655 := by
  unfold tailWord_7922160
  simp only [CollatzResearch.WordTrace]
  refine ⟨144472456489687396027749967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192629941986249861370333289 144472456489687396027749967)
  ·
    refine ⟨216708684734531094041624951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144472456489687396027749967 216708684734531094041624951)
    ·
      refine ⟨325063027101796641062437427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216708684734531094041624951 325063027101796641062437427)
      ·
        refine ⟨487594540652694961593656141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325063027101796641062437427 487594540652694961593656141)
        ·
          refine ⟨182847952744760610597621053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487594540652694961593656141 182847952744760610597621053)
          ·
            refine ⟨68567982279285228974107895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182847952744760610597621053 68567982279285228974107895)
            ·
              refine ⟨102851973418927843461161843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68567982279285228974107895 102851973418927843461161843)
              ·
                refine ⟨154277960128391765191742765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102851973418927843461161843 154277960128391765191742765)
                ·
                  refine ⟨57854235048146911946903537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154277960128391765191742765 57854235048146911946903537)
                  ·
                    refine ⟨43390676286110183960177653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57854235048146911946903537 43390676286110183960177653)
                    ·
                      refine ⟨4067875901822829746266655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43390676286110183960177653 4067875901822829746266655)
                      ·
                        rfl

theorem cell23_7922160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_7922160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922160 prefixEnd_7922160 := by exact prefixLift 7922160
  have htrace : WordTrace (prefixWord ++ tailWord_7922160) baseStart_7922160 baseEnd_7922160 := by
    simpa [prefixWord, tailWord_7922160, baseEnd_7922160] using wordTrace_append hprefix tailTrace_7922160
  have hstable : (prefixWord ++ tailWord_7922160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922160).length < 2 ^ (prefixWord ++ tailWord_7922160).sum := by decide
  have hdescent : baseEnd_7922160 < baseStart_7922160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922165 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_7922165 : Nat := 118140960795 + 7922165 * 2 ^ 59
def prefixEnd_7922165 : Nat := 4983230072969 + 3 ^ 40 * 7922165 * 2
def baseEnd_7922165 : Nat := 4067878469226102226704133

theorem tailTrace_7922165 : CollatzResearch.WordTrace tailWord_7922165 prefixEnd_7922165 4067878469226102226704133 := by
  unfold tailWord_7922165
  simp only [CollatzResearch.WordTrace]
  refine ⟨288945095344356677909431949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192630063562904451939621299 288945095344356677909431949)
  ·
    refine ⟨108354410754133754216036981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288945095344356677909431949 108354410754133754216036981)
    ·
      refine ⟨10158226008200039457753467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108354410754133754216036981 10158226008200039457753467)
      ·
        refine ⟨15237339012300059186630201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10158226008200039457753467 15237339012300059186630201)
        ·
          refine ⟨11428004259225044389972651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15237339012300059186630201 11428004259225044389972651)
          ·
            refine ⟨17142006388837566584958977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11428004259225044389972651 17142006388837566584958977)
            ·
              refine ⟨12856504791628174938719233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17142006388837566584958977 12856504791628174938719233)
              ·
                refine ⟨9642378593721131204039425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12856504791628174938719233 9642378593721131204039425)
                ·
                  refine ⟨7231783945290848403029569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9642378593721131204039425 7231783945290848403029569)
                  ·
                    refine ⟨5423837958968136302272177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7231783945290848403029569 5423837958968136302272177)
                    ·
                      refine ⟨4067878469226102226704133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423837958968136302272177 4067878469226102226704133)
                      ·
                        rfl

theorem cell23_7922165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_7922165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922165 prefixEnd_7922165 := by exact prefixLift 7922165
  have htrace : WordTrace (prefixWord ++ tailWord_7922165) baseStart_7922165 baseEnd_7922165 := by
    simpa [prefixWord, tailWord_7922165, baseEnd_7922165] using wordTrace_append hprefix tailTrace_7922165
  have hstable : (prefixWord ++ tailWord_7922165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922165).length < 2 ^ (prefixWord ++ tailWord_7922165).sum := by decide
  have hdescent : baseEnd_7922165 < baseStart_7922165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922177 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_7922177 : Nat := 118140960795 + 7922177 * 2 ^ 59
def prefixEnd_7922177 : Nat := 4983230072969 + 3 ^ 40 * 7922177 * 2
def baseEnd_7922177 : Nat := 4067884630993956179754077

theorem tailTrace_7922177 : CollatzResearch.WordTrace tailWord_7922177 prefixEnd_7922177 4067884630993956179754077 := by
  unfold tailWord_7922177
  simp only [CollatzResearch.WordTrace]
  refine ⟨288945533020313203958868785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192630355346875469305912523 288945533020313203958868785)
  ·
    refine ⟨216709149765234902969151589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288945533020313203958868785 216709149765234902969151589)
    ·
      refine ⟨40632965580981544306715923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216709149765234902969151589 40632965580981544306715923)
      ·
        refine ⟨60949448371472316460073885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40632965580981544306715923 60949448371472316460073885)
        ·
          refine ⟨22856043139302118672527707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60949448371472316460073885 22856043139302118672527707)
          ·
            refine ⟨34284064708953178008791561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22856043139302118672527707 34284064708953178008791561)
            ·
              refine ⟨25713048531714883506593671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34284064708953178008791561 25713048531714883506593671)
              ·
                refine ⟨38569572797572325259890507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25713048531714883506593671 38569572797572325259890507)
                ·
                  refine ⟨57854359196358487889835761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38569572797572325259890507 57854359196358487889835761)
                  ·
                    refine ⟨43390769397268865917376821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57854359196358487889835761 43390769397268865917376821)
                    ·
                      refine ⟨4067884630993956179754077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43390769397268865917376821 4067884630993956179754077)
                      ·
                        rfl

theorem cell23_7922177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_7922177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922177 prefixEnd_7922177 := by exact prefixLift 7922177
  have htrace : WordTrace (prefixWord ++ tailWord_7922177) baseStart_7922177 baseEnd_7922177 := by
    simpa [prefixWord, tailWord_7922177, baseEnd_7922177] using wordTrace_append hprefix tailTrace_7922177
  have hstable : (prefixWord ++ tailWord_7922177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922177).length < 2 ^ (prefixWord ++ tailWord_7922177).sum := by decide
  have hdescent : baseEnd_7922177 < baseStart_7922177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922182 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7922182 : Nat := 118140960795 + 7922182 * 2 ^ 59
def prefixEnd_7922182 : Nat := 4983230072969 + 3 ^ 40 * 7922182 * 2
def baseEnd_7922182 : Nat := 4067887198397228660191555

theorem tailTrace_7922182 : CollatzResearch.WordTrace tailWord_7922182 prefixEnd_7922182 4067887198397228660191555 := by
  unfold tailWord_7922182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9029553605790471556650025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192630476923530059875200533 9029553605790471556650025)
  ·
    refine ⟨6772165204342853667487519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9029553605790471556650025 6772165204342853667487519)
    ·
      refine ⟨10158247806514280501231279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6772165204342853667487519 10158247806514280501231279)
      ·
        refine ⟨15237371709771420751846919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10158247806514280501231279 15237371709771420751846919)
        ·
          refine ⟨22856057564657131127770379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15237371709771420751846919 22856057564657131127770379)
          ·
            refine ⟨34284086346985696691655569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22856057564657131127770379 34284086346985696691655569)
            ·
              refine ⟨25713064760239272518741677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34284086346985696691655569 25713064760239272518741677)
              ·
                refine ⟨9642399285089727194528129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25713064760239272518741677 9642399285089727194528129)
                ·
                  refine ⟨7231799463817295395896097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9642399285089727194528129 7231799463817295395896097)
                  ·
                    refine ⟨5423849597862971546922073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7231799463817295395896097 5423849597862971546922073)
                    ·
                      refine ⟨4067887198397228660191555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423849597862971546922073 4067887198397228660191555)
                      ·
                        rfl

theorem cell23_7922182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7922182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922182 prefixEnd_7922182 := by exact prefixLift 7922182
  have htrace : WordTrace (prefixWord ++ tailWord_7922182) baseStart_7922182 baseEnd_7922182 := by
    simpa [prefixWord, tailWord_7922182, baseEnd_7922182] using wordTrace_append hprefix tailTrace_7922182
  have hstable : (prefixWord ++ tailWord_7922182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922182).length < 2 ^ (prefixWord ++ tailWord_7922182).sum := by decide
  have hdescent : baseEnd_7922182 < baseStart_7922182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922204 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_7922204 : Nat := 118140960795 + 7922204 * 2 ^ 59
def prefixEnd_7922204 : Nat := 4983230072969 + 3 ^ 40 * 7922204 * 2
def baseEnd_7922204 : Nat := 4067898494971627574116453

theorem tailTrace_7922204 : CollatzResearch.WordTrace tailWord_7922204 prefixEnd_7922204 4067898494971627574116453 := by
  unfold tailWord_7922204
  simp only [CollatzResearch.WordTrace]
  refine ⟨144473258895607693785050833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192631011860810258380067777 144473258895607693785050833)
  ·
    refine ⟨108354944171705770338788125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144473258895607693785050833 108354944171705770338788125)
    ·
      refine ⟨40633104064389663877045547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108354944171705770338788125 40633104064389663877045547)
      ·
        refine ⟨60949656096584495815568321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40633104064389663877045547 60949656096584495815568321)
        ·
          refine ⟨45712242072438371861676241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60949656096584495815568321 45712242072438371861676241)
          ·
            refine ⟨34284181554328778896257181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45712242072438371861676241 34284181554328778896257181)
            ·
              refine ⟨12856568082873292086096443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34284181554328778896257181 12856568082873292086096443)
              ·
                refine ⟨19284852124309938129144665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12856568082873292086096443 19284852124309938129144665)
                ·
                  refine ⟨14463639093232453596858499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19284852124309938129144665 14463639093232453596858499)
                  ·
                    refine ⟨21695458639848680395287749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14463639093232453596858499 21695458639848680395287749)
                    ·
                      refine ⟨4067898494971627574116453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21695458639848680395287749 4067898494971627574116453)
                      ·
                        rfl

theorem cell23_7922204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_7922204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922204 prefixEnd_7922204 := by exact prefixLift 7922204
  have htrace : WordTrace (prefixWord ++ tailWord_7922204) baseStart_7922204 baseEnd_7922204 := by
    simpa [prefixWord, tailWord_7922204, baseEnd_7922204] using wordTrace_append hprefix tailTrace_7922204
  have hstable : (prefixWord ++ tailWord_7922204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922204).length < 2 ^ (prefixWord ++ tailWord_7922204).sum := by decide
  have hdescent : baseEnd_7922204 < baseStart_7922204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922264 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 1, 5, 2]
def baseStart_7922264 : Nat := 118140960795 + 7922264 * 2 ^ 59
def prefixEnd_7922264 : Nat := 4983230072969 + 3 ^ 40 * 7922264 * 2
def baseEnd_7922264 : Nat := 4067929303810897339366177

theorem tailTrace_7922264 : CollatzResearch.WordTrace tailWord_7922264 prefixEnd_7922264 4067929303810897339366177 := by
  unfold tailWord_7922264
  simp only [CollatzResearch.WordTrace]
  refine ⟨144474353085499008908642923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192632470780665345211523897 144474353085499008908642923)
  ·
    refine ⟨216711529628248513362964385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144474353085499008908642923 216711529628248513362964385)
    ·
      refine ⟨162533647221186385022223289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216711529628248513362964385 162533647221186385022223289)
      ·
        refine ⟨121900235415889788766667467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162533647221186385022223289 121900235415889788766667467)
        ·
          refine ⟨182850353123834683150001201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121900235415889788766667467 182850353123834683150001201)
          ·
            refine ⟨137137764842876012362500901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182850353123834683150001201 137137764842876012362500901)
            ·
              refine ⟨25713330908039252317968919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137137764842876012362500901 25713330908039252317968919)
              ·
                refine ⟨38569996362058878476953379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25713330908039252317968919 38569996362058878476953379)
                ·
                  refine ⟨57854994543088317715430069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38569996362058878476953379 57854994543088317715430069)
                  ·
                    refine ⟨5423905738414529785821569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57854994543088317715430069 5423905738414529785821569)
                    ·
                      refine ⟨4067929303810897339366177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423905738414529785821569 4067929303810897339366177)
                      ·
                        rfl

theorem cell23_7922264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_7922264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922264 prefixEnd_7922264 := by exact prefixLift 7922264
  have htrace : WordTrace (prefixWord ++ tailWord_7922264) baseStart_7922264 baseEnd_7922264 := by
    simpa [prefixWord, tailWord_7922264, baseEnd_7922264] using wordTrace_append hprefix tailTrace_7922264
  have hstable : (prefixWord ++ tailWord_7922264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922264).length < 2 ^ (prefixWord ++ tailWord_7922264).sum := by decide
  have hdescent : baseEnd_7922264 < baseStart_7922264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922288 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 3, 1, 3]
def baseStart_7922288 : Nat := 118140960795 + 7922288 * 2 ^ 59
def prefixEnd_7922288 : Nat := 4983230072969 + 3 ^ 40 * 7922288 * 2
def baseEnd_7922288 : Nat := 4067941627346605245466067

theorem tailTrace_7922288 : CollatzResearch.WordTrace tailWord_7922288 prefixEnd_7922288 4067941627346605245466067 := by
  unfold tailWord_7922288
  simp only [CollatzResearch.WordTrace]
  refine ⟨144474790761455534958079759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192633054348607379944106345 144474790761455534958079759)
  ·
    refine ⟨216712186142183302437119639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144474790761455534958079759 216712186142183302437119639)
    ·
      refine ⟨325068279213274953655679459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216712186142183302437119639 325068279213274953655679459)
      ·
        refine ⟨487602418819912430483519189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325068279213274953655679459 487602418819912430483519189)
        ·
          refine ⟨11428181691091697589457481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 487602418819912430483519189 11428181691091697589457481)
          ·
            refine ⟨8571136268318773192093111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11428181691091697589457481 8571136268318773192093111)
            ·
              refine ⟨12856704402478159788139667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571136268318773192093111 12856704402478159788139667)
              ·
                refine ⟨19285056603717239682209501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12856704402478159788139667 19285056603717239682209501)
                ·
                  refine ⟨7231896226393964880828563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19285056603717239682209501 7231896226393964880828563)
                  ·
                    refine ⟨10847844339590947321242845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7231896226393964880828563 10847844339590947321242845)
                    ·
                      refine ⟨4067941627346605245466067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10847844339590947321242845 4067941627346605245466067)
                      ·
                        rfl

theorem cell23_7922288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3, 1, 3].length) (baseStart_7922288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922288 prefixEnd_7922288 := by exact prefixLift 7922288
  have htrace : WordTrace (prefixWord ++ tailWord_7922288) baseStart_7922288 baseEnd_7922288 := by
    simpa [prefixWord, tailWord_7922288, baseEnd_7922288] using wordTrace_append hprefix tailTrace_7922288
  have hstable : (prefixWord ++ tailWord_7922288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922288).length < 2 ^ (prefixWord ++ tailWord_7922288).sum := by decide
  have hdescent : baseEnd_7922288 < baseStart_7922288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922307 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 6]
def baseStart_7922307 : Nat := 118140960795 + 7922307 * 2 ^ 59
def prefixEnd_7922307 : Nat := 4983230072969 + 3 ^ 40 * 7922307 * 2
def baseEnd_7922307 : Nat := 4067951383479040671128479

theorem tailTrace_7922307 : CollatzResearch.WordTrace tailWord_7922307 prefixEnd_7922307 4067951383479040671128479 := by
  unfold tailWord_7922307
  simp only [CollatzResearch.WordTrace]
  refine ⟨288950274509842236161101175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192633516339894824107400783 288950274509842236161101175)
  ·
    refine ⟨433425411764763354241651763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288950274509842236161101175 433425411764763354241651763)
    ·
      refine ⟨650138117647145031362477645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433425411764763354241651763 650138117647145031362477645)
      ·
        refine ⟨243801794117679386760929117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 650138117647145031362477645 243801794117679386760929117)
        ·
          refine ⟨91425672794129770035348419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243801794117679386760929117 91425672794129770035348419)
          ·
            refine ⟨137138509191194655053022629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91425672794129770035348419 137138509191194655053022629)
            ·
              refine ⟨25713470473348997822441743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137138509191194655053022629 25713470473348997822441743)
              ·
                refine ⟨38570205710023496733662615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25713470473348997822441743 38570205710023496733662615)
                ·
                  refine ⟨57855308565035245100493923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38570205710023496733662615 57855308565035245100493923)
                  ·
                    refine ⟨86782962847552867650740885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57855308565035245100493923 86782962847552867650740885)
                    ·
                      refine ⟨4067951383479040671128479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86782962847552867650740885 4067951383479040671128479)
                      ·
                        rfl

theorem cell23_7922307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_7922307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922307 prefixEnd_7922307 := by exact prefixLift 7922307
  have htrace : WordTrace (prefixWord ++ tailWord_7922307) baseStart_7922307 baseEnd_7922307 := by
    simpa [prefixWord, tailWord_7922307, baseEnd_7922307] using wordTrace_append hprefix tailTrace_7922307
  have hstable : (prefixWord ++ tailWord_7922307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922307).length < 2 ^ (prefixWord ++ tailWord_7922307).sum := by decide
  have hdescent : baseEnd_7922307 < baseStart_7922307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922311 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 5, 2, 2]
def baseStart_7922311 : Nat := 118140960795 + 7922311 * 2 ^ 59
def prefixEnd_7922311 : Nat := 4983230072969 + 3 ^ 40 * 7922311 * 2
def baseEnd_7922311 : Nat := 4067953437401658655478461

theorem tailTrace_7922311 : CollatzResearch.WordTrace tailWord_7922311 prefixEnd_7922311 4067953437401658655478461 := by
  unfold tailWord_7922311
  simp only [CollatzResearch.WordTrace]
  refine ⟨288950420401827744844246787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192633613601218496562831191 288950420401827744844246787)
  ·
    refine ⟨433425630602741617266370181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288950420401827744844246787 433425630602741617266370181)
    ·
      refine ⟨81267305738014053237444409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433425630602741617266370181 81267305738014053237444409)
      ·
        refine ⟨60950479303510539928083307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81267305738014053237444409 60950479303510539928083307)
        ·
          refine ⟨91425718955265809892124961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60950479303510539928083307 91425718955265809892124961)
          ·
            refine ⟨68569289216449357419093721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91425718955265809892124961 68569289216449357419093721)
            ·
              refine ⟨51426966912337018064320291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68569289216449357419093721 51426966912337018064320291)
              ·
                refine ⟨77140450368505527096480437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51426966912337018064320291 77140450368505527096480437)
                ·
                  refine ⟨7231917222047393165295041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77140450368505527096480437 7231917222047393165295041)
                  ·
                    refine ⟨5423937916535544873971281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7231917222047393165295041 5423937916535544873971281)
                    ·
                      refine ⟨4067953437401658655478461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423937916535544873971281 4067953437401658655478461)
                      ·
                        rfl

theorem cell23_7922311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_7922311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922311 prefixEnd_7922311 := by exact prefixLift 7922311
  have htrace : WordTrace (prefixWord ++ tailWord_7922311) baseStart_7922311 baseEnd_7922311 := by
    simpa [prefixWord, tailWord_7922311, baseEnd_7922311] using wordTrace_append hprefix tailTrace_7922311
  have hstable : (prefixWord ++ tailWord_7922311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922311).length < 2 ^ (prefixWord ++ tailWord_7922311).sum := by decide
  have hdescent : baseEnd_7922311 < baseStart_7922311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922384 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 2, 8, 2]
def baseStart_7922384 : Nat := 118140960795 + 7922384 * 2 ^ 59
def prefixEnd_7922384 : Nat := 4983230072969 + 3 ^ 40 * 7922384 * 2
def baseEnd_7922384 : Nat := 4067990921489436869865625

theorem tailTrace_7922384 : CollatzResearch.WordTrace tailWord_7922384 prefixEnd_7922384 4067990921489436869865625 := by
  unfold tailWord_7922384
  simp only [CollatzResearch.WordTrace]
  refine ⟨144476541465281639155827103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192635388620375518874436137 144476541465281639155827103)
  ·
    refine ⟨216714812197922458733740655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144476541465281639155827103 216714812197922458733740655)
    ·
      refine ⟨325072218296883688100610983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216714812197922458733740655 325072218296883688100610983)
      ·
        refine ⟨487608327445325532150916475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325072218296883688100610983 487608327445325532150916475)
        ·
          refine ⟨731412491167988298226374713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487608327445325532150916475 731412491167988298226374713)
          ·
            refine ⟨548559368375991223669781035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731412491167988298226374713 548559368375991223669781035)
            ·
              refine ⟨822839052563986835504671553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548559368375991223669781035 822839052563986835504671553)
              ·
                refine ⟨617129289422990126628503665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822839052563986835504671553 617129289422990126628503665)
                ·
                  refine ⟨462846967067242594971377749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617129289422990126628503665 462846967067242594971377749)
                  ·
                    refine ⟨5423987895319249159820833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 462846967067242594971377749 5423987895319249159820833)
                    ·
                      refine ⟨4067990921489436869865625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5423987895319249159820833 4067990921489436869865625)
                      ·
                        rfl

theorem cell23_7922384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 8, 2].length) (baseStart_7922384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922384 prefixEnd_7922384 := by exact prefixLift 7922384
  have htrace : WordTrace (prefixWord ++ tailWord_7922384) baseStart_7922384 baseEnd_7922384 := by
    simpa [prefixWord, tailWord_7922384, baseEnd_7922384] using wordTrace_append hprefix tailTrace_7922384
  have hstable : (prefixWord ++ tailWord_7922384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922384).length < 2 ^ (prefixWord ++ tailWord_7922384).sum := by decide
  have hdescent : baseEnd_7922384 < baseStart_7922384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922418 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 1, 4, 2]
def baseStart_7922418 : Nat := 118140960795 + 7922418 * 2 ^ 59
def prefixEnd_7922418 : Nat := 4983230072969 + 3 ^ 40 * 7922418 * 2
def baseEnd_7922418 : Nat := 4068008379831689736840469

theorem tailTrace_7922418 : CollatzResearch.WordTrace tailWord_7922418 prefixEnd_7922418 4068008379831689736840469 := by
  unfold tailWord_7922418
  simp only [CollatzResearch.WordTrace]
  refine ⟨72238580753110025529597977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192636215341626734745594605 72238580753110025529597977)
  ·
    refine ⟨54178935564832519147198483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72238580753110025529597977 54178935564832519147198483)
    ·
      refine ⟨81268403347248778720797725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54178935564832519147198483 81268403347248778720797725)
      ·
        refine ⟨30475651255218292020299147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81268403347248778720797725 30475651255218292020299147)
        ·
          refine ⟨45713476882827438030448721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30475651255218292020299147 45713476882827438030448721)
          ·
            refine ⟨34285107662120578522836541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45713476882827438030448721 34285107662120578522836541)
            ·
              refine ⟨12856915373295216946063703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34285107662120578522836541 12856915373295216946063703)
              ·
                refine ⟨19285373059942825419095555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12856915373295216946063703 19285373059942825419095555)
                ·
                  refine ⟨28928059589914238128643333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19285373059942825419095555 28928059589914238128643333)
                  ·
                    refine ⟨5424011173108919649120625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28928059589914238128643333 5424011173108919649120625)
                    ·
                      refine ⟨4068008379831689736840469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5424011173108919649120625 4068008379831689736840469)
                      ·
                        rfl

theorem cell23_7922418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_7922418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922418 prefixEnd_7922418 := by exact prefixLift 7922418
  have htrace : WordTrace (prefixWord ++ tailWord_7922418) baseStart_7922418 baseEnd_7922418 := by
    simpa [prefixWord, tailWord_7922418, baseEnd_7922418] using wordTrace_append hprefix tailTrace_7922418
  have hstable : (prefixWord ++ tailWord_7922418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922418).length < 2 ^ (prefixWord ++ tailWord_7922418).sum := by decide
  have hdescent : baseEnd_7922418 < baseStart_7922418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922427 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 6]
def baseStart_7922427 : Nat := 118140960795 + 7922427 * 2 ^ 59
def prefixEnd_7922427 : Nat := 4983230072969 + 3 ^ 40 * 7922427 * 2
def baseEnd_7922427 : Nat := 4068013001157580201627927

theorem tailTrace_7922427 : CollatzResearch.WordTrace tailWord_7922427 prefixEnd_7922427 4068013001157580201627927 := by
  unfold tailWord_7922427
  simp only [CollatzResearch.WordTrace]
  refine ⟨288954651269407496655469535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192636434179604997770313023 288954651269407496655469535)
  ·
    refine ⟨433431976904111244983204303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288954651269407496655469535 433431976904111244983204303)
    ·
      refine ⟨650147965356166867474806455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433431976904111244983204303 650147965356166867474806455)
      ·
        refine ⟨975221948034250301212209683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650147965356166867474806455 975221948034250301212209683)
        ·
          refine ⟨1462832922051375451818314525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975221948034250301212209683 1462832922051375451818314525)
          ·
            refine ⟨548562345769265794431867947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1462832922051375451818314525 548562345769265794431867947)
            ·
              refine ⟨822843518653898691647801921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548562345769265794431867947 822843518653898691647801921)
              ·
                refine ⟨617132638990424018735851441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822843518653898691647801921 617132638990424018735851441)
                ·
                  refine ⟨462849479242818014051888581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617132638990424018735851441 462849479242818014051888581)
                  ·
                    refine ⟨86784277358028377634729109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 462849479242818014051888581 86784277358028377634729109)
                    ·
                      refine ⟨4068013001157580201627927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86784277358028377634729109 4068013001157580201627927)
                      ·
                        rfl

theorem cell23_7922427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_7922427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922427 prefixEnd_7922427 := by exact prefixLift 7922427
  have htrace : WordTrace (prefixWord ++ tailWord_7922427) baseStart_7922427 baseEnd_7922427 := by
    simpa [prefixWord, tailWord_7922427, baseEnd_7922427] using wordTrace_append hprefix tailTrace_7922427
  have hstable : (prefixWord ++ tailWord_7922427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922427).length < 2 ^ (prefixWord ++ tailWord_7922427).sum := by decide
  have hdescent : baseEnd_7922427 < baseStart_7922427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922441 : List Nat := [1, 2, 1, 1, 3, 2, 5, 3, 5]
def baseStart_7922441 : Nat := 118140960795 + 7922441 * 2 ^ 59
def prefixEnd_7922441 : Nat := 4983230072969 + 3 ^ 40 * 7922441 * 2
def baseEnd_7922441 : Nat := 452002243320749238539207

theorem tailTrace_7922441 : CollatzResearch.WordTrace tailWord_7922441 prefixEnd_7922441 452002243320749238539207 := by
  unfold tailWord_7922441
  simp only [CollatzResearch.WordTrace]
  refine ⟨288955161891356777046479177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192636774594237851364319451 288955161891356777046479177)
  ·
    refine ⟨216716371418517582784859383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288955161891356777046479177 216716371418517582784859383)
    ·
      refine ⟨325074557127776374177289075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216716371418517582784859383 325074557127776374177289075)
      ·
        refine ⟨487611835691664561265933613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325074557127776374177289075 487611835691664561265933613)
        ·
          refine ⟨182854438384374210474725105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487611835691664561265933613 182854438384374210474725105)
          ·
            refine ⟨137140828788280657856043829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182854438384374210474725105 137140828788280657856043829)
            ·
              refine ⟨12856952698901311674004109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137140828788280657856043829 12856952698901311674004109)
              ·
                refine ⟨4821357262087991877751541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12856952698901311674004109 4821357262087991877751541)
                ·
                  refine ⟨452002243320749238539207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4821357262087991877751541 452002243320749238539207)
                  ·
                    rfl

theorem cell23_7922441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 5].length) (baseStart_7922441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922441 prefixEnd_7922441 := by exact prefixLift 7922441
  have htrace : WordTrace (prefixWord ++ tailWord_7922441) baseStart_7922441 baseEnd_7922441 := by
    simpa [prefixWord, tailWord_7922441, baseEnd_7922441] using wordTrace_append hprefix tailTrace_7922441
  have hstable : (prefixWord ++ tailWord_7922441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922441).length < 2 ^ (prefixWord ++ tailWord_7922441).sum := by decide
  have hdescent : baseEnd_7922441 < baseStart_7922441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922458 : List Nat := [3, 1, 1, 3, 2, 1, 5, 2, 5]
def baseStart_7922458 : Nat := 118140960795 + 7922458 * 2 ^ 59
def prefixEnd_7922458 : Nat := 4983230072969 + 3 ^ 40 * 7922458 * 2
def baseEnd_7922458 : Nat := 452003213228652175593365

theorem tailTrace_7922458 : CollatzResearch.WordTrace tailWord_7922458 prefixEnd_7922458 452003213228652175593365 := by
  unfold tailWord_7922458
  simp only [CollatzResearch.WordTrace]
  refine ⟨72238945483073797237462007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192637187954863459299898685 72238945483073797237462007)
  ·
    refine ⟨108358418224610695856193011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72238945483073797237462007 108358418224610695856193011)
    ·
      refine ⟨162537627336916043784289517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108358418224610695856193011 162537627336916043784289517)
      ·
        refine ⟨60951610251343516419108569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162537627336916043784289517 60951610251343516419108569)
        ·
          refine ⟨45713707688507637314331427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60951610251343516419108569 45713707688507637314331427)
          ·
            refine ⟨68570561532761455971497141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45713707688507637314331427 68570561532761455971497141)
            ·
              refine ⟨6428490143696386497327857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68570561532761455971497141 6428490143696386497327857)
              ·
                refine ⟨4821367607772289872995893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6428490143696386497327857 4821367607772289872995893)
                ·
                  refine ⟨452003213228652175593365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4821367607772289872995893 452003213228652175593365)
                  ·
                    rfl

theorem cell23_7922458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_7922458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922458 prefixEnd_7922458 := by exact prefixLift 7922458
  have htrace : WordTrace (prefixWord ++ tailWord_7922458) baseStart_7922458 baseEnd_7922458 := by
    simpa [prefixWord, tailWord_7922458, baseEnd_7922458] using wordTrace_append hprefix tailTrace_7922458
  have hstable : (prefixWord ++ tailWord_7922458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922458).length < 2 ^ (prefixWord ++ tailWord_7922458).sum := by decide
  have hdescent : baseEnd_7922458 < baseStart_7922458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922464 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_7922464 : Nat := 118140960795 + 7922464 * 2 ^ 59
def prefixEnd_7922464 : Nat := 4983230072969 + 3 ^ 40 * 7922464 * 2
def baseEnd_7922464 : Nat := 4068031999941796556865257

theorem tailTrace_7922464 : CollatzResearch.WordTrace tailWord_7922464 prefixEnd_7922464 4068031999941796556865257 := by
  unfold tailWord_7922464
  simp only [CollatzResearch.WordTrace]
  refine ⟨144478000385136725987283223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192637333846848967983044297 144478000385136725987283223)
  ·
    refine ⟨216717000577705088980924835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144478000385136725987283223 216717000577705088980924835)
    ·
      refine ⟨325075500866557633471387253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216717000577705088980924835 325075500866557633471387253)
      ·
        refine ⟨30475828206239778137942555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325075500866557633471387253 30475828206239778137942555)
        ·
          refine ⟨45713742309359667206913833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30475828206239778137942555 45713742309359667206913833)
          ·
            refine ⟨34285306732019750405185375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45713742309359667206913833 34285306732019750405185375)
            ·
              refine ⟨51427960098029625607778063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34285306732019750405185375 51427960098029625607778063)
              ·
                refine ⟨77141940147044438411667095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51427960098029625607778063 77141940147044438411667095)
                ·
                  refine ⟨115712910220566657617500643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77141940147044438411667095 115712910220566657617500643)
                  ·
                    refine ⟨173569365330849986426250965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115712910220566657617500643 173569365330849986426250965)
                    ·
                      refine ⟨4068031999941796556865257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173569365330849986426250965 4068031999941796556865257)
                      ·
                        rfl

theorem cell23_7922464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_7922464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922464 prefixEnd_7922464 := by exact prefixLift 7922464
  have htrace : WordTrace (prefixWord ++ tailWord_7922464) baseStart_7922464 baseEnd_7922464 := by
    simpa [prefixWord, tailWord_7922464, baseEnd_7922464] using wordTrace_append hprefix tailTrace_7922464
  have hstable : (prefixWord ++ tailWord_7922464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922464).length < 2 ^ (prefixWord ++ tailWord_7922464).sum := by decide
  have hdescent : baseEnd_7922464 < baseStart_7922464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922504 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_7922504 : Nat := 118140960795 + 7922504 * 2 ^ 59
def prefixEnd_7922504 : Nat := 4983230072969 + 3 ^ 40 * 7922504 * 2
def baseEnd_7922504 : Nat := 4068052539167976400365073

theorem tailTrace_7922504 : CollatzResearch.WordTrace tailWord_7922504 prefixEnd_7922504 4068052539167976400365073 := by
  unfold tailWord_7922504
  simp only [CollatzResearch.WordTrace]
  refine ⟨144478729845064269403011283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192638306460085692537348377 144478729845064269403011283)
  ·
    refine ⟨216718094767596404104516925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144478729845064269403011283 216718094767596404104516925)
    ·
      refine ⟨81269285537848651539193847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216718094767596404104516925 81269285537848651539193847)
      ·
        refine ⟨121903928306772977308790771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81269285537848651539193847 121903928306772977308790771)
        ·
          refine ⟨182855892460159465963186157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121903928306772977308790771 182855892460159465963186157)
          ·
            refine ⟨68570959672559799736194809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182855892460159465963186157 68570959672559799736194809)
            ·
              refine ⟨51428219754419849802146107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68570959672559799736194809 51428219754419849802146107)
              ·
                refine ⟨77142329631629774703219161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51428219754419849802146107 77142329631629774703219161)
                ·
                  refine ⟨57856747223722331027414371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77142329631629774703219161 57856747223722331027414371)
                  ·
                    refine ⟨86785120835583496541121557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57856747223722331027414371 86785120835583496541121557)
                    ·
                      refine ⟨4068052539167976400365073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86785120835583496541121557 4068052539167976400365073)
                      ·
                        rfl

theorem cell23_7922504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_7922504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922504 prefixEnd_7922504 := by exact prefixLift 7922504
  have htrace : WordTrace (prefixWord ++ tailWord_7922504) baseStart_7922504 baseEnd_7922504 := by
    simpa [prefixWord, tailWord_7922504, baseEnd_7922504] using wordTrace_append hprefix tailTrace_7922504
  have hstable : (prefixWord ++ tailWord_7922504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922504).length < 2 ^ (prefixWord ++ tailWord_7922504).sum := by decide
  have hdescent : baseEnd_7922504 < baseStart_7922504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922509 : List Nat := [1, 6, 1, 2, 3, 1, 2, 2, 5]
def baseStart_7922509 : Nat := 118140960795 + 7922509 * 2 ^ 59
def prefixEnd_7922509 : Nat := 4983230072969 + 3 ^ 40 * 7922509 * 2
def baseEnd_7922509 : Nat := 452006122952360986755839

theorem tailTrace_7922509 : CollatzResearch.WordTrace tailWord_7922509 prefixEnd_7922509 452006122952360986755839 := by
  unfold tailWord_7922509
  simp only [CollatzResearch.WordTrace]
  refine ⟨288957642055110424659954581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192638428036740283106636387 288957642055110424659954581)
  ·
    refine ⟨13544889471333301155935371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 288957642055110424659954581 13544889471333301155935371)
    ·
      refine ⟨20317334206999951733903057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13544889471333301155935371 20317334206999951733903057)
      ·
        refine ⟨15238000655249963800427293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20317334206999951733903057 15238000655249963800427293)
        ·
          refine ⟨5714250245718736425160235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15238000655249963800427293 5714250245718736425160235)
          ·
            refine ⟨8571375368578104637740353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5714250245718736425160235 8571375368578104637740353)
            ·
              refine ⟨6428531526433578478305265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8571375368578104637740353 6428531526433578478305265)
              ·
                refine ⟨4821398644825183858728949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6428531526433578478305265 4821398644825183858728949)
                ·
                  refine ⟨452006122952360986755839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4821398644825183858728949 452006122952360986755839)
                  ·
                    rfl

theorem cell23_7922509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_7922509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922509 prefixEnd_7922509 := by exact prefixLift 7922509
  have htrace : WordTrace (prefixWord ++ tailWord_7922509) baseStart_7922509 baseEnd_7922509 := by
    simpa [prefixWord, tailWord_7922509, baseEnd_7922509] using wordTrace_append hprefix tailTrace_7922509
  have hstable : (prefixWord ++ tailWord_7922509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922509).length < 2 ^ (prefixWord ++ tailWord_7922509).sum := by decide
  have hdescent : baseEnd_7922509 < baseStart_7922509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922531 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 6]
def baseStart_7922531 : Nat := 118140960795 + 7922531 * 2 ^ 59
def prefixEnd_7922531 : Nat := 4983230072969 + 3 ^ 40 * 7922531 * 2
def baseEnd_7922531 : Nat := 452007378127294199414161

theorem tailTrace_7922531 : CollatzResearch.WordTrace tailWord_7922531 prefixEnd_7922531 452007378127294199414161 := by
  unfold tailWord_7922531
  simp only [CollatzResearch.WordTrace]
  refine ⟨288958444461030722417255447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192638962974020481611503631 288958444461030722417255447)
  ·
    refine ⟨433437666691546083625883171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288958444461030722417255447 433437666691546083625883171)
    ·
      refine ⟨650156500037319125438824757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433437666691546083625883171 650156500037319125438824757)
      ·
        refine ⟨60952171878498668009889821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 650156500037319125438824757 60952171878498668009889821)
        ·
          refine ⟨22857064454437000503708683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60952171878498668009889821 22857064454437000503708683)
          ·
            refine ⟨34285596681655500755563025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22857064454437000503708683 34285596681655500755563025)
            ·
              refine ⟨25714197511241625566672269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34285596681655500755563025 25714197511241625566672269)
              ·
                refine ⟨9642824066715609587502101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25714197511241625566672269 9642824066715609587502101)
                ·
                  refine ⟨452007378127294199414161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9642824066715609587502101 452007378127294199414161)
                  ·
                    rfl

theorem cell23_7922531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 6].length) (baseStart_7922531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922531 prefixEnd_7922531 := by exact prefixLift 7922531
  have htrace : WordTrace (prefixWord ++ tailWord_7922531) baseStart_7922531 baseEnd_7922531 := by
    simpa [prefixWord, tailWord_7922531, baseEnd_7922531] using wordTrace_append hprefix tailTrace_7922531
  have hstable : (prefixWord ++ tailWord_7922531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922531).length < 2 ^ (prefixWord ++ tailWord_7922531).sum := by decide
  have hdescent : baseEnd_7922531 < baseStart_7922531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922542 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_7922542 : Nat := 118140960795 + 7922542 * 2 ^ 59
def prefixEnd_7922542 : Nat := 4983230072969 + 3 ^ 40 * 7922542 * 2
def baseEnd_7922542 : Nat := 4068072051432847251689899

theorem tailTrace_7922542 : CollatzResearch.WordTrace tailWord_7922542 prefixEnd_7922542 4068072051432847251689899 := by
  unfold tailWord_7922542
  simp only [CollatzResearch.WordTrace]
  refine ⟨36119855707998858911988235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192639230442660580863937253 36119855707998858911988235)
  ·
    refine ⟨54179783561998288367982353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36119855707998858911988235 54179783561998288367982353)
    ·
      refine ⟨40634837671498716275986765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54179783561998288367982353 40634837671498716275986765)
      ·
        refine ⟨15238064126812018603495037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40634837671498716275986765 15238064126812018603495037)
        ·
          refine ⟨5714274047554506976310639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15238064126812018603495037 5714274047554506976310639)
          ·
            refine ⟨8571411071331760464465959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5714274047554506976310639 8571411071331760464465959)
            ·
              refine ⟨12857116606997640696698939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571411071331760464465959 12857116606997640696698939)
              ·
                refine ⟨19285674910496461045048409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12857116606997640696698939 19285674910496461045048409)
                ·
                  refine ⟨14464256182872345783786307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19285674910496461045048409 14464256182872345783786307)
                  ·
                    refine ⟨21696384274308518675679461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14464256182872345783786307 21696384274308518675679461)
                    ·
                      refine ⟨4068072051432847251689899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21696384274308518675679461 4068072051432847251689899)
                      ·
                        rfl

theorem cell23_7922542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_7922542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922542 prefixEnd_7922542 := by exact prefixLift 7922542
  have htrace : WordTrace (prefixWord ++ tailWord_7922542) baseStart_7922542 baseEnd_7922542 := by
    simpa [prefixWord, tailWord_7922542, baseEnd_7922542] using wordTrace_append hprefix tailTrace_7922542
  have hstable : (prefixWord ++ tailWord_7922542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922542).length < 2 ^ (prefixWord ++ tailWord_7922542).sum := by decide
  have hdescent : baseEnd_7922542 < baseStart_7922542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922554 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_7922554 : Nat := 118140960795 + 7922554 * 2 ^ 59
def prefixEnd_7922554 : Nat := 4983230072969 + 3 ^ 40 * 7922554 * 2
def baseEnd_7922554 : Nat := 4068078213200701204739843

theorem tailTrace_7922554 : CollatzResearch.WordTrace tailWord_7922554 prefixEnd_7922554 4068078213200701204739843 := by
  unfold tailWord_7922554
  simp only [CollatzResearch.WordTrace]
  refine ⟨72239820834986849336335679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192639522226631598230228477 72239820834986849336335679)
  ·
    refine ⟨108359731252480274004503519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72239820834986849336335679 108359731252480274004503519)
    ·
      refine ⟨162539596878720411006755279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108359731252480274004503519 162539596878720411006755279)
      ·
        refine ⟨243809395318080616510132919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162539596878720411006755279 243809395318080616510132919)
        ·
          refine ⟨365714092977120924765199379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243809395318080616510132919 365714092977120924765199379)
          ·
            refine ⟨548571139465681387147799069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365714092977120924765199379 548571139465681387147799069)
            ·
              refine ⟨205714177299630520180424651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548571139465681387147799069 205714177299630520180424651)
              ·
                refine ⟨308571265949445780270636977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205714177299630520180424651 308571265949445780270636977)
                ·
                  refine ⟨231428449462084335202977733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308571265949445780270636977 231428449462084335202977733)
                  ·
                    refine ⟨43392834274140812850558325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 231428449462084335202977733 43392834274140812850558325)
                    ·
                      refine ⟨4068078213200701204739843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43392834274140812850558325 4068078213200701204739843)
                      ·
                        rfl

theorem cell23_7922554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_7922554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922554 prefixEnd_7922554 := by exact prefixLift 7922554
  have htrace : WordTrace (prefixWord ++ tailWord_7922554) baseStart_7922554 baseEnd_7922554 := by
    simpa [prefixWord, tailWord_7922554, baseEnd_7922554] using wordTrace_append hprefix tailTrace_7922554
  have hstable : (prefixWord ++ tailWord_7922554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922554).length < 2 ^ (prefixWord ++ tailWord_7922554).sum := by decide
  have hdescent : baseEnd_7922554 < baseStart_7922554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922604 : List Nat := [2, 2, 1, 1, 1, 1, 2, 13]
def baseStart_7922604 : Nat := 118140960795 + 7922604 * 2 ^ 59
def prefixEnd_7922604 : Nat := 4983230072969 + 3 ^ 40 * 7922604 * 2
def baseEnd_7922604 : Nat := 150670514341978741078319

theorem tailTrace_7922604 : CollatzResearch.WordTrace tailWord_7922604 prefixEnd_7922604 150670514341978741078319 := by
  unfold tailWord_7922604
  simp only [CollatzResearch.WordTrace]
  refine ⟨144480553494883127942331433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192640737993177503923108577 144480553494883127942331433)
  ·
    refine ⟨108360415121162345956748575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144480553494883127942331433 108360415121162345956748575)
    ·
      refine ⟨162540622681743518935122863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108360415121162345956748575 162540622681743518935122863)
      ·
        refine ⟨243810934022615278402684295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162540622681743518935122863 243810934022615278402684295)
        ·
          refine ⟨365716401033922917604026443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243810934022615278402684295 365716401033922917604026443)
          ·
            refine ⟨548574601550884376406039665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365716401033922917604026443 548574601550884376406039665)
            ·
              refine ⟨411430951163163282304529749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548574601550884376406039665 411430951163163282304529749)
              ·
                refine ⟨150670514341978741078319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 411430951163163282304529749 150670514341978741078319)
                ·
                  rfl

theorem cell23_7922604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 13].length) (baseStart_7922604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922604 prefixEnd_7922604 := by exact prefixLift 7922604
  have htrace : WordTrace (prefixWord ++ tailWord_7922604) baseStart_7922604 baseEnd_7922604 := by
    simpa [prefixWord, tailWord_7922604, baseEnd_7922604] using wordTrace_append hprefix tailTrace_7922604
  have hstable : (prefixWord ++ tailWord_7922604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922604).length < 2 ^ (prefixWord ++ tailWord_7922604).sum := by decide
  have hdescent : baseEnd_7922604 < baseStart_7922604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922609 : List Nat := [1, 2, 2, 4, 3, 2, 1, 3, 1, 1, 3]
def baseStart_7922609 : Nat := 118140960795 + 7922609 * 2 ^ 59
def prefixEnd_7922609 : Nat := 4983230072969 + 3 ^ 40 * 7922609 * 2
def baseEnd_7922609 : Nat := 4068106454636698489552091

theorem tailTrace_7922609 : CollatzResearch.WordTrace tailWord_7922609 prefixEnd_7922609 4068106454636698489552091 := by
  unfold tailWord_7922609
  simp only [CollatzResearch.WordTrace]
  refine ⟨288961289354748141738594881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192640859569832094492396587 288961289354748141738594881)
  ·
    refine ⟨216720967016061106303946161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288961289354748141738594881 216720967016061106303946161)
    ·
      refine ⟨162540725262045829727959621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216720967016061106303946161 162540725262045829727959621)
      ·
        refine ⟨30476385986633593073992429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162540725262045829727959621 30476385986633593073992429)
        ·
          refine ⟨11428644744987597402747161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30476385986633593073992429 11428644744987597402747161)
          ·
            refine ⟨8571483558740698052060371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11428644744987597402747161 8571483558740698052060371)
            ·
              refine ⟨12857225338111047078090557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571483558740698052060371 12857225338111047078090557)
              ·
                refine ⟨4821459501791642654283959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12857225338111047078090557 4821459501791642654283959)
                ·
                  refine ⟨7232189252687463981425939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821459501791642654283959 7232189252687463981425939)
                  ·
                    refine ⟨10848283879031195972138909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7232189252687463981425939 10848283879031195972138909)
                    ·
                      refine ⟨4068106454636698489552091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10848283879031195972138909 4068106454636698489552091)
                      ·
                        rfl

theorem cell23_7922609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_7922609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922609 prefixEnd_7922609 := by exact prefixLift 7922609
  have htrace : WordTrace (prefixWord ++ tailWord_7922609) baseStart_7922609 baseEnd_7922609 := by
    simpa [prefixWord, tailWord_7922609, baseEnd_7922609] using wordTrace_append hprefix tailTrace_7922609
  have hstable : (prefixWord ++ tailWord_7922609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922609).length < 2 ^ (prefixWord ++ tailWord_7922609).sum := by decide
  have hdescent : baseEnd_7922609 < baseStart_7922609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922618 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3]
def baseStart_7922618 : Nat := 118140960795 + 7922618 * 2 ^ 59
def prefixEnd_7922618 : Nat := 4983230072969 + 3 ^ 40 * 7922618 * 2
def baseEnd_7922618 : Nat := 4068111075962588954339549

theorem tailTrace_7922618 : CollatzResearch.WordTrace tailWord_7922618 prefixEnd_7922618 4068111075962588954339549 := by
  unfold tailWord_7922618
  simp only [CollatzResearch.WordTrace]
  refine ⟨72240404402928884068918127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192641078407810357517115005 72240404402928884068918127)
  ·
    refine ⟨108360606604393326103377191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72240404402928884068918127 108360606604393326103377191)
    ·
      refine ⟨162540909906589989155065787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108360606604393326103377191 162540909906589989155065787)
      ·
        refine ⟨243811364859884983732598681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162540909906589989155065787 243811364859884983732598681)
        ·
          refine ⟨182858523644913737799449011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243811364859884983732598681 182858523644913737799449011)
          ·
            refine ⟨274287785467370606699173517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182858523644913737799449011 274287785467370606699173517)
            ·
              refine ⟨102857919550263977512190069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274287785467370606699173517 102857919550263977512190069)
              ·
                refine ⟨9642929957837247891767819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102857919550263977512190069 9642929957837247891767819)
                ·
                  refine ⟨14464394936755871837651729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9642929957837247891767819 14464394936755871837651729)
                  ·
                    refine ⟨10848296202566903878238797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14464394936755871837651729 10848296202566903878238797)
                    ·
                      refine ⟨4068111075962588954339549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10848296202566903878238797 4068111075962588954339549)
                      ·
                        rfl

theorem cell23_7922618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_7922618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922618 prefixEnd_7922618 := by exact prefixLift 7922618
  have htrace : WordTrace (prefixWord ++ tailWord_7922618) baseStart_7922618 baseEnd_7922618 := by
    simpa [prefixWord, tailWord_7922618, baseEnd_7922618] using wordTrace_append hprefix tailTrace_7922618
  have hstable : (prefixWord ++ tailWord_7922618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922618).length < 2 ^ (prefixWord ++ tailWord_7922618).sum := by decide
  have hdescent : baseEnd_7922618 < baseStart_7922618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922642 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_7922642 : Nat := 118140960795 + 7922642 * 2 ^ 59
def prefixEnd_7922642 : Nat := 4983230072969 + 3 ^ 40 * 7922642 * 2
def baseEnd_7922642 : Nat := 1356041133166098953479813

theorem tailTrace_7922642 : CollatzResearch.WordTrace tailWord_7922642 prefixEnd_7922642 1356041133166098953479813 := by
  unfold tailWord_7922642
  simp only [CollatzResearch.WordTrace]
  refine ⟨72240623240907147093636545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192641661975752392249697453 72240623240907147093636545)
  ·
    refine ⟨54180467430680360320227409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72240623240907147093636545 54180467430680360320227409)
    ·
      refine ⟨40635350573010270240170557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54180467430680360320227409 40635350573010270240170557)
      ·
        refine ⟨15238256464878851340063959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40635350573010270240170557 15238256464878851340063959)
        ·
          refine ⟨22857384697318277010095939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15238256464878851340063959 22857384697318277010095939)
          ·
            refine ⟨34286077045977415515143909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22857384697318277010095939 34286077045977415515143909)
            ·
              refine ⟨6428639446120765409089483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34286077045977415515143909 6428639446120765409089483)
              ·
                refine ⟨9642959169181148113634225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428639446120765409089483 9642959169181148113634225)
                ·
                  refine ⟨7232219376885861085225669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9642959169181148113634225 7232219376885861085225669)
                  ·
                    refine ⟨1356041133166098953479813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7232219376885861085225669 1356041133166098953479813)
                    ·
                      rfl

theorem cell23_7922642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_7922642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922642 prefixEnd_7922642 := by exact prefixLift 7922642
  have htrace : WordTrace (prefixWord ++ tailWord_7922642) baseStart_7922642 baseEnd_7922642 := by
    simpa [prefixWord, tailWord_7922642, baseEnd_7922642] using wordTrace_append hprefix tailTrace_7922642
  have hstable : (prefixWord ++ tailWord_7922642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922642).length < 2 ^ (prefixWord ++ tailWord_7922642).sum := by decide
  have hdescent : baseEnd_7922642 < baseStart_7922642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922681 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 2, 6]
def baseStart_7922681 : Nat := 118140960795 + 7922681 * 2 ^ 59
def prefixEnd_7922681 : Nat := 4983230072969 + 3 ^ 40 * 7922681 * 2
def baseEnd_7922681 : Nat := 1356047808414607402617253

theorem tailTrace_7922681 : CollatzResearch.WordTrace tailWord_7922681 prefixEnd_7922681 1356047808414607402617253 := by
  unfold tailWord_7922681
  simp only [CollatzResearch.WordTrace]
  refine ⟨288963915410487298035215897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192642610273658198690143931 288963915410487298035215897)
  ·
    refine ⟨216722936557865473526411923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288963915410487298035215897 216722936557865473526411923)
    ·
      refine ⟨325084404836798210289617885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216722936557865473526411923 325084404836798210289617885)
      ·
        refine ⟨121906651813799328858606707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325084404836798210289617885 121906651813799328858606707)
        ·
          refine ⟨182859977720698993287910061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121906651813799328858606707 182859977720698993287910061)
          ·
            refine ⟨68572491645262122482966273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182859977720698993287910061 68572491645262122482966273)
            ·
              refine ⟨51429368733946591862224705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68572491645262122482966273 51429368733946591862224705)
              ·
                refine ⟨38572026550459943896668529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51429368733946591862224705 38572026550459943896668529)
                ·
                  refine ⟨28929019912844957922501397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38572026550459943896668529 28929019912844957922501397)
                  ·
                    refine ⟨1356047808414607402617253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28929019912844957922501397 1356047808414607402617253)
                    ·
                      rfl

theorem cell23_7922681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_7922681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922681 prefixEnd_7922681 := by exact prefixLift 7922681
  have htrace : WordTrace (prefixWord ++ tailWord_7922681) baseStart_7922681 baseEnd_7922681 := by
    simpa [prefixWord, tailWord_7922681, baseEnd_7922681] using wordTrace_append hprefix tailTrace_7922681
  have hstable : (prefixWord ++ tailWord_7922681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922681).length < 2 ^ (prefixWord ++ tailWord_7922681).sum := by decide
  have hdescent : baseEnd_7922681 < baseStart_7922681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922698 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_7922698 : Nat := 118140960795 + 7922698 * 2 ^ 59
def prefixEnd_7922698 : Nat := 4983230072969 + 3 ^ 40 * 7922698 * 2
def baseEnd_7922698 : Nat := 1356050718138316213779727

theorem tailTrace_7922698 : CollatzResearch.WordTrace tailWord_7922698 prefixEnd_7922698 1356050718138316213779727 := by
  unfold tailWord_7922698
  simp only [CollatzResearch.WordTrace]
  refine ⟨72241133862856427484646187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192643023634283806625723165 72241133862856427484646187)
  ·
    refine ⟨108361700794284641226969281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72241133862856427484646187 108361700794284641226969281)
    ·
      refine ⟨81271275595713480920226961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108361700794284641226969281 81271275595713480920226961)
      ·
        refine ⟨60953456696785110690170221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81271275595713480920226961 60953456696785110690170221)
        ·
          refine ⟨22857546261294416508813833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60953456696785110690170221 22857546261294416508813833)
          ·
            refine ⟨17143159695970812381610375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22857546261294416508813833 17143159695970812381610375)
            ·
              refine ⟨25714739543956218572415563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17143159695970812381610375 25714739543956218572415563)
              ·
                refine ⟨38572109315934327858623345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25714739543956218572415563 38572109315934327858623345)
                ·
                  refine ⟨28929081986950745893967509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38572109315934327858623345 28929081986950745893967509)
                  ·
                    refine ⟨1356050718138316213779727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28929081986950745893967509 1356050718138316213779727)
                    ·
                      rfl

theorem cell23_7922698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_7922698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922698 prefixEnd_7922698 := by exact prefixLift 7922698
  have htrace : WordTrace (prefixWord ++ tailWord_7922698) baseStart_7922698 baseEnd_7922698 := by
    simpa [prefixWord, tailWord_7922698, baseEnd_7922698] using wordTrace_append hprefix tailTrace_7922698
  have hstable : (prefixWord ++ tailWord_7922698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922698).length < 2 ^ (prefixWord ++ tailWord_7922698).sum := by decide
  have hdescent : baseEnd_7922698 < baseStart_7922698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922738 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_7922738 : Nat := 118140960795 + 7922738 * 2 ^ 59
def prefixEnd_7922738 : Nat := 4983230072969 + 3 ^ 40 * 7922738 * 2
def baseEnd_7922738 : Nat := 4068172693641128484838997

theorem tailTrace_7922738 : CollatzResearch.WordTrace tailWord_7922738 prefixEnd_7922738 4068172693641128484838997 := by
  unfold tailWord_7922738
  simp only [CollatzResearch.WordTrace]
  refine ⟨72241498592820199192510217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192643996247520531180027245 72241498592820199192510217)
  ·
    refine ⟨54181123944615149394382663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72241498592820199192510217 54181123944615149394382663)
    ·
      refine ⟨81271685916922724091573995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54181123944615149394382663 81271685916922724091573995)
      ·
        refine ⟨121907528875384086137360993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81271685916922724091573995 121907528875384086137360993)
        ·
          refine ⟨91430646656538064603020745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121907528875384086137360993 91430646656538064603020745)
          ·
            refine ⟨68572984992403548452265559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91430646656538064603020745 68572984992403548452265559)
            ·
              refine ⟨102859477488605322678398339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68572984992403548452265559 102859477488605322678398339)
              ·
                refine ⟨154289216232907984017597509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102859477488605322678398339 154289216232907984017597509)
                ·
                  refine ⟨28929228043670247003299533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154289216232907984017597509 28929228043670247003299533)
                  ·
                    refine ⟨10848460516376342626237325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28929228043670247003299533 10848460516376342626237325)
                    ·
                      refine ⟨4068172693641128484838997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10848460516376342626237325 4068172693641128484838997)
                      ·
                        rfl

theorem cell23_7922738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_7922738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922738 prefixEnd_7922738 := by exact prefixLift 7922738
  have htrace : WordTrace (prefixWord ++ tailWord_7922738) baseStart_7922738 baseEnd_7922738 := by
    simpa [prefixWord, tailWord_7922738, baseEnd_7922738] using wordTrace_append hprefix tailTrace_7922738
  have hstable : (prefixWord ++ tailWord_7922738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922738).length < 2 ^ (prefixWord ++ tailWord_7922738).sum := by decide
  have hdescent : baseEnd_7922738 < baseStart_7922738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922745 : List Nat := [1, 2, 1, 5, 2, 1, 2, 4, 5]
def baseStart_7922745 : Nat := 118140960795 + 7922745 * 2 ^ 59
def prefixEnd_7922745 : Nat := 4983230072969 + 3 ^ 40 * 7922745 * 2
def baseEnd_7922745 : Nat := 452019587556189995272385

theorem tailTrace_7922745 : CollatzResearch.WordTrace tailWord_7922745 prefixEnd_7922745 452019587556189995272385 := by
  unfold tailWord_7922745
  simp only [CollatzResearch.WordTrace]
  refine ⟨288966249682255436965545689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192644166454836957977030459 288966249682255436965545689)
  ·
    refine ⟨216724687261691577724159267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288966249682255436965545689 216724687261691577724159267)
    ·
      refine ⟨325087030892537366586238901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216724687261691577724159267 325087030892537366586238901)
      ·
        refine ⟨30476909146175378117459897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325087030892537366586238901 30476909146175378117459897)
        ·
          refine ⟨22857681859631533588094923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30476909146175378117459897 22857681859631533588094923)
          ·
            refine ⟨34286522789447300382142385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22857681859631533588094923 34286522789447300382142385)
            ·
              refine ⟨25714892092085475286606789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34286522789447300382142385 25714892092085475286606789)
              ·
                refine ⟨4821542267266026616238773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25714892092085475286606789 4821542267266026616238773)
                ·
                  refine ⟨452019587556189995272385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4821542267266026616238773 452019587556189995272385)
                  ·
                    rfl

theorem cell23_7922745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 5].length) (baseStart_7922745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922745 prefixEnd_7922745 := by exact prefixLift 7922745
  have htrace : WordTrace (prefixWord ++ tailWord_7922745) baseStart_7922745 baseEnd_7922745 := by
    simpa [prefixWord, tailWord_7922745, baseEnd_7922745] using wordTrace_append hprefix tailTrace_7922745
  have hstable : (prefixWord ++ tailWord_7922745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922745).length < 2 ^ (prefixWord ++ tailWord_7922745).sum := by decide
  have hdescent : baseEnd_7922745 < baseStart_7922745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922751 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_7922751 : Nat := 118140960795 + 7922751 * 2 ^ 59
def prefixEnd_7922751 : Nat := 4983230072969 + 3 ^ 40 * 7922751 * 2
def baseEnd_7922751 : Nat := 4068179368889636933976437

theorem tailTrace_7922751 : CollatzResearch.WordTrace tailWord_7922751 prefixEnd_7922751 4068179368889636933976437 := by
  unfold tailWord_7922751
  simp only [CollatzResearch.WordTrace]
  refine ⟨288966468520233699990264107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192644312346822466660176071 288966468520233699990264107)
  ·
    refine ⟨433449702780350549985396161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288966468520233699990264107 433449702780350549985396161)
    ·
      refine ⟨325087277085262912489047121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433449702780350549985396161 325087277085262912489047121)
      ·
        refine ⟨243815457813947184366785341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325087277085262912489047121 243815457813947184366785341)
        ·
          refine ⟨91430796680230194137544503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243815457813947184366785341 91430796680230194137544503)
          ·
            refine ⟨137146195020345291206316755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91430796680230194137544503 137146195020345291206316755)
            ·
              refine ⟨205719292530517936809475133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137146195020345291206316755 205719292530517936809475133)
              ·
                refine ⟨77144734698944226303553175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205719292530517936809475133 77144734698944226303553175)
                ·
                  refine ⟨115717102048416339455329763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77144734698944226303553175 115717102048416339455329763)
                  ·
                    refine ⟨173575653072624509182994645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115717102048416339455329763 173575653072624509182994645)
                    ·
                      refine ⟨4068179368889636933976437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173575653072624509182994645 4068179368889636933976437)
                      ·
                        rfl

theorem cell23_7922751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_7922751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922751 prefixEnd_7922751 := by exact prefixLift 7922751
  have htrace : WordTrace (prefixWord ++ tailWord_7922751) baseStart_7922751 baseEnd_7922751 := by
    simpa [prefixWord, tailWord_7922751, baseEnd_7922751] using wordTrace_append hprefix tailTrace_7922751
  have hstable : (prefixWord ++ tailWord_7922751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922751).length < 2 ^ (prefixWord ++ tailWord_7922751).sum := by decide
  have hdescent : baseEnd_7922751 < baseStart_7922751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922792 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 2, 5]
def baseStart_7922792 : Nat := 118140960795 + 7922792 * 2 ^ 59
def prefixEnd_7922792 : Nat := 4983230072969 + 3 ^ 40 * 7922792 * 2
def baseEnd_7922792 : Nat := 1356066807198823757854583

theorem tailTrace_7922792 : CollatzResearch.WordTrace tailWord_7922792 prefixEnd_7922792 1356066807198823757854583 := by
  unfold tailWord_7922792
  simp only [CollatzResearch.WordTrace]
  refine ⟨144483981956542581996253315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192645309275390109328337753 144483981956542581996253315)
  ·
    refine ⟨216725972934813872994379973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144483981956542581996253315 216725972934813872994379973)
    ·
      refine ⟨40636119925277601186446245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216725972934813872994379973 40636119925277601186446245)
      ·
        refine ⟨7619272485989550222458671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40636119925277601186446245 7619272485989550222458671)
        ·
          refine ⟨11428908728984325333688007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7619272485989550222458671 11428908728984325333688007)
          ·
            refine ⟨17143363093476488000532011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11428908728984325333688007 17143363093476488000532011)
            ·
              refine ⟨25715044640214732000798017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17143363093476488000532011 25715044640214732000798017)
              ·
                refine ⟨19286283480161049000598513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25715044640214732000798017 19286283480161049000598513)
                ·
                  refine ⟨14464712610120786750448885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19286283480161049000598513 14464712610120786750448885)
                  ·
                    refine ⟨1356066807198823757854583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14464712610120786750448885 1356066807198823757854583)
                    ·
                      rfl

theorem cell23_7922792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_7922792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922792 prefixEnd_7922792 := by exact prefixLift 7922792
  have htrace : WordTrace (prefixWord ++ tailWord_7922792) baseStart_7922792 baseEnd_7922792 := by
    simpa [prefixWord, tailWord_7922792, baseEnd_7922792] using wordTrace_append hprefix tailTrace_7922792
  have hstable : (prefixWord ++ tailWord_7922792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922792).length < 2 ^ (prefixWord ++ tailWord_7922792).sum := by decide
  have hdescent : baseEnd_7922792 < baseStart_7922792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922828 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 2, 5, 3]
def baseStart_7922828 : Nat := 118140960795 + 7922828 * 2 ^ 59
def prefixEnd_7922828 : Nat := 4983230072969 + 3 ^ 40 * 7922828 * 2
def baseEnd_7922828 : Nat := 4068218906900033132713583

theorem tailTrace_7922828 : CollatzResearch.WordTrace tailWord_7922828 prefixEnd_7922828 4068218906900033132713583 := by
  unfold tailWord_7922828
  simp only [CollatzResearch.WordTrace]
  refine ⟨144484638470477371070408569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192646184627303161427211425 144484638470477371070408569)
  ·
    refine ⟨108363478852858028302806427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144484638470477371070408569 108363478852858028302806427)
    ·
      refine ⟨162545218279287042454209641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108363478852858028302806427 162545218279287042454209641)
      ·
        refine ⟨121908913709465281840657231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162545218279287042454209641 121908913709465281840657231)
        ·
          refine ⟨182863370564197922760985847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121908913709465281840657231 182863370564197922760985847)
          ·
            refine ⟨274295055846296884141478771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182863370564197922760985847 274295055846296884141478771)
            ·
              refine ⟨411442583769445326212218157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274295055846296884141478771 411442583769445326212218157)
              ·
                refine ⟨154290968913541997329581809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411442583769445326212218157 154290968913541997329581809)
                ·
                  refine ⟨115718226685156497997186357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154290968913541997329581809 115718226685156497997186357)
                  ·
                    refine ⟨10848583751733421687236221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115718226685156497997186357 10848583751733421687236221)
                    ·
                      refine ⟨4068218906900033132713583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10848583751733421687236221 4068218906900033132713583)
                      ·
                        rfl

theorem cell23_7922828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_7922828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922828 prefixEnd_7922828 := by exact prefixLift 7922828
  have htrace : WordTrace (prefixWord ++ tailWord_7922828) baseStart_7922828 baseEnd_7922828 := by
    simpa [prefixWord, tailWord_7922828, baseEnd_7922828] using wordTrace_append hprefix tailTrace_7922828
  have hstable : (prefixWord ++ tailWord_7922828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922828).length < 2 ^ (prefixWord ++ tailWord_7922828).sum := by decide
  have hdescent : baseEnd_7922828 < baseStart_7922828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922865 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 3, 5]
def baseStart_7922865 : Nat := 118140960795 + 7922865 * 2 ^ 59
def prefixEnd_7922865 : Nat := 4983230072969 + 3 ^ 40 * 7922865 * 2
def baseEnd_7922865 : Nat := 1356079301894749829316971

theorem tailTrace_7922865 : CollatzResearch.WordTrace tailWord_7922865 prefixEnd_7922865 1356079301894749829316971 := by
  unfold tailWord_7922865
  simp only [CollatzResearch.WordTrace]
  refine ⟨288970626441820697459914049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192647084294547131639942699 288970626441820697459914049)
  ·
    refine ⟨216727969831365523094935537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288970626441820697459914049 216727969831365523094935537)
    ·
      refine ⟨162545977373524142321201653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216727969831365523094935537 162545977373524142321201653)
      ·
        refine ⟨15238685378767888342612655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162545977373524142321201653 15238685378767888342612655)
        ·
          refine ⟨22858028068151832513918983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15238685378767888342612655 22858028068151832513918983)
          ·
            refine ⟨34287042102227748770878475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22858028068151832513918983 34287042102227748770878475)
            ·
              refine ⟨51430563153341623156317713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34287042102227748770878475 51430563153341623156317713)
              ·
                refine ⟨38572922365006217367238285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51430563153341623156317713 38572922365006217367238285)
                ·
                  refine ⟨14464845886877331512714357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38572922365006217367238285 14464845886877331512714357)
                  ·
                    refine ⟨1356079301894749829316971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14464845886877331512714357 1356079301894749829316971)
                    ·
                      rfl

theorem cell23_7922865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_7922865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922865 prefixEnd_7922865 := by exact prefixLift 7922865
  have htrace : WordTrace (prefixWord ++ tailWord_7922865) baseStart_7922865 baseEnd_7922865 := by
    simpa [prefixWord, tailWord_7922865, baseEnd_7922865] using wordTrace_append hprefix tailTrace_7922865
  have hstable : (prefixWord ++ tailWord_7922865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922865).length < 2 ^ (prefixWord ++ tailWord_7922865).sum := by decide
  have hdescent : baseEnd_7922865 < baseStart_7922865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922885 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 4]
def baseStart_7922885 : Nat := 118140960795 + 7922885 * 2 ^ 59
def prefixEnd_7922885 : Nat := 4983230072969 + 3 ^ 40 * 7922885 * 2
def baseEnd_7922885 : Nat := 4068248175297339409700821

theorem tailTrace_7922885 : CollatzResearch.WordTrace tailWord_7922885 prefixEnd_7922885 4068248175297339409700821 := by
  unfold tailWord_7922885
  simp only [CollatzResearch.WordTrace]
  refine ⟨288971355901748240875642109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192647570601165493917094739 288971355901748240875642109)
  ·
    refine ⟨108364258463155590328365791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288971355901748240875642109 108364258463155590328365791)
    ·
      refine ⟨162546387694733385492548687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108364258463155590328365791 162546387694733385492548687)
      ·
        refine ⟨243819581542100078238823031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162546387694733385492548687 243819581542100078238823031)
        ·
          refine ⟨365729372313150117358234547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243819581542100078238823031 365729372313150117358234547)
          ·
            refine ⟨548594058469725176037351821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365729372313150117358234547 548594058469725176037351821)
            ·
              refine ⟨205722771926146941014006933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548594058469725176037351821 205722771926146941014006933)
              ·
                refine ⟨9643254934038137860031575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205722771926146941014006933 9643254934038137860031575)
                ·
                  refine ⟨14464882401057206790047363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9643254934038137860031575 14464882401057206790047363)
                  ·
                    refine ⟨21697323601585810185071045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14464882401057206790047363 21697323601585810185071045)
                    ·
                      refine ⟨4068248175297339409700821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21697323601585810185071045 4068248175297339409700821)
                      ·
                        rfl

theorem cell23_7922885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_7922885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922885 prefixEnd_7922885 := by exact prefixLift 7922885
  have htrace : WordTrace (prefixWord ++ tailWord_7922885) baseStart_7922885 baseEnd_7922885 := by
    simpa [prefixWord, tailWord_7922885, baseEnd_7922885] using wordTrace_append hprefix tailTrace_7922885
  have hstable : (prefixWord ++ tailWord_7922885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922885).length < 2 ^ (prefixWord ++ tailWord_7922885).sum := by decide
  have hdescent : baseEnd_7922885 < baseStart_7922885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922912 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 2, 4]
def baseStart_7922912 : Nat := 118140960795 + 7922912 * 2 ^ 59
def prefixEnd_7922912 : Nat := 4983230072969 + 3 ^ 40 * 7922912 * 2
def baseEnd_7922912 : Nat := 1356087346425003601354399

theorem tailTrace_7922912 : CollatzResearch.WordTrace tailWord_7922912 prefixEnd_7922912 1356087346425003601354399 := by
  unfold tailWord_7922912
  simp only [CollatzResearch.WordTrace]
  refine ⟨144486170336325212243437495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192648227115100282991249993 144486170336325212243437495)
  ·
    refine ⟨216729255504487818365156243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144486170336325212243437495 216729255504487818365156243)
    ·
      refine ⟨325093883256731727547734365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216729255504487818365156243 325093883256731727547734365)
      ·
        refine ⟨121910206221274397830400387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325093883256731727547734365 121910206221274397830400387)
        ·
          refine ⟨182865309331911596745600581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121910206221274397830400387 182865309331911596745600581)
          ·
            refine ⟨34287245499733424389800109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182865309331911596745600581 34287245499733424389800109)
            ·
              refine ⟨12857717062400034146175041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34287245499733424389800109 12857717062400034146175041)
              ·
                refine ⟨9643287796800025609631281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12857717062400034146175041 9643287796800025609631281)
                ·
                  refine ⟨7232465847600019207223461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9643287796800025609631281 7232465847600019207223461)
                  ·
                    refine ⟨1356087346425003601354399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7232465847600019207223461 1356087346425003601354399)
                    ·
                      rfl

theorem cell23_7922912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2, 4].length) (baseStart_7922912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922912 prefixEnd_7922912 := by exact prefixLift 7922912
  have htrace : WordTrace (prefixWord ++ tailWord_7922912) baseStart_7922912 baseEnd_7922912 := by
    simpa [prefixWord, tailWord_7922912, baseEnd_7922912] using wordTrace_append hprefix tailTrace_7922912
  have hstable : (prefixWord ++ tailWord_7922912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922912).length < 2 ^ (prefixWord ++ tailWord_7922912).sum := by decide
  have hdescent : baseEnd_7922912 < baseStart_7922912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922942 : List Nat := [4, 2, 2, 1, 1, 2, 4, 7]
def baseStart_7922942 : Nat := 118140960795 + 7922942 * 2 ^ 59
def prefixEnd_7922942 : Nat := 4983230072969 + 3 ^ 40 * 7922942 * 2
def baseEnd_7922942 : Nat := 150676942359060951358817

theorem tailTrace_7922942 : CollatzResearch.WordTrace tailWord_7922942 prefixEnd_7922942 150676942359060951358817 := by
  unfold tailWord_7922942
  simp only [CollatzResearch.WordTrace]
  refine ⟨36121679357817717451308385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192648956575027826406978053 36121679357817717451308385)
  ·
    refine ⟨27091259518363288088481289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36121679357817717451308385 27091259518363288088481289)
    ·
      refine ⟨20318444638772466066360967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27091259518363288088481289 20318444638772466066360967)
      ·
        refine ⟨30477666958158699099541451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20318444638772466066360967 30477666958158699099541451)
        ·
          refine ⟨45716500437238048649312177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30477666958158699099541451 45716500437238048649312177)
          ·
            refine ⟨34287375327928536486984133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45716500437238048649312177 34287375327928536486984133)
            ·
              refine ⟨6428882873986600591309525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34287375327928536486984133 6428882873986600591309525)
              ·
                refine ⟨150676942359060951358817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6428882873986600591309525 150676942359060951358817)
                ·
                  rfl

theorem cell23_7922942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_7922942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922942 prefixEnd_7922942 := by exact prefixLift 7922942
  have htrace : WordTrace (prefixWord ++ tailWord_7922942) baseStart_7922942 baseEnd_7922942 := by
    simpa [prefixWord, tailWord_7922942, baseEnd_7922942] using wordTrace_append hprefix tailTrace_7922942
  have hstable : (prefixWord ++ tailWord_7922942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922942).length < 2 ^ (prefixWord ++ tailWord_7922942).sum := by decide
  have hdescent : baseEnd_7922942 < baseStart_7922942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922986 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7922986 : Nat := 118140960795 + 7922986 * 2 ^ 59
def prefixEnd_7922986 : Nat := 4983230072969 + 3 ^ 40 * 7922986 * 2
def baseEnd_7922986 : Nat := 4068300036843443514537857

theorem tailTrace_7922986 : CollatzResearch.WordTrace tailWord_7922986 prefixEnd_7922986 4068300036843443514537857 := by
  unfold tailWord_7922986
  simp only [CollatzResearch.WordTrace]
  refine ⟨72243759918595583781267203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192650026449588223416712541 72243759918595583781267203)
  ·
    refine ⟨108365639877893375671900805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72243759918595583781267203 108365639877893375671900805)
    ·
      refine ⟨20318557477105007938481401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108365639877893375671900805 20318557477105007938481401)
      ·
        refine ⟨15238918107828755953861051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20318557477105007938481401 15238918107828755953861051)
        ·
          refine ⟨22858377161743133930791577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15238918107828755953861051 22858377161743133930791577)
          ·
            refine ⟨17143782871307350448093683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22858377161743133930791577 17143782871307350448093683)
            ·
              refine ⟨25715674306961025672140525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17143782871307350448093683 25715674306961025672140525)
              ·
                refine ⟨9643377865110384627052697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25715674306961025672140525 9643377865110384627052697)
                ·
                  refine ⟨7232533398832788470289523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9643377865110384627052697 7232533398832788470289523)
                  ·
                    refine ⟨10848800098249182705434285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7232533398832788470289523 10848800098249182705434285)
                    ·
                      refine ⟨4068300036843443514537857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10848800098249182705434285 4068300036843443514537857)
                      ·
                        rfl

theorem cell23_7922986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7922986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922986 prefixEnd_7922986 := by exact prefixLift 7922986
  have htrace : WordTrace (prefixWord ++ tailWord_7922986) baseStart_7922986 baseEnd_7922986 := by
    simpa [prefixWord, tailWord_7922986, baseEnd_7922986] using wordTrace_append hprefix tailTrace_7922986
  have hstable : (prefixWord ++ tailWord_7922986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922986).length < 2 ^ (prefixWord ++ tailWord_7922986).sum := by decide
  have hdescent : baseEnd_7922986 < baseStart_7922986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922992 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 1, 4, 2]
def baseStart_7922992 : Nat := 118140960795 + 7922992 * 2 ^ 59
def prefixEnd_7922992 : Nat := 4983230072969 + 3 ^ 40 * 7922992 * 2
def baseEnd_7922992 : Nat := 4068303117727370491062829

theorem tailTrace_7922992 : CollatzResearch.WordTrace tailWord_7922992 prefixEnd_7922992 4068303117727370491062829 := by
  unfold tailWord_7922992
  simp only [CollatzResearch.WordTrace]
  refine ⟨144487629256180299074893615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192650172341573732099858153 144487629256180299074893615)
  ·
    refine ⟨216731443884270448612340423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144487629256180299074893615 216731443884270448612340423)
    ·
      refine ⟨325097165826405672918510635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216731443884270448612340423 325097165826405672918510635)
      ·
        refine ⟨487645748739608509377765953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325097165826405672918510635 487645748739608509377765953)
        ·
          refine ⟨365734311554706382033324465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487645748739608509377765953 365734311554706382033324465)
          ·
            refine ⟨274300733666029786524993349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365734311554706382033324465 274300733666029786524993349)
            ·
              refine ⟨51431387562380584973436253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274300733666029786524993349 51431387562380584973436253)
              ·
                refine ⟨19286770335892719365038595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51431387562380584973436253 19286770335892719365038595)
                ·
                  refine ⟨28930155503839079047557893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19286770335892719365038595 28930155503839079047557893)
                  ·
                    refine ⟨5424404156969827321417105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28930155503839079047557893 5424404156969827321417105)
                    ·
                      refine ⟨4068303117727370491062829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5424404156969827321417105 4068303117727370491062829)
                      ·
                        rfl

theorem cell23_7922992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 4, 2].length) (baseStart_7922992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922992 prefixEnd_7922992 := by exact prefixLift 7922992
  have htrace : WordTrace (prefixWord ++ tailWord_7922992) baseStart_7922992 baseEnd_7922992 := by
    simpa [prefixWord, tailWord_7922992, baseEnd_7922992] using wordTrace_append hprefix tailTrace_7922992
  have hstable : (prefixWord ++ tailWord_7922992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922992).length < 2 ^ (prefixWord ++ tailWord_7922992).sum := by decide
  have hdescent : baseEnd_7922992 < baseStart_7922992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7922995 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 5]
def baseStart_7922995 : Nat := 118140960795 + 7922995 * 2 ^ 59
def prefixEnd_7922995 : Nat := 4983230072969 + 3 ^ 40 * 7922995 * 2
def baseEnd_7922995 : Nat := 4068304658169333979325315

theorem tailTrace_7922995 : CollatzResearch.WordTrace tailWord_7922995 prefixEnd_7922995 4068304658169333979325315 := by
  unfold tailWord_7922995
  simp only [CollatzResearch.WordTrace]
  refine ⟨288975367931349729662146439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192650245287566486441430959 288975367931349729662146439)
  ·
    refine ⟨433463051897024594493219659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288975367931349729662146439 433463051897024594493219659)
    ·
      refine ⟨650194577845536891739829489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433463051897024594493219659 650194577845536891739829489)
      ·
        refine ⟨487645933384152668804872117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650194577845536891739829489 487645933384152668804872117)
        ·
          refine ⟨45716806254764312700456761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 487645933384152668804872117 45716806254764312700456761)
          ·
            refine ⟨34287604691073234525342571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45716806254764312700456761 34287604691073234525342571)
            ·
              refine ⟨51431407036609851788013857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34287604691073234525342571 51431407036609851788013857)
              ·
                refine ⟨38573555277457388841010393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51431407036609851788013857 38573555277457388841010393)
                ·
                  refine ⟨28930166458093041630757795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38573555277457388841010393 28930166458093041630757795)
                  ·
                    refine ⟨43395249687139562446136693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28930166458093041630757795 43395249687139562446136693)
                    ·
                      refine ⟨4068304658169333979325315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43395249687139562446136693 4068304658169333979325315)
                      ·
                        rfl

theorem cell23_7922995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_7922995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7922995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7922995 prefixEnd_7922995 := by exact prefixLift 7922995
  have htrace : WordTrace (prefixWord ++ tailWord_7922995) baseStart_7922995 baseEnd_7922995 := by
    simpa [prefixWord, tailWord_7922995, baseEnd_7922995] using wordTrace_append hprefix tailTrace_7922995
  have hstable : (prefixWord ++ tailWord_7922995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7922995).length < 2 ^ (prefixWord ++ tailWord_7922995).sum := by decide
  have hdescent : baseEnd_7922995 < baseStart_7922995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7922995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923009 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_7923009 : Nat := 118140960795 + 7923009 * 2 ^ 59
def prefixEnd_7923009 : Nat := 4983230072969 + 3 ^ 40 * 7923009 * 2
def baseEnd_7923009 : Nat := 4068311846898496924550251

theorem tailTrace_7923009 : CollatzResearch.WordTrace tailWord_7923009 prefixEnd_7923009 4068311846898496924550251 := by
  unfold tailWord_7923009
  simp only [CollatzResearch.WordTrace]
  refine ⟨288975878553299010053156081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192650585702199340035437387 288975878553299010053156081)
  ·
    refine ⟨216731908914974257539867061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288975878553299010053156081 216731908914974257539867061)
    ·
      refine ⟨20318616460778836644362537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216731908914974257539867061 20318616460778836644362537)
      ·
        refine ⟨15238962345584127483271903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20318616460778836644362537 15238962345584127483271903)
        ·
          refine ⟨22858443518376191224907855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15238962345584127483271903 22858443518376191224907855)
          ·
            refine ⟨34287665277564286837361783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22858443518376191224907855 34287665277564286837361783)
            ·
              refine ⟨51431497916346430256042675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34287665277564286837361783 51431497916346430256042675)
              ·
                refine ⟨77147246874519645384064013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51431497916346430256042675 77147246874519645384064013)
                ·
                  refine ⟨28930217577944867019024005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77147246874519645384064013 28930217577944867019024005)
                  ·
                    refine ⟨5424415795864662566067001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28930217577944867019024005 5424415795864662566067001)
                    ·
                      refine ⟨4068311846898496924550251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5424415795864662566067001 4068311846898496924550251)
                      ·
                        rfl

theorem cell23_7923009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_7923009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923009 prefixEnd_7923009 := by exact prefixLift 7923009
  have htrace : WordTrace (prefixWord ++ tailWord_7923009) baseStart_7923009 baseEnd_7923009 := by
    simpa [prefixWord, tailWord_7923009, baseEnd_7923009] using wordTrace_append hprefix tailTrace_7923009
  have hstable : (prefixWord ++ tailWord_7923009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923009).length < 2 ^ (prefixWord ++ tailWord_7923009).sum := by decide
  have hdescent : baseEnd_7923009 < baseStart_7923009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923032 : List Nat := [2, 1, 2, 2, 1, 1, 5, 4, 5]
def baseStart_7923032 : Nat := 118140960795 + 7923032 * 2 ^ 59
def prefixEnd_7923032 : Nat := 4983230072969 + 3 ^ 40 * 7923032 * 2
def baseEnd_7923032 : Nat := 452035961883727814951405

theorem tailTrace_7923032 : CollatzResearch.WordTrace tailWord_7923032 prefixEnd_7923032 452035961883727814951405 := by
  unfold tailWord_7923032
  simp only [CollatzResearch.WordTrace]
  refine ⟨144488358716107842490621675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192651144954810456654162233 144488358716107842490621675)
  ·
    refine ⟨216732538074161763735932513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144488358716107842490621675 216732538074161763735932513)
    ·
      refine ⟨162549403555621322801949385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216732538074161763735932513 162549403555621322801949385)
      ·
        refine ⟨121912052666715992101462039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162549403555621322801949385 121912052666715992101462039)
        ·
          refine ⟨182868079000073988152193059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121912052666715992101462039 182868079000073988152193059)
          ·
            refine ⟨274302118500110982228289589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182868079000073988152193059 274302118500110982228289589)
            ·
              refine ⟨25715823609385404583902149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274302118500110982228289589 25715823609385404583902149)
              ·
                refine ⟨4821716926759763359481653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25715823609385404583902149 4821716926759763359481653)
                ·
                  refine ⟨452035961883727814951405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4821716926759763359481653 452035961883727814951405)
                  ·
                    rfl

theorem cell23_7923032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 5].length) (baseStart_7923032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923032 prefixEnd_7923032 := by exact prefixLift 7923032
  have htrace : WordTrace (prefixWord ++ tailWord_7923032) baseStart_7923032 baseEnd_7923032 := by
    simpa [prefixWord, tailWord_7923032, baseEnd_7923032] using wordTrace_append hprefix tailTrace_7923032
  have hstable : (prefixWord ++ tailWord_7923032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923032).length < 2 ^ (prefixWord ++ tailWord_7923032).sum := by decide
  have hdescent : baseEnd_7923032 < baseStart_7923032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923045 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_7923045 : Nat := 118140960795 + 7923045 * 2 ^ 59
def prefixEnd_7923045 : Nat := 4983230072969 + 3 ^ 40 * 7923045 * 2
def baseEnd_7923045 : Nat := 1356110110734019594566695

theorem tailTrace_7923045 : CollatzResearch.WordTrace tailWord_7923045 prefixEnd_7923045 1356110110734019594566695 := by
  unfold tailWord_7923045
  simp only [CollatzResearch.WordTrace]
  refine ⟨288977191581168588201466589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192651461054112392134311059 288977191581168588201466589)
  ·
    refine ⟨108366446842938220575549971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288977191581168588201466589 108366446842938220575549971)
    ·
      refine ⟨162549670264407330863324957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108366446842938220575549971 162549670264407330863324957)
      ·
        refine ⟨60956126349152749073746859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162549670264407330863324957 60956126349152749073746859)
        ·
          refine ⟨91434189523729123610620289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60956126349152749073746859 91434189523729123610620289)
          ·
            refine ⟨68575642142796842707965217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91434189523729123610620289 68575642142796842707965217)
            ·
              refine ⟨51431731607097632030973913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68575642142796842707965217 51431731607097632030973913)
              ·
                refine ⟨38573798705323224023230435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51431731607097632030973913 38573798705323224023230435)
                ·
                  refine ⟨57860698057984836034845653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38573798705323224023230435 57860698057984836034845653)
                  ·
                    refine ⟨1356110110734019594566695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57860698057984836034845653 1356110110734019594566695)
                    ·
                      rfl

theorem cell23_7923045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_7923045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923045 prefixEnd_7923045 := by exact prefixLift 7923045
  have htrace : WordTrace (prefixWord ++ tailWord_7923045) baseStart_7923045 baseEnd_7923045 := by
    simpa [prefixWord, tailWord_7923045, baseEnd_7923045] using wordTrace_append hprefix tailTrace_7923045
  have hstable : (prefixWord ++ tailWord_7923045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923045).length < 2 ^ (prefixWord ++ tailWord_7923045).sum := by decide
  have hdescent : baseEnd_7923045 < baseStart_7923045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923095 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7923095 : Nat := 118140960795 + 7923095 * 2 ^ 59
def prefixEnd_7923095 : Nat := 4983230072969 + 3 ^ 40 * 7923095 * 2
def baseEnd_7923095 : Nat := 4068356006234783588074855

theorem tailTrace_7923095 : CollatzResearch.WordTrace tailWord_7923095 prefixEnd_7923095 4068356006234783588074855 := by
  unfold tailWord_7923095
  simp only [CollatzResearch.WordTrace]
  refine ⟨288979015230987446740786739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192652676820658297827191159 288979015230987446740786739)
  ·
    refine ⟨433468522846481170111180109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288979015230987446740786739 433468522846481170111180109)
    ·
      refine ⟨162550696067430438791692541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433468522846481170111180109 162550696067430438791692541)
      ·
        refine ⟨60956511025286414546884703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162550696067430438791692541 60956511025286414546884703)
        ·
          refine ⟨91434766537929621820327055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60956511025286414546884703 91434766537929621820327055)
          ·
            refine ⟨137152149806894432730490583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91434766537929621820327055 137152149806894432730490583)
            ·
              refine ⟨205728224710341649095735875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137152149806894432730490583 205728224710341649095735875)
              ·
                refine ⟨308592337065512473643603813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205728224710341649095735875 308592337065512473643603813)
                ·
                  refine ⟨57861063199783588808175715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308592337065512473643603813 57861063199783588808175715)
                  ·
                    refine ⟨86791594799675383212263573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57861063199783588808175715 86791594799675383212263573)
                    ·
                      refine ⟨4068356006234783588074855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86791594799675383212263573 4068356006234783588074855)
                      ·
                        rfl

theorem cell23_7923095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7923095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923095 prefixEnd_7923095 := by exact prefixLift 7923095
  have htrace : WordTrace (prefixWord ++ tailWord_7923095) baseStart_7923095 baseEnd_7923095 := by
    simpa [prefixWord, tailWord_7923095, baseEnd_7923095] using wordTrace_append hprefix tailTrace_7923095
  have hstable : (prefixWord ++ tailWord_7923095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923095).length < 2 ^ (prefixWord ++ tailWord_7923095).sum := by decide
  have hdescent : baseEnd_7923095 < baseStart_7923095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923145 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_7923145 : Nat := 118140960795 + 7923145 * 2 ^ 59
def prefixEnd_7923145 : Nat := 4983230072969 + 3 ^ 40 * 7923145 * 2
def baseEnd_7923145 : Nat := 4068381680267508392449625

theorem tailTrace_7923145 : CollatzResearch.WordTrace tailWord_7923145 prefixEnd_7923145 4068381680267508392449625 := by
  unfold tailWord_7923145
  simp only [CollatzResearch.WordTrace]
  refine ⟨288980838880806305280106889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192653892587204203520071259 288980838880806305280106889)
  ·
    refine ⟨216735629160604728960080167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288980838880806305280106889 216735629160604728960080167)
    ·
      refine ⟨325103443740907093440120251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216735629160604728960080167 325103443740907093440120251)
      ·
        refine ⟨487655165611360640160180377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325103443740907093440120251 487655165611360640160180377)
        ·
          refine ⟨365741374208520480120135283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487655165611360640160180377 365741374208520480120135283)
          ·
            refine ⟨548612061312780720180202925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365741374208520480120135283 548612061312780720180202925)
            ·
              refine ⟨205729522992292770067576097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548612061312780720180202925 205729522992292770067576097)
              ·
                refine ⟨154297142244219577550682073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205729522992292770067576097 154297142244219577550682073)
                ·
                  refine ⟨115722856683164683163011555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154297142244219577550682073 115722856683164683163011555)
                  ·
                    refine ⟨173584285024747024744517333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115722856683164683163011555 173584285024747024744517333)
                    ·
                      refine ⟨4068381680267508392449625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173584285024747024744517333 4068381680267508392449625)
                      ·
                        rfl

theorem cell23_7923145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_7923145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923145 prefixEnd_7923145 := by exact prefixLift 7923145
  have htrace : WordTrace (prefixWord ++ tailWord_7923145) baseStart_7923145 baseEnd_7923145 := by
    simpa [prefixWord, tailWord_7923145, baseEnd_7923145] using wordTrace_append hprefix tailTrace_7923145
  have hstable : (prefixWord ++ tailWord_7923145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923145).length < 2 ^ (prefixWord ++ tailWord_7923145).sum := by decide
  have hdescent : baseEnd_7923145 < baseStart_7923145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923169 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 1, 5]
def baseStart_7923169 : Nat := 118140960795 + 7923169 * 2 ^ 59
def prefixEnd_7923169 : Nat := 4983230072969 + 3 ^ 40 * 7923169 * 2
def baseEnd_7923169 : Nat := 1356131334601072099516505

theorem tailTrace_7923169 : CollatzResearch.WordTrace tailWord_7923169 prefixEnd_7923169 1356131334601072099516505 := by
  unfold tailWord_7923169
  simp only [CollatzResearch.WordTrace]
  refine ⟨288981714232719357378980561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192654476155146238252653707 288981714232719357378980561)
  ·
    refine ⟨216736285674539518034235421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288981714232719357378980561 216736285674539518034235421)
    ·
      refine ⟨81276107127952319262838283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216736285674539518034235421 81276107127952319262838283)
      ·
        refine ⟨121914160691928478894257425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81276107127952319262838283 121914160691928478894257425)
        ·
          refine ⟨91435620518946359170693069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121914160691928478894257425 91435620518946359170693069)
          ·
            refine ⟨34288357694604884689009901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91435620518946359170693069 34288357694604884689009901)
            ·
              refine ⟨12858134135476831758378713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34288357694604884689009901 12858134135476831758378713)
              ·
                refine ⟨9643600601607623818784035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12858134135476831758378713 9643600601607623818784035)
                ·
                  refine ⟨14465400902411435728176053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9643600601607623818784035 14465400902411435728176053)
                  ·
                    refine ⟨1356131334601072099516505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14465400902411435728176053 1356131334601072099516505)
                    ·
                      rfl

theorem cell23_7923169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_7923169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923169 prefixEnd_7923169 := by exact prefixLift 7923169
  have htrace : WordTrace (prefixWord ++ tailWord_7923169) baseStart_7923169 baseEnd_7923169 := by
    simpa [prefixWord, tailWord_7923169, baseEnd_7923169] using wordTrace_append hprefix tailTrace_7923169
  have hstable : (prefixWord ++ tailWord_7923169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923169).length < 2 ^ (prefixWord ++ tailWord_7923169).sum := by decide
  have hdescent : baseEnd_7923169 < baseStart_7923169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923176 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_7923176 : Nat := 118140960795 + 7923176 * 2 ^ 59
def prefixEnd_7923176 : Nat := 4983230072969 + 3 ^ 40 * 7923176 * 2
def baseEnd_7923176 : Nat := 4068397598167797771161983

theorem tailTrace_7923176 : CollatzResearch.WordTrace tailWord_7923176 prefixEnd_7923176 4068397598167797771161983 := by
  unfold tailWord_7923176
  simp only [CollatzResearch.WordTrace]
  refine ⟨144490984771846998787242691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192654646362462665049656921 144490984771846998787242691)
  ·
    refine ⟨216736477157770498180864037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144490984771846998787242691 216736477157770498180864037)
    ·
      refine ⟨40638089467081968408912007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216736477157770498180864037 40638089467081968408912007)
      ·
        refine ⟨60957134200622952613368011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40638089467081968408912007 60957134200622952613368011)
        ·
          refine ⟨91435701300934428920052017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60957134200622952613368011 91435701300934428920052017)
          ·
            refine ⟨68576775975700821690039013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91435701300934428920052017 68576775975700821690039013)
            ·
              refine ⟨12858145495443904066882315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68576775975700821690039013 12858145495443904066882315)
              ·
                refine ⟨19287218243165856100323473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12858145495443904066882315 19287218243165856100323473)
                ·
                  refine ⟨14465413682374392075242605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19287218243165856100323473 14465413682374392075242605)
                  ·
                    refine ⟨5424530130890397028215977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14465413682374392075242605 5424530130890397028215977)
                    ·
                      refine ⟨4068397598167797771161983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5424530130890397028215977 4068397598167797771161983)
                      ·
                        rfl

theorem cell23_7923176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_7923176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923176 prefixEnd_7923176 := by exact prefixLift 7923176
  have htrace : WordTrace (prefixWord ++ tailWord_7923176) baseStart_7923176 baseEnd_7923176 := by
    simpa [prefixWord, tailWord_7923176, baseEnd_7923176] using wordTrace_append hprefix tailTrace_7923176
  have hstable : (prefixWord ++ tailWord_7923176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923176).length < 2 ^ (prefixWord ++ tailWord_7923176).sum := by decide
  have hdescent : baseEnd_7923176 < baseStart_7923176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923219 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 4]
def baseStart_7923219 : Nat := 118140960795 + 7923219 * 2 ^ 59
def prefixEnd_7923219 : Nat := 4983230072969 + 3 ^ 40 * 7923219 * 2
def baseEnd_7923219 : Nat := 4068419677835941102924285

theorem tailTrace_7923219 : CollatzResearch.WordTrace tailWord_7923219 prefixEnd_7923219 4068419677835941102924285 := by
  unfold tailWord_7923219
  simp only [CollatzResearch.WordTrace]
  refine ⟨288983537882538215918300711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192655691921692143945533807 288983537882538215918300711)
  ·
    refine ⟨433475306823807323877451067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288983537882538215918300711 433475306823807323877451067)
    ·
      refine ⟨650212960235710985816176601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433475306823807323877451067 650212960235710985816176601)
      ·
        refine ⟨487659720176783239362132451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650212960235710985816176601 487659720176783239362132451)
        ·
          refine ⟨731489580265174859043198677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487659720176783239362132451 731489580265174859043198677)
          ·
            refine ⟨17144287037465035758824969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 731489580265174859043198677 17144287037465035758824969)
            ·
              refine ⟨12858215278098776819118727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17144287037465035758824969 12858215278098776819118727)
              ·
                refine ⟨19287322917148165228678091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12858215278098776819118727 19287322917148165228678091)
                ·
                  refine ⟨28930984375722247843017137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19287322917148165228678091 28930984375722247843017137)
                  ·
                    refine ⟨21698238281791685882262853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28930984375722247843017137 21698238281791685882262853)
                    ·
                      refine ⟨4068419677835941102924285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21698238281791685882262853 4068419677835941102924285)
                      ·
                        rfl

theorem cell23_7923219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 4].length) (baseStart_7923219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923219 prefixEnd_7923219 := by exact prefixLift 7923219
  have htrace : WordTrace (prefixWord ++ tailWord_7923219) baseStart_7923219 baseEnd_7923219 := by
    simpa [prefixWord, tailWord_7923219, baseEnd_7923219] using wordTrace_append hprefix tailTrace_7923219
  have hstable : (prefixWord ++ tailWord_7923219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923219).length < 2 ^ (prefixWord ++ tailWord_7923219).sum := by decide
  have hdescent : baseEnd_7923219 < baseStart_7923219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923229 : List Nat := [1, 4, 2, 2, 1, 1, 5, 7]
def baseStart_7923229 : Nat := 118140960795 + 7923229 * 2 ^ 59
def prefixEnd_7923229 : Nat := 4983230072969 + 3 ^ 40 * 7923229 * 2
def baseEnd_7923229 : Nat := 150682400468240224585157

theorem tailTrace_7923229 : CollatzResearch.WordTrace tailWord_7923229 prefixEnd_7923229 150682400468240224585157 := by
  unfold tailWord_7923229
  simp only [CollatzResearch.WordTrace]
  refine ⟨288983902612501987626164741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192655935075001325084109827 288983902612501987626164741)
  ·
    refine ⟨54184481739844122679905889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288983902612501987626164741 54184481739844122679905889)
    ·
      refine ⟨40638361304883092009929417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54184481739844122679905889 40638361304883092009929417)
      ·
        refine ⟨30478770978662319007447063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40638361304883092009929417 30478770978662319007447063)
        ·
          refine ⟨45718156467993478511170595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30478770978662319007447063 45718156467993478511170595)
          ·
            refine ⟨68577234701990217766755893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45718156467993478511170595 68577234701990217766755893)
            ·
              refine ⟨6429115753311582915633365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68577234701990217766755893 6429115753311582915633365)
              ·
                refine ⟨150682400468240224585157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6429115753311582915633365 150682400468240224585157)
                ·
                  rfl

theorem cell23_7923229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 7].length) (baseStart_7923229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923229 prefixEnd_7923229 := by exact prefixLift 7923229
  have htrace : WordTrace (prefixWord ++ tailWord_7923229) baseStart_7923229 baseEnd_7923229 := by
    simpa [prefixWord, tailWord_7923229, baseEnd_7923229] using wordTrace_append hprefix tailTrace_7923229
  have hstable : (prefixWord ++ tailWord_7923229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923229).length < 2 ^ (prefixWord ++ tailWord_7923229).sum := by decide
  have hdescent : baseEnd_7923229 < baseStart_7923229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923240 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_7923240 : Nat := 118140960795 + 7923240 * 2 ^ 59
def prefixEnd_7923240 : Nat := 4983230072969 + 3 ^ 40 * 7923240 * 2
def baseEnd_7923240 : Nat := 4068430460929685520761689

theorem tailTrace_7923240 : CollatzResearch.WordTrace tailWord_7923240 prefixEnd_7923240 4068430460929685520761689 := by
  unfold tailWord_7923240
  simp only [CollatzResearch.WordTrace]
  refine ⟨144492151907731068252407587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192656202543641424336543449 144492151907731068252407587)
  ·
    refine ⟨216738227861596602378611381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144492151907731068252407587 216738227861596602378611381)
    ·
      refine ⟨20319208862024681472994817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216738227861596602378611381 20319208862024681472994817)
      ·
        refine ⟨15239406646518511104746113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20319208862024681472994817 15239406646518511104746113)
        ·
          refine ⟨11429554984888883328559585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15239406646518511104746113 11429554984888883328559585)
          ·
            refine ⟨8572166238666662496419689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11429554984888883328559585 8572166238666662496419689)
            ·
              refine ⟨6429124678999996872314767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8572166238666662496419689 6429124678999996872314767)
              ·
                refine ⟨9643687018499995308472151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6429124678999996872314767 9643687018499995308472151)
                ·
                  refine ⟨14465530527749992962708227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9643687018499995308472151 14465530527749992962708227)
                  ·
                    refine ⟨21698295791624989444062341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14465530527749992962708227 21698295791624989444062341)
                    ·
                      refine ⟨4068430460929685520761689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21698295791624989444062341 4068430460929685520761689)
                      ·
                        rfl

theorem cell23_7923240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_7923240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923240 prefixEnd_7923240 := by exact prefixLift 7923240
  have htrace : WordTrace (prefixWord ++ tailWord_7923240) baseStart_7923240 baseEnd_7923240 := by
    simpa [prefixWord, tailWord_7923240, baseEnd_7923240] using wordTrace_append hprefix tailTrace_7923240
  have hstable : (prefixWord ++ tailWord_7923240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923240).length < 2 ^ (prefixWord ++ tailWord_7923240).sum := by decide
  have hdescent : baseEnd_7923240 < baseStart_7923240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923256 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 4, 1, 3]
def baseStart_7923256 : Nat := 118140960795 + 7923256 * 2 ^ 59
def prefixEnd_7923256 : Nat := 4983230072969 + 3 ^ 40 * 7923256 * 2
def baseEnd_7923256 : Nat := 4068438676620157458161615

theorem tailTrace_7923256 : CollatzResearch.WordTrace tailWord_7923256 prefixEnd_7923256 4068438676620157458161615 := by
  unfold tailWord_7923256
  simp only [CollatzResearch.WordTrace]
  refine ⟨144492443691702085618698811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192656591588936114158265081 144492443691702085618698811)
  ·
    refine ⟨216738665537553128428048217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144492443691702085618698811 216738665537553128428048217)
    ·
      refine ⟨162553999153164846321036163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216738665537553128428048217 162553999153164846321036163)
      ·
        refine ⟨243830998729747269481554245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162553999153164846321036163 243830998729747269481554245)
        ·
          refine ⟨45718312261827613027791421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243830998729747269481554245 45718312261827613027791421)
          ·
            refine ⟨17144367098185354885421783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45718312261827613027791421 17144367098185354885421783)
            ·
              refine ⟨25716550647278032328132675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17144367098185354885421783 25716550647278032328132675)
              ·
                refine ⟨38574825970917048492199013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25716550647278032328132675 38574825970917048492199013)
                ·
                  refine ⟨7232779869546946592287315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38574825970917048492199013 7232779869546946592287315)
                  ·
                    refine ⟨10849169804320419888430973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7232779869546946592287315 10849169804320419888430973)
                    ·
                      refine ⟨4068438676620157458161615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10849169804320419888430973 4068438676620157458161615)
                      ·
                        rfl

theorem cell23_7923256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_7923256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923256 prefixEnd_7923256 := by exact prefixLift 7923256
  have htrace : WordTrace (prefixWord ++ tailWord_7923256) baseStart_7923256 baseEnd_7923256 := by
    simpa [prefixWord, tailWord_7923256, baseEnd_7923256] using wordTrace_append hprefix tailTrace_7923256
  have hstable : (prefixWord ++ tailWord_7923256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923256).length < 2 ^ (prefixWord ++ tailWord_7923256).sum := by decide
  have hdescent : baseEnd_7923256 < baseStart_7923256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923270 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_7923270 : Nat := 118140960795 + 7923270 * 2 ^ 59
def prefixEnd_7923270 : Nat := 4983230072969 + 3 ^ 40 * 7923270 * 2
def baseEnd_7923270 : Nat := 4068445865349320403386551

theorem tailTrace_7923270 : CollatzResearch.WordTrace tailWord_7923270 prefixEnd_7923270 4068445865349320403386551 := by
  unfold tailWord_7923270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030793687667295363387727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192656932003568967752271509 9030793687667295363387727)
  ·
    refine ⟨13546190531500943045081591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9030793687667295363387727 13546190531500943045081591)
    ·
      refine ⟨20319285797251414567622387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13546190531500943045081591 20319285797251414567622387)
      ·
        refine ⟨30478928695877121851433581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20319285797251414567622387 30478928695877121851433581)
        ·
          refine ⟨11429598260953920694287593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30478928695877121851433581 11429598260953920694287593)
          ·
            refine ⟨8572198695715440520715695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11429598260953920694287593 8572198695715440520715695)
            ·
              refine ⟨12858298043573160781073543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572198695715440520715695 12858298043573160781073543)
              ·
                refine ⟨19287447065359741171610315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12858298043573160781073543 19287447065359741171610315)
                ·
                  refine ⟨28931170598039611757415473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19287447065359741171610315 28931170598039611757415473)
                  ·
                    refine ⟨21698377948529708818061605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28931170598039611757415473 21698377948529708818061605)
                    ·
                      refine ⟨4068445865349320403386551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21698377948529708818061605 4068445865349320403386551)
                      ·
                        rfl

theorem cell23_7923270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_7923270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923270 prefixEnd_7923270 := by exact prefixLift 7923270
  have htrace : WordTrace (prefixWord ++ tailWord_7923270) baseStart_7923270 baseEnd_7923270 := by
    simpa [prefixWord, tailWord_7923270, baseEnd_7923270] using wordTrace_append hprefix tailTrace_7923270
  have hstable : (prefixWord ++ tailWord_7923270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923270).length < 2 ^ (prefixWord ++ tailWord_7923270).sum := by decide
  have hdescent : baseEnd_7923270 < baseStart_7923270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923299 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7923299 : Nat := 118140960795 + 7923299 * 2 ^ 59
def prefixEnd_7923299 : Nat := 4983230072969 + 3 ^ 40 * 7923299 * 2
def baseEnd_7923299 : Nat := 4068460756288300789923917

theorem tailTrace_7923299 : CollatzResearch.WordTrace tailWord_7923299 prefixEnd_7923299 4068460756288300789923917 := by
  unfold tailWord_7923299
  simp only [CollatzResearch.WordTrace]
  refine ⟨288986455722248389581212951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192657637148165593054141967 288986455722248389581212951)
  ·
    refine ⟨433479683583372584371819427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288986455722248389581212951 433479683583372584371819427)
    ·
      refine ⟨650219525375058876557729141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433479683583372584371819427 650219525375058876557729141)
      ·
        refine ⟨60958080503911769677287107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 650219525375058876557729141 60958080503911769677287107)
        ·
          refine ⟨91437120755867654515930661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60958080503911769677287107 91437120755867654515930661)
          ·
            refine ⟨17144460141725185221736999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91437120755867654515930661 17144460141725185221736999)
            ·
              refine ⟨25716690212587777832605499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17144460141725185221736999 25716690212587777832605499)
              ·
                refine ⟨38575035318881666748908249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25716690212587777832605499 38575035318881666748908249)
                ·
                  refine ⟨28931276489161250061681187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38575035318881666748908249 28931276489161250061681187)
                  ·
                    refine ⟨43396914733741875092521781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28931276489161250061681187 43396914733741875092521781)
                    ·
                      refine ⟨4068460756288300789923917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43396914733741875092521781 4068460756288300789923917)
                      ·
                        rfl

theorem cell23_7923299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7923299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923299 prefixEnd_7923299 := by exact prefixLift 7923299
  have htrace : WordTrace (prefixWord ++ tailWord_7923299) baseStart_7923299 baseEnd_7923299 := by
    simpa [prefixWord, tailWord_7923299, baseEnd_7923299] using wordTrace_append hprefix tailTrace_7923299
  have hstable : (prefixWord ++ tailWord_7923299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923299).length < 2 ^ (prefixWord ++ tailWord_7923299).sum := by decide
  have hdescent : baseEnd_7923299 < baseStart_7923299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923322 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_7923322 : Nat := 118140960795 + 7923322 * 2 ^ 59
def prefixEnd_7923322 : Nat := 4983230072969 + 3 ^ 40 * 7923322 * 2
def baseEnd_7923322 : Nat := 4068472566343354199936311

theorem tailTrace_7923322 : CollatzResearch.WordTrace tailWord_7923322 prefixEnd_7923322 4068472566343354199936311 := by
  unfold tailWord_7923322
  simp only [CollatzResearch.WordTrace]
  refine ⟨72246823650291266127325055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192658196400776709672866813 72246823650291266127325055)
  ·
    refine ⟨108370235475436899190987583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72246823650291266127325055 108370235475436899190987583)
    ·
      refine ⟨162555353213155348786481375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108370235475436899190987583 162555353213155348786481375)
      ·
        refine ⟨243833029819733023179722063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162555353213155348786481375 243833029819733023179722063)
        ·
          refine ⟨365749544729599534769583095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243833029819733023179722063 365749544729599534769583095)
          ·
            refine ⟨548624317094399302154374643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365749544729599534769583095 548624317094399302154374643)
            ·
              refine ⟨822936475641598953231561965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548624317094399302154374643 822936475641598953231561965)
              ·
                refine ⟨308601178365599607461835737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 822936475641598953231561965 308601178365599607461835737)
                ·
                  refine ⟨231450883774199705596376803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308601178365599607461835737 231450883774199705596376803)
                  ·
                    refine ⟨347176325661299558394565205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231450883774199705596376803 347176325661299558394565205)
                    ·
                      refine ⟨4068472566343354199936311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 347176325661299558394565205 4068472566343354199936311)
                      ·
                        rfl

theorem cell23_7923322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_7923322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923322 prefixEnd_7923322 := by exact prefixLift 7923322
  have htrace : WordTrace (prefixWord ++ tailWord_7923322) baseStart_7923322 baseEnd_7923322 := by
    simpa [prefixWord, tailWord_7923322, baseEnd_7923322] using wordTrace_append hprefix tailTrace_7923322
  have hstable : (prefixWord ++ tailWord_7923322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923322).length < 2 ^ (prefixWord ++ tailWord_7923322).sum := by decide
  have hdescent : baseEnd_7923322 < baseStart_7923322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923386 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2]
def baseStart_7923386 : Nat := 118140960795 + 7923386 * 2 ^ 59
def prefixEnd_7923386 : Nat := 4983230072969 + 3 ^ 40 * 7923386 * 2
def baseEnd_7923386 : Nat := 4068505429105241949536017

theorem tailTrace_7923386 : CollatzResearch.WordTrace tailWord_7923386 prefixEnd_7923386 4068505429105241949536017 := by
  unfold tailWord_7923386
  simp only [CollatzResearch.WordTrace]
  refine ⟨72247407218233300859907503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192659752581955468959753341 72247407218233300859907503)
  ·
    refine ⟨108371110827349951289861255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72247407218233300859907503 108371110827349951289861255)
    ·
      refine ⟨162556666241024926934791883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108371110827349951289861255 162556666241024926934791883)
      ·
        refine ⟨243834999361537390402187825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162556666241024926934791883 243834999361537390402187825)
        ·
          refine ⟨182876249521153042801640869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243834999361537390402187825 182876249521153042801640869)
          ·
            refine ⟨34289296785216195525307663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182876249521153042801640869 34289296785216195525307663)
            ·
              refine ⟨51433945177824293287961495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34289296785216195525307663 51433945177824293287961495)
              ·
                refine ⟨77150917766736439931942243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51433945177824293287961495 77150917766736439931942243)
                ·
                  refine ⟨115726376650104659897913365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77150917766736439931942243 115726376650104659897913365)
                  ·
                    refine ⟨5424673905473655932714689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115726376650104659897913365 5424673905473655932714689)
                    ·
                      refine ⟨4068505429105241949536017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5424673905473655932714689 4068505429105241949536017)
                      ·
                        rfl

theorem cell23_7923386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_7923386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923386 prefixEnd_7923386 := by exact prefixLift 7923386
  have htrace : WordTrace (prefixWord ++ tailWord_7923386) baseStart_7923386 baseEnd_7923386 := by
    simpa [prefixWord, tailWord_7923386, baseEnd_7923386] using wordTrace_append hprefix tailTrace_7923386
  have hstable : (prefixWord ++ tailWord_7923386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923386).length < 2 ^ (prefixWord ++ tailWord_7923386).sum := by decide
  have hdescent : baseEnd_7923386 < baseStart_7923386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923406 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_7923406 : Nat := 118140960795 + 7923406 * 2 ^ 59
def prefixEnd_7923406 : Nat := 4983230072969 + 3 ^ 40 * 7923406 * 2
def baseEnd_7923406 : Nat := 4068515698718331871285925

theorem tailTrace_7923406 : CollatzResearch.WordTrace tailWord_7923406 prefixEnd_7923406 4068515698718331871285925 := by
  unfold tailWord_7923406
  simp only [CollatzResearch.WordTrace]
  refine ⟨36123794791607593356919759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192660238888573831236905381 36123794791607593356919759)
  ·
    refine ⟨54185692187411390035379639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36123794791607593356919759 54185692187411390035379639)
    ·
      refine ⟨81278538281117085053069459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54185692187411390035379639 81278538281117085053069459)
      ·
        refine ⟨121917807421675627579604189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81278538281117085053069459 121917807421675627579604189)
        ·
          refine ⟨45719177783128360342351571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121917807421675627579604189 45719177783128360342351571)
          ·
            refine ⟨68578766674692540513527357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45719177783128360342351571 68578766674692540513527357)
            ·
              refine ⟨25717037503009702692572759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68578766674692540513527357 25717037503009702692572759)
              ·
                refine ⟨38575556254514554038859139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25717037503009702692572759 38575556254514554038859139)
                ·
                  refine ⟨57863334381771831058288709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38575556254514554038859139 57863334381771831058288709)
                  ·
                    refine ⟨10849375196582218323429133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57863334381771831058288709 10849375196582218323429133)
                    ·
                      refine ⟨4068515698718331871285925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10849375196582218323429133 4068515698718331871285925)
                      ·
                        rfl

theorem cell23_7923406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_7923406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923406 prefixEnd_7923406 := by exact prefixLift 7923406
  have htrace : WordTrace (prefixWord ++ tailWord_7923406) baseStart_7923406 baseEnd_7923406 := by
    simpa [prefixWord, tailWord_7923406, baseEnd_7923406] using wordTrace_append hprefix tailTrace_7923406
  have hstable : (prefixWord ++ tailWord_7923406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923406).length < 2 ^ (prefixWord ++ tailWord_7923406).sum := by decide
  have hdescent : baseEnd_7923406 < baseStart_7923406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923429 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_7923429 : Nat := 118140960795 + 7923429 * 2 ^ 59
def prefixEnd_7923429 : Nat := 4983230072969 + 3 ^ 40 * 7923429 * 2
def baseEnd_7923429 : Nat := 4068527508773385281298319

theorem tailTrace_7923429 : CollatzResearch.WordTrace tailWord_7923429 prefixEnd_7923429 4068527508773385281298319 := by
  unfold tailWord_7923429
  simp only [CollatzResearch.WordTrace]
  refine ⟨288991197211777421783445341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192660798141184947855630227 288991197211777421783445341)
  ·
    refine ⟨108371698954416533168792003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288991197211777421783445341 108371698954416533168792003)
    ·
      refine ⟨162557548431624799753188005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108371698954416533168792003 162557548431624799753188005)
      ·
        refine ⟨30479540330929649953722751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162557548431624799753188005 30479540330929649953722751)
        ·
          refine ⟨45719310496394474930584127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30479540330929649953722751 45719310496394474930584127)
          ·
            refine ⟨68578965744591712395876191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45719310496394474930584127 68578965744591712395876191)
            ·
              refine ⟨102868448616887568593814287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68578965744591712395876191 102868448616887568593814287)
              ·
                refine ⟨154302672925331352890721431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102868448616887568593814287 154302672925331352890721431)
                ·
                  refine ⟨231454009387997029336082147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154302672925331352890721431 231454009387997029336082147)
                  ·
                    refine ⟨347181014081995544004123221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231454009387997029336082147 347181014081995544004123221)
                    ·
                      refine ⟨4068527508773385281298319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 347181014081995544004123221 4068527508773385281298319)
                      ·
                        rfl

theorem cell23_7923429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_7923429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923429 prefixEnd_7923429 := by exact prefixLift 7923429
  have htrace : WordTrace (prefixWord ++ tailWord_7923429) baseStart_7923429 baseEnd_7923429 := by
    simpa [prefixWord, tailWord_7923429, baseEnd_7923429] using wordTrace_append hprefix tailTrace_7923429
  have hstable : (prefixWord ++ tailWord_7923429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923429).length < 2 ^ (prefixWord ++ tailWord_7923429).sum := by decide
  have hdescent : baseEnd_7923429 < baseStart_7923429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923487 : List Nat := [1, 1, 2, 4, 2, 1, 5, 2, 1, 1, 3]
def baseStart_7923487 : Nat := 118140960795 + 7923487 * 2 ^ 59
def prefixEnd_7923487 : Nat := 4983230072969 + 3 ^ 40 * 7923487 * 2
def baseEnd_7923487 : Nat := 4068557290651346054373053

theorem tailTrace_7923487 : CollatzResearch.WordTrace tailWord_7923487 prefixEnd_7923487 4068557290651346054373053 := by
  unfold tailWord_7923487
  simp only [CollatzResearch.WordTrace]
  refine ⟨288993312645567297689056715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192662208430378198459371143 288993312645567297689056715)
  ·
    refine ⟨433489968968350946533585073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288993312645567297689056715 433489968968350946533585073)
    ·
      refine ⟨325117476726263209900188805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433489968968350946533585073 325117476726263209900188805)
      ·
        refine ⟨60959526886174351856285401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325117476726263209900188805 60959526886174351856285401)
        ·
          refine ⟨45719645164630763892214051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60959526886174351856285401 45719645164630763892214051)
          ·
            refine ⟨68579467746946145838321077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45719645164630763892214051 68579467746946145838321077)
            ·
              refine ⟨6429325101276201172342601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68579467746946145838321077 6429325101276201172342601)
              ·
                refine ⟨4821993825957150879256951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6429325101276201172342601 4821993825957150879256951)
                ·
                  refine ⟨7232990738935726318885427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821993825957150879256951 7232990738935726318885427)
                  ·
                    refine ⟨10849486108403589478328141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7232990738935726318885427 10849486108403589478328141)
                    ·
                      refine ⟨4068557290651346054373053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10849486108403589478328141 4068557290651346054373053)
                      ·
                        rfl

theorem cell23_7923487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_7923487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923487 prefixEnd_7923487 := by exact prefixLift 7923487
  have htrace : WordTrace (prefixWord ++ tailWord_7923487) baseStart_7923487 baseEnd_7923487 := by
    simpa [prefixWord, tailWord_7923487, baseEnd_7923487] using wordTrace_append hprefix tailTrace_7923487
  have hstable : (prefixWord ++ tailWord_7923487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923487).length < 2 ^ (prefixWord ++ tailWord_7923487).sum := by decide
  have hdescent : baseEnd_7923487 < baseStart_7923487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923506 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_7923506 : Nat := 118140960795 + 7923506 * 2 ^ 59
def prefixEnd_7923506 : Nat := 4983230072969 + 3 ^ 40 * 7923506 * 2
def baseEnd_7923506 : Nat := 4068567046783781480035465

theorem tailTrace_7923506 : CollatzResearch.WordTrace tailWord_7923506 prefixEnd_7923506 4068567046783781480035465 := by
  unfold tailWord_7923506
  simp only [CollatzResearch.WordTrace]
  refine ⟨72248501408124615983499593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192662670421665642622665581 72248501408124615983499593)
  ·
    refine ⟨54186376056093461987624695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72248501408124615983499593 54186376056093461987624695)
    ·
      refine ⟨81279564084140192981437043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54186376056093461987624695 81279564084140192981437043)
      ·
        refine ⟨121919346126210289472155565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81279564084140192981437043 121919346126210289472155565)
        ·
          refine ⟨45719754797328858552058337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121919346126210289472155565 45719754797328858552058337)
          ·
            refine ⟨34289816097996643914043753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45719754797328858552058337 34289816097996643914043753)
            ·
              refine ⟨25717362073497482935532815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34289816097996643914043753 25717362073497482935532815)
              ·
                refine ⟨38576043110246224403299223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25717362073497482935532815 38576043110246224403299223)
                ·
                  refine ⟨57864064665369336604948835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38576043110246224403299223 57864064665369336604948835)
                  ·
                    refine ⟨86796096998054004907423253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57864064665369336604948835 86796096998054004907423253)
                    ·
                      refine ⟨4068567046783781480035465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86796096998054004907423253 4068567046783781480035465)
                      ·
                        rfl

theorem cell23_7923506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_7923506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923506 prefixEnd_7923506 := by exact prefixLift 7923506
  have htrace : WordTrace (prefixWord ++ tailWord_7923506) baseStart_7923506 baseEnd_7923506 := by
    simpa [prefixWord, tailWord_7923506, baseEnd_7923506] using wordTrace_append hprefix tailTrace_7923506
  have hstable : (prefixWord ++ tailWord_7923506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923506).length < 2 ^ (prefixWord ++ tailWord_7923506).sum := by decide
  have hdescent : baseEnd_7923506 < baseStart_7923506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923510 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7923510 : Nat := 118140960795 + 7923510 * 2 ^ 59
def prefixEnd_7923510 : Nat := 4983230072969 + 3 ^ 40 * 7923510 * 2
def baseEnd_7923510 : Nat := 4068569100706399464385447

theorem tailTrace_7923510 : CollatzResearch.WordTrace tailWord_7923510 prefixEnd_7923510 4068569100706399464385447 := by
  unfold tailWord_7923510
  simp only [CollatzResearch.WordTrace]
  refine ⟨18062134470280248288571499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192662767682989315078095989 18062134470280248288571499)
  ·
    refine ⟨27093201705420372432857249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18062134470280248288571499 27093201705420372432857249)
    ·
      refine ⟨20319901279065279324642937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27093201705420372432857249 20319901279065279324642937)
      ·
        refine ⟨15239925959298959493482203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20319901279065279324642937 15239925959298959493482203)
        ·
          refine ⟨22859888938948439240223305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15239925959298959493482203 22859888938948439240223305)
          ·
            refine ⟨17144916704211329430167479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22859888938948439240223305 17144916704211329430167479)
            ·
              refine ⟨25717375056316994145251219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17144916704211329430167479 25717375056316994145251219)
              ·
                refine ⟨38576062584475491217876829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25717375056316994145251219 38576062584475491217876829)
                ·
                  refine ⟨14466023469178309206703811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38576062584475491217876829 14466023469178309206703811)
                  ·
                    refine ⟨21699035203767463810055717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14466023469178309206703811 21699035203767463810055717)
                    ·
                      refine ⟨4068569100706399464385447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21699035203767463810055717 4068569100706399464385447)
                      ·
                        rfl

theorem cell23_7923510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7923510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923510 prefixEnd_7923510 := by exact prefixLift 7923510
  have htrace : WordTrace (prefixWord ++ tailWord_7923510) baseStart_7923510 baseEnd_7923510 := by
    simpa [prefixWord, tailWord_7923510, baseEnd_7923510] using wordTrace_append hprefix tailTrace_7923510
  have hstable : (prefixWord ++ tailWord_7923510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923510).length < 2 ^ (prefixWord ++ tailWord_7923510).sum := by decide
  have hdescent : baseEnd_7923510 < baseStart_7923510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923530 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3]
def baseStart_7923530 : Nat := 118140960795 + 7923530 * 2 ^ 59
def prefixEnd_7923530 : Nat := 4983230072969 + 3 ^ 40 * 7923530 * 2
def baseEnd_7923530 : Nat := 4068579370319489386135355

theorem tailTrace_7923530 : CollatzResearch.WordTrace tailWord_7923530 prefixEnd_7923530 4068579370319489386135355 := by
  unfold tailWord_7923530
  simp only [CollatzResearch.WordTrace]
  refine ⟨72248720246102879008218011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192663253989607677355248029 72248720246102879008218011)
  ·
    refine ⟨108373080369154318512327017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72248720246102879008218011 108373080369154318512327017)
    ·
      refine ⟨81279810276865738884245263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108373080369154318512327017 81279810276865738884245263)
      ·
        refine ⟨121919715415298608326367895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81279810276865738884245263 121919715415298608326367895)
        ·
          refine ⟨182879573122947912489551843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121919715415298608326367895 182879573122947912489551843)
          ·
            refine ⟨274319359684421868734327765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182879573122947912489551843 274319359684421868734327765)
            ·
              refine ⟨6429359992603637548460807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 274319359684421868734327765 6429359992603637548460807)
              ·
                refine ⟨9644039988905456322691211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6429359992603637548460807 9644039988905456322691211)
                ·
                  refine ⟨14466059983358184484036817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9644039988905456322691211 14466059983358184484036817)
                  ·
                    refine ⟨10849544987518638363027613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14466059983358184484036817 10849544987518638363027613)
                    ·
                      refine ⟨4068579370319489386135355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10849544987518638363027613 4068579370319489386135355)
                      ·
                        rfl

theorem cell23_7923530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_7923530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923530 prefixEnd_7923530 := by exact prefixLift 7923530
  have htrace : WordTrace (prefixWord ++ tailWord_7923530) baseStart_7923530 baseEnd_7923530 := by
    simpa [prefixWord, tailWord_7923530, baseEnd_7923530] using wordTrace_append hprefix tailTrace_7923530
  have hstable : (prefixWord ++ tailWord_7923530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923530).length < 2 ^ (prefixWord ++ tailWord_7923530).sum := by decide
  have hdescent : baseEnd_7923530 < baseStart_7923530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923539 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 7]
def baseStart_7923539 : Nat := 118140960795 + 7923539 * 2 ^ 59
def prefixEnd_7923539 : Nat := 4983230072969 + 3 ^ 40 * 7923539 * 2
def baseEnd_7923539 : Nat := 4068583991645379850922813

theorem tailTrace_7923539 : CollatzResearch.WordTrace tailWord_7923539 prefixEnd_7923539 4068583991645379850922813 := by
  unfold tailWord_7923539
  simp only [CollatzResearch.WordTrace]
  refine ⟨288995209241378910569949671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192663472827585940379966447 288995209241378910569949671)
  ·
    refine ⟨433492813862068365854924507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288995209241378910569949671 433492813862068365854924507)
    ·
      refine ⟨650239220793102548782386761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433492813862068365854924507 650239220793102548782386761)
      ·
        refine ⟨487679415594826911586790071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650239220793102548782386761 487679415594826911586790071)
        ·
          refine ⟨731519123392240367380185107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487679415594826911586790071 731519123392240367380185107)
          ·
            refine ⟨1097278685088360551070277661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731519123392240367380185107 1097278685088360551070277661)
            ·
              refine ⟨411479506908135206651354123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1097278685088360551070277661 411479506908135206651354123)
              ·
                refine ⟨617219260362202809977031185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411479506908135206651354123 617219260362202809977031185)
                ·
                  refine ⟨462914445271652107482773389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617219260362202809977031185 462914445271652107482773389)
                  ·
                    refine ⟨173592916976869540306040021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462914445271652107482773389 173592916976869540306040021)
                    ·
                      refine ⟨4068583991645379850922813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173592916976869540306040021 4068583991645379850922813)
                      ·
                        rfl

theorem cell23_7923539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_7923539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923539 prefixEnd_7923539 := by exact prefixLift 7923539
  have htrace : WordTrace (prefixWord ++ tailWord_7923539) baseStart_7923539 baseEnd_7923539 := by
    simpa [prefixWord, tailWord_7923539, baseEnd_7923539] using wordTrace_append hprefix tailTrace_7923539
  have hstable : (prefixWord ++ tailWord_7923539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923539).length < 2 ^ (prefixWord ++ tailWord_7923539).sum := by decide
  have hdescent : baseEnd_7923539 < baseStart_7923539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923553 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 5, 3, 2]
def baseStart_7923553 : Nat := 118140960795 + 7923553 * 2 ^ 59
def prefixEnd_7923553 : Nat := 4983230072969 + 3 ^ 40 * 7923553 * 2
def baseEnd_7923553 : Nat := 4068591180374542796147749

theorem tailTrace_7923553 : CollatzResearch.WordTrace tailWord_7923553 prefixEnd_7923553 4068591180374542796147749 := by
  unfold tailWord_7923553
  simp only [CollatzResearch.WordTrace]
  refine ⟨288995719863328190960959313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192663813242218793973972875 288995719863328190960959313)
  ·
    refine ⟨216746789897496143220719485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288995719863328190960959313 216746789897496143220719485)
    ·
      refine ⟨81280046211561053707769807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216746789897496143220719485 81280046211561053707769807)
      ·
        refine ⟨121920069317341580561654711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81280046211561053707769807 121920069317341580561654711)
        ·
          refine ⟨182880103976012370842482067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121920069317341580561654711 182880103976012370842482067)
          ·
            refine ⟨274320155964018556263723101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182880103976012370842482067 274320155964018556263723101)
            ·
              refine ⟨102870058486506958598896163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274320155964018556263723101 102870058486506958598896163)
              ·
                refine ⟨154305087729760437898344245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102870058486506958598896163 154305087729760437898344245)
                ·
                  refine ⟨14466101974665041052969773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154305087729760437898344245 14466101974665041052969773)
                  ·
                    refine ⟨5424788240499390394863665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14466101974665041052969773 5424788240499390394863665)
                    ·
                      refine ⟨4068591180374542796147749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5424788240499390394863665 4068591180374542796147749)
                      ·
                        rfl

theorem cell23_7923553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_7923553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923553 prefixEnd_7923553 := by exact prefixLift 7923553
  have htrace : WordTrace (prefixWord ++ tailWord_7923553) baseStart_7923553 baseEnd_7923553 := by
    simpa [prefixWord, tailWord_7923553, baseEnd_7923553] using wordTrace_append hprefix tailTrace_7923553
  have hstable : (prefixWord ++ tailWord_7923553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923553).length < 2 ^ (prefixWord ++ tailWord_7923553).sum := by decide
  have hdescent : baseEnd_7923553 < baseStart_7923553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923560 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_7923560 : Nat := 118140960795 + 7923560 * 2 ^ 59
def prefixEnd_7923560 : Nat := 4983230072969 + 3 ^ 40 * 7923560 * 2
def baseEnd_7923560 : Nat := 4068594774739124268760217

theorem tailTrace_7923560 : CollatzResearch.WordTrace tailWord_7923560 prefixEnd_7923560 4068594774739124268760217 := by
  unfold tailWord_7923560
  simp only [CollatzResearch.WordTrace]
  refine ⟨144497987587151415578232067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192663983449535220770976089 144497987587151415578232067)
  ·
    refine ⟨216746981380727123367348101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144497987587151415578232067 216746981380727123367348101)
    ·
      refine ⟨40640059008886335631377769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216746981380727123367348101 40640059008886335631377769)
      ·
        refine ⟨30480044256664751723533327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40640059008886335631377769 30480044256664751723533327)
        ·
          refine ⟨45720066384997127585299991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30480044256664751723533327 45720066384997127585299991)
          ·
            refine ⟨68580099577495691377949987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45720066384997127585299991 68580099577495691377949987)
            ·
              refine ⟨102870149366243537066924981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68580099577495691377949987 102870149366243537066924981)
              ·
                refine ⟨9644076503085331600024217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102870149366243537066924981 9644076503085331600024217)
                ·
                  refine ⟨7233057377313998700018163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9644076503085331600024217 7233057377313998700018163)
                  ·
                    refine ⟨10849586065970998050027245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7233057377313998700018163 10849586065970998050027245)
                    ·
                      refine ⟨4068594774739124268760217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10849586065970998050027245 4068594774739124268760217)
                      ·
                        rfl

theorem cell23_7923560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_7923560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923560 prefixEnd_7923560 := by exact prefixLift 7923560
  have htrace : WordTrace (prefixWord ++ tailWord_7923560) baseStart_7923560 baseEnd_7923560 := by
    simpa [prefixWord, tailWord_7923560, baseEnd_7923560] using wordTrace_append hprefix tailTrace_7923560
  have hstable : (prefixWord ++ tailWord_7923560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923560).length < 2 ^ (prefixWord ++ tailWord_7923560).sum := by decide
  have hdescent : baseEnd_7923560 < baseStart_7923560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923570 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 1, 3, 2]
def baseStart_7923570 : Nat := 118140960795 + 7923570 * 2 ^ 59
def prefixEnd_7923570 : Nat := 4983230072969 + 3 ^ 40 * 7923570 * 2
def baseEnd_7923570 : Nat := 4068599909545669229635171

theorem tailTrace_7923570 : CollatzResearch.WordTrace tailWord_7923570 prefixEnd_7923570 4068599909545669229635171 := by
  unfold tailWord_7923570
  simp only [CollatzResearch.WordTrace]
  refine ⟨72249084976066650716082041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192664226602844401909552109 72249084976066650716082041)
  ·
    refine ⟨54186813732049988037061531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72249084976066650716082041 54186813732049988037061531)
    ·
      refine ⟨81280220598074982055592297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54186813732049988037061531 81280220598074982055592297)
      ·
        refine ⟨60960165448556236541694223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81280220598074982055592297 60960165448556236541694223)
        ·
          refine ⟨91440248172834354812541335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60960165448556236541694223 91440248172834354812541335)
          ·
            refine ⟨137160372259251532218812003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91440248172834354812541335 137160372259251532218812003)
            ·
              refine ⟨205740558388877298328218005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137160372259251532218812003 205740558388877298328218005)
              ·
                refine ⟨9644088674478623359135219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205740558388877298328218005 9644088674478623359135219)
                ·
                  refine ⟨14466133011717935038702829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9644088674478623359135219 14466133011717935038702829)
                  ·
                    refine ⟨5424799879394225639513561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14466133011717935038702829 5424799879394225639513561)
                    ·
                      refine ⟨4068599909545669229635171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5424799879394225639513561 4068599909545669229635171)
                      ·
                        rfl

theorem cell23_7923570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_7923570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923570 prefixEnd_7923570 := by exact prefixLift 7923570
  have htrace : WordTrace (prefixWord ++ tailWord_7923570) baseStart_7923570 baseEnd_7923570 := by
    simpa [prefixWord, tailWord_7923570, baseEnd_7923570] using wordTrace_append hprefix tailTrace_7923570
  have hstable : (prefixWord ++ tailWord_7923570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923570).length < 2 ^ (prefixWord ++ tailWord_7923570).sum := by decide
  have hdescent : baseEnd_7923570 < baseStart_7923570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923587 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 1, 3, 2]
def baseStart_7923587 : Nat := 118140960795 + 7923587 * 2 ^ 59
def prefixEnd_7923587 : Nat := 4983230072969 + 3 ^ 40 * 7923587 * 2
def baseEnd_7923587 : Nat := 4068608638716795663122593

theorem tailTrace_7923587 : CollatzResearch.WordTrace tailWord_7923587 prefixEnd_7923587 4068608638716795663122593 := by
  unfold tailWord_7923587
  simp only [CollatzResearch.WordTrace]
  refine ⟨288996959945205014767697015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192664639963470009845131343 288996959945205014767697015)
  ·
    refine ⟨433495439917807522151545523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288996959945205014767697015 433495439917807522151545523)
    ·
      refine ⟨650243159876711283227318285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433495439917807522151545523 650243159876711283227318285)
      ·
        refine ⟨243841184953766731210244357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 650243159876711283227318285 243841184953766731210244357)
        ·
          refine ⟨45720222178831262101920817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243841184953766731210244357 45720222178831262101920817)
          ·
            refine ⟨34290166634123446576440613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45720222178831262101920817 34290166634123446576440613)
            ·
              refine ⟨6429406243898146233082615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34290166634123446576440613 6429406243898146233082615)
              ·
                refine ⟨9644109365847219349623923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6429406243898146233082615 9644109365847219349623923)
                ·
                  refine ⟨14466164048770829024435885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9644109365847219349623923 14466164048770829024435885)
                  ·
                    refine ⟨5424811518289060884163457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14466164048770829024435885 5424811518289060884163457)
                    ·
                      refine ⟨4068608638716795663122593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5424811518289060884163457 4068608638716795663122593)
                      ·
                        rfl

theorem cell23_7923587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_7923587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923587 prefixEnd_7923587 := by exact prefixLift 7923587
  have htrace : WordTrace (prefixWord ++ tailWord_7923587) baseStart_7923587 baseEnd_7923587 := by
    simpa [prefixWord, tailWord_7923587, baseEnd_7923587] using wordTrace_append hprefix tailTrace_7923587
  have hstable : (prefixWord ++ tailWord_7923587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923587).length < 2 ^ (prefixWord ++ tailWord_7923587).sum := by decide
  have hdescent : baseEnd_7923587 < baseStart_7923587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923594 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_7923594 : Nat := 118140960795 + 7923594 * 2 ^ 59
def prefixEnd_7923594 : Nat := 4983230072969 + 3 ^ 40 * 7923594 * 2
def baseEnd_7923594 : Nat := 4068612233081377135735061

theorem tailTrace_7923594 : CollatzResearch.WordTrace tailWord_7923594 prefixEnd_7923594 4068612233081377135735061 := by
  unfold tailWord_7923594
  simp only [CollatzResearch.WordTrace]
  refine ⟨72249303814044913740800459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192664810170786436642134557 72249303814044913740800459)
  ·
    refine ⟨108373955721067370611200689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72249303814044913740800459 108373955721067370611200689)
    ·
      refine ⟨81280466790800527958400517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108373955721067370611200689 81280466790800527958400517)
      ·
        refine ⟨15240087523275098992200097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81280466790800527958400517 15240087523275098992200097)
        ·
          refine ⟨11430065642456324244150073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15240087523275098992200097 11430065642456324244150073)
          ·
            refine ⟨8572549231842243183112555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11430065642456324244150073 8572549231842243183112555)
            ·
              refine ⟨12858823847763364774668833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572549231842243183112555 12858823847763364774668833)
              ·
                refine ⟨9644117885822523581001625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12858823847763364774668833 9644117885822523581001625)
                ·
                  refine ⟨7233088414366892685751219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9644117885822523581001625 7233088414366892685751219)
                  ·
                    refine ⟨10849632621550339028626829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7233088414366892685751219 10849632621550339028626829)
                    ·
                      refine ⟨4068612233081377135735061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10849632621550339028626829 4068612233081377135735061)
                      ·
                        rfl

theorem cell23_7923594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_7923594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923594 prefixEnd_7923594 := by exact prefixLift 7923594
  have htrace : WordTrace (prefixWord ++ tailWord_7923594) baseStart_7923594 baseEnd_7923594 := by
    simpa [prefixWord, tailWord_7923594, baseEnd_7923594] using wordTrace_append hprefix tailTrace_7923594
  have hstable : (prefixWord ++ tailWord_7923594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923594).length < 2 ^ (prefixWord ++ tailWord_7923594).sum := by decide
  have hdescent : baseEnd_7923594 < baseStart_7923594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923613 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_7923613 : Nat := 118140960795 + 7923613 * 2 ^ 59
def prefixEnd_7923613 : Nat := 4983230072969 + 3 ^ 40 * 7923613 * 2
def baseEnd_7923613 : Nat := 4068621989213812561397473

theorem tailTrace_7923613 : CollatzResearch.WordTrace tailWord_7923613 prefixEnd_7923613 4068621989213812561397473 := by
  unfold tailWord_7923613
  simp only [CollatzResearch.WordTrace]
  refine ⟨288997908243110821208143493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192665272162073880805428995 288997908243110821208143493)
  ·
    refine ⟨54187107795583278976526905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288997908243110821208143493 54187107795583278976526905)
    ·
      refine ⟨40640330846687459232395179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54187107795583278976526905 40640330846687459232395179)
      ·
        refine ⟨60960496270031188848592769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40640330846687459232395179 60960496270031188848592769)
        ·
          refine ⟨45720372202523391636444577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60960496270031188848592769 45720372202523391636444577)
          ·
            refine ⟨34290279151892543727333433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45720372202523391636444577 34290279151892543727333433)
            ·
              refine ⟨25717709363919407795500075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34290279151892543727333433 25717709363919407795500075)
              ·
                refine ⟨38576564045879111693250113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25717709363919407795500075 38576564045879111693250113)
                ·
                  refine ⟨28932423034409333769937585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38576564045879111693250113 28932423034409333769937585)
                  ·
                    refine ⟨21699317275807000327453189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28932423034409333769937585 21699317275807000327453189)
                    ·
                      refine ⟨4068621989213812561397473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21699317275807000327453189 4068621989213812561397473)
                      ·
                        rfl

theorem cell23_7923613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_7923613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923613 prefixEnd_7923613 := by exact prefixLift 7923613
  have htrace : WordTrace (prefixWord ++ tailWord_7923613) baseStart_7923613 baseEnd_7923613 := by
    simpa [prefixWord, tailWord_7923613, baseEnd_7923613] using wordTrace_append hprefix tailTrace_7923613
  have hstable : (prefixWord ++ tailWord_7923613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923613).length < 2 ^ (prefixWord ++ tailWord_7923613).sum := by decide
  have hdescent : baseEnd_7923613 < baseStart_7923613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923623 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 7]
def baseStart_7923623 : Nat := 118140960795 + 7923623 * 2 ^ 59
def prefixEnd_7923623 : Nat := 4983230072969 + 3 ^ 40 * 7923623 * 2
def baseEnd_7923623 : Nat := 452069680446706391363603

theorem tailTrace_7923623 : CollatzResearch.WordTrace tailWord_7923623 prefixEnd_7923623 452069680446706391363603 := by
  unfold tailWord_7923623
  simp only [CollatzResearch.WordTrace]
  refine ⟨288998272973074592916007523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192665515315383061944005015 288998272973074592916007523)
  ·
    refine ⟨433497409459611889374011285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288998272973074592916007523 433497409459611889374011285)
    ·
      refine ⟨20320191068419307314406779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 433497409459611889374011285 20320191068419307314406779)
      ·
        refine ⟨30480286602628960971610169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20320191068419307314406779 30480286602628960971610169)
        ·
          refine ⟨22860214951971720728707627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30480286602628960971610169 22860214951971720728707627)
          ·
            refine ⟨34290322427957581093061441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22860214951971720728707627 34290322427957581093061441)
            ·
              refine ⟨25717741820968185819796081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34290322427957581093061441 25717741820968185819796081)
              ·
                refine ⟨19288306365726139364847061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25717741820968185819796081 19288306365726139364847061)
                ·
                  refine ⟨452069680446706391363603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19288306365726139364847061 452069680446706391363603)
                  ·
                    rfl

theorem cell23_7923623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 7].length) (baseStart_7923623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923623 prefixEnd_7923623 := by exact prefixLift 7923623
  have htrace : WordTrace (prefixWord ++ tailWord_7923623) baseStart_7923623 baseEnd_7923623 := by
    simpa [prefixWord, tailWord_7923623, baseEnd_7923623] using wordTrace_append hprefix tailTrace_7923623
  have hstable : (prefixWord ++ tailWord_7923623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923623).length < 2 ^ (prefixWord ++ tailWord_7923623).sum := by decide
  have hdescent : baseEnd_7923623 < baseStart_7923623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7923690 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_7923690 : Nat := 118140960795 + 7923690 * 2 ^ 59
def prefixEnd_7923690 : Nat := 4983230072969 + 3 ^ 40 * 7923690 * 2
def baseEnd_7923690 : Nat := 4068661527224208760134619

theorem tailTrace_7923690 : CollatzResearch.WordTrace tailWord_7923690 prefixEnd_7923690 4068661527224208760134619 := by
  unfold tailWord_7923690
  simp only [CollatzResearch.WordTrace]
  refine ⟨72250179165957965839674131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192667144442554575572464349 72250179165957965839674131)
  ·
    refine ⟨108375268748936948759511197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72250179165957965839674131 108375268748936948759511197)
    ·
      refine ⟨40640725780851355784816699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108375268748936948759511197 40640725780851355784816699)
      ·
        refine ⟨60961088671277033677225049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40640725780851355784816699 60961088671277033677225049)
        ·
          refine ⟨45720816503457775257918787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60961088671277033677225049 45720816503457775257918787)
          ·
            refine ⟨68581224755186662886878181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45720816503457775257918787 68581224755186662886878181)
            ·
              refine ⟨12858979641597499291289659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68581224755186662886878181 12858979641597499291289659)
              ·
                refine ⟨19288469462396248936934489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12858979641597499291289659 19288469462396248936934489)
                ·
                  refine ⟨14466352096797186702700867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19288469462396248936934489 14466352096797186702700867)
                  ·
                    refine ⟨21699528145195780054051301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14466352096797186702700867 21699528145195780054051301)
                    ·
                      refine ⟨4068661527224208760134619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21699528145195780054051301 4068661527224208760134619)
                      ·
                        rfl

theorem cell23_7923690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_7923690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7923690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7923690 prefixEnd_7923690 := by exact prefixLift 7923690
  have htrace : WordTrace (prefixWord ++ tailWord_7923690) baseStart_7923690 baseEnd_7923690 := by
    simpa [prefixWord, tailWord_7923690, baseEnd_7923690] using wordTrace_append hprefix tailTrace_7923690
  have hstable : (prefixWord ++ tailWord_7923690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7923690).length < 2 ^ (prefixWord ++ tailWord_7923690).sum := by decide
  have hdescent : baseEnd_7923690 < baseStart_7923690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7923690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
