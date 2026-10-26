import V185TrunkScan23Chunk0286

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1697240 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1697240 : Nat := 118140960795 + 1697240 * 2 ^ 59
def prefixEnd_1697240 : Nat := 4983230072969 + 3 ^ 40 * 1697240 * 2
def baseEnd_1697240 : Nat := 871499906037044774394541

theorem tailTrace_1697240 : CollatzResearch.WordTrace tailWord_1697240 prefixEnd_1697240 871499906037044774394541 := by
  unfold tailWord_1697240
  simp only [CollatzResearch.WordTrace]
  refine ⟨30951714185598410179868587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41268952247464546906491449 30951714185598410179868587)
  ·
    refine ⟨46427571278397615269802881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30951714185598410179868587 46427571278397615269802881)
    ·
      refine ⟨34820678458798211452352161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46427571278397615269802881 34820678458798211452352161)
      ·
        refine ⟨26115508844098658589264121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34820678458798211452352161 26115508844098658589264121)
        ·
          refine ⟨19586631633073993941948091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26115508844098658589264121 19586631633073993941948091)
          ·
            refine ⟨29379947449610990912922137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19586631633073993941948091 29379947449610990912922137)
            ·
              refine ⟨22034960587208243184691603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29379947449610990912922137 22034960587208243184691603)
              ·
                refine ⟨33052440880812364777037405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22034960587208243184691603 33052440880812364777037405)
                ·
                  refine ⟨12394665330304636791389027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33052440880812364777037405 12394665330304636791389027)
                  ·
                    refine ⟨18591997995456955187083541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12394665330304636791389027 18591997995456955187083541)
                    ·
                      refine ⟨871499906037044774394541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18591997995456955187083541 871499906037044774394541)
                      ·
                        rfl

theorem cell23_1697240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1697240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697240 prefixEnd_1697240 := by exact prefixLift 1697240
  have htrace : WordTrace (prefixWord ++ tailWord_1697240) baseStart_1697240 baseEnd_1697240 := by
    simpa [prefixWord, tailWord_1697240, baseEnd_1697240] using wordTrace_append hprefix tailTrace_1697240
  have hstable : (prefixWord ++ tailWord_1697240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697240).length < 2 ^ (prefixWord ++ tailWord_1697240).sum := by decide
  have hdescent : baseEnd_1697240 < baseStart_1697240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697247 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 3]
def baseStart_1697247 : Nat := 118140960795 + 1697247 * 2 ^ 59
def prefixEnd_1697247 : Nat := 4983230072969 + 3 ^ 40 * 1697247 * 2
def baseEnd_1697247 : Nat := 871503500401626247007009

theorem tailTrace_1697247 : CollatzResearch.WordTrace tailWord_1697247 prefixEnd_1697247 871503500401626247007009 := by
  unfold tailWord_1697247
  simp only [CollatzResearch.WordTrace]
  refine ⟨61903683682171460555241995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41269122454780973703494663 61903683682171460555241995)
  ·
    refine ⟨92855525523257190832862993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61903683682171460555241995 92855525523257190832862993)
    ·
      refine ⟨69641644142442893124647245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92855525523257190832862993 69641644142442893124647245)
      ·
        refine ⟨26115616553416084921742717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69641644142442893124647245 26115616553416084921742717)
        ·
          refine ⟨9793356207531031845653519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26115616553416084921742717 9793356207531031845653519)
          ·
            refine ⟨14690034311296547768480279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9793356207531031845653519 14690034311296547768480279)
            ·
              refine ⟨22035051466944821652720419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14690034311296547768480279 22035051466944821652720419)
              ·
                refine ⟨33052577200417232479080629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22035051466944821652720419 33052577200417232479080629)
                ·
                  refine ⟨3098679112539115544913809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33052577200417232479080629 3098679112539115544913809)
                  ·
                    refine ⟨2324009334404336658685357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3098679112539115544913809 2324009334404336658685357)
                    ·
                      refine ⟨871503500401626247007009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2324009334404336658685357 871503500401626247007009)
                      ·
                        rfl

theorem cell23_1697247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_1697247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697247 prefixEnd_1697247 := by exact prefixLift 1697247
  have htrace : WordTrace (prefixWord ++ tailWord_1697247) baseStart_1697247 baseEnd_1697247 := by
    simpa [prefixWord, tailWord_1697247, baseEnd_1697247] using wordTrace_append hprefix tailTrace_1697247
  have hstable : (prefixWord ++ tailWord_1697247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697247).length < 2 ^ (prefixWord ++ tailWord_1697247).sum := by decide
  have hdescent : baseEnd_1697247 < baseStart_1697247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697278 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1697278 : Nat := 118140960795 + 1697278 * 2 ^ 59
def prefixEnd_1697278 : Nat := 4983230072969 + 3 ^ 40 * 1697278 * 2
def baseEnd_1697278 : Nat := 871519418301915625719367

theorem tailTrace_1697278 : CollatzResearch.WordTrace tailWord_1697278 prefixEnd_1697278 871519418301915625719367 := by
  unfold tailWord_1697278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7738101793132394106202561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41269876230039435233080325 7738101793132394106202561)
  ·
    refine ⟨5803576344849295579651921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7738101793132394106202561 5803576344849295579651921)
    ·
      refine ⟨4352682258636971684738941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5803576344849295579651921 4352682258636971684738941)
      ·
        refine ⟨1632255846988864381777103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4352682258636971684738941 1632255846988864381777103)
        ·
          refine ⟨2448383770483296572665655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632255846988864381777103 2448383770483296572665655)
          ·
            refine ⟨3672575655724944858998483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448383770483296572665655 3672575655724944858998483)
            ·
              refine ⟨5508863483587417288497725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672575655724944858998483 5508863483587417288497725)
              ·
                refine ⟨2065823806345281483186647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5508863483587417288497725 2065823806345281483186647)
                ·
                  refine ⟨3098735709517922224779971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065823806345281483186647 3098735709517922224779971)
                  ·
                    refine ⟨4648103564276883337169957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3098735709517922224779971 4648103564276883337169957)
                    ·
                      refine ⟨871519418301915625719367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4648103564276883337169957 871519418301915625719367)
                      ·
                        rfl

theorem cell23_1697278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1697278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697278 prefixEnd_1697278 := by exact prefixLift 1697278
  have htrace : WordTrace (prefixWord ++ tailWord_1697278) baseStart_1697278 baseEnd_1697278 := by
    simpa [prefixWord, tailWord_1697278, baseEnd_1697278] using wordTrace_append hprefix tailTrace_1697278
  have hstable : (prefixWord ++ tailWord_1697278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697278).length < 2 ^ (prefixWord ++ tailWord_1697278).sum := by decide
  have hdescent : baseEnd_1697278 < baseStart_1697278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697281 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_1697281 : Nat := 118140960795 + 1697281 * 2 ^ 59
def prefixEnd_1697281 : Nat := 4983230072969 + 3 ^ 40 * 1697281 * 2
def baseEnd_1697281 : Nat := 871520958743879113981853

theorem tailTrace_1697281 : CollatzResearch.WordTrace tailWord_1697281 prefixEnd_1697281 871520958743879113981853 := by
  unfold tailWord_1697281
  simp only [CollatzResearch.WordTrace]
  refine ⟨61904923764048284361979697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41269949176032189574653131 61904923764048284361979697)
  ·
    refine ⟨46428692823036213271484773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61904923764048284361979697 46428692823036213271484773)
    ·
      refine ⟨8705379904319289988403395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46428692823036213271484773 8705379904319289988403395)
      ·
        refine ⟨13058069856478934982605093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8705379904319289988403395 13058069856478934982605093)
        ·
          refine ⟨2448388098089800309238455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13058069856478934982605093 2448388098089800309238455)
          ·
            refine ⟨3672582147134700463857683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448388098089800309238455 3672582147134700463857683)
            ·
              refine ⟨5508873220702050695786525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672582147134700463857683 5508873220702050695786525)
              ·
                refine ⟨2065827457763269010919947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5508873220702050695786525 2065827457763269010919947)
                ·
                  refine ⟨3098741186644903516379921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065827457763269010919947 3098741186644903516379921)
                  ·
                    refine ⟨2324055889983677637284941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3098741186644903516379921 2324055889983677637284941)
                    ·
                      refine ⟨871520958743879113981853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2324055889983677637284941 871520958743879113981853)
                      ·
                        rfl

theorem cell23_1697281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_1697281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697281 prefixEnd_1697281 := by exact prefixLift 1697281
  have htrace : WordTrace (prefixWord ++ tailWord_1697281) baseStart_1697281 baseEnd_1697281 := by
    simpa [prefixWord, tailWord_1697281, baseEnd_1697281] using wordTrace_append hprefix tailTrace_1697281
  have hstable : (prefixWord ++ tailWord_1697281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697281).length < 2 ^ (prefixWord ++ tailWord_1697281).sum := by decide
  have hdescent : baseEnd_1697281 < baseStart_1697281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697337 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1697337 : Nat := 118140960795 + 1697337 * 2 ^ 59
def prefixEnd_1697337 : Nat := 4983230072969 + 3 ^ 40 * 1697337 * 2
def baseEnd_1697337 : Nat := 871549713660530894881595

theorem tailTrace_1697337 : CollatzResearch.WordTrace tailWord_1697337 prefixEnd_1697337 871549713660530894881595 := by
  unfold tailWord_1697337
  simp only [CollatzResearch.WordTrace]
  refine ⟨61906966251845405926018265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41271310834563603950678843 61906966251845405926018265)
  ·
    refine ⟨46430224688884054444513699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61906966251845405926018265 46430224688884054444513699)
    ·
      refine ⟨69645337033326081666770549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46430224688884054444513699 69645337033326081666770549)
      ·
        refine ⟨6529250346874320156259739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69645337033326081666770549 6529250346874320156259739)
        ·
          refine ⟨9793875520311480234389609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529250346874320156259739 9793875520311480234389609)
          ·
            refine ⟨7345406640233610175792207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9793875520311480234389609 7345406640233610175792207)
            ·
              refine ⟨11018109960350415263688311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345406640233610175792207 11018109960350415263688311)
              ·
                refine ⟨16527164940525622895532467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11018109960350415263688311 16527164940525622895532467)
                ·
                  refine ⟨24790747410788434343298701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16527164940525622895532467 24790747410788434343298701)
                  ·
                    refine ⟨9296530279045662878737013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24790747410788434343298701 9296530279045662878737013)
                    ·
                      refine ⟨871549713660530894881595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9296530279045662878737013 871549713660530894881595)
                      ·
                        rfl

theorem cell23_1697337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1697337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697337 prefixEnd_1697337 := by exact prefixLift 1697337
  have htrace : WordTrace (prefixWord ++ tailWord_1697337) baseStart_1697337 baseEnd_1697337 := by
    simpa [prefixWord, tailWord_1697337, baseEnd_1697337] using wordTrace_append hprefix tailTrace_1697337
  have hstable : (prefixWord ++ tailWord_1697337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697337).length < 2 ^ (prefixWord ++ tailWord_1697337).sum := by decide
  have hdescent : baseEnd_1697337 < baseStart_1697337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697438 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1697438 : Nat := 118140960795 + 1697438 * 2 ^ 59
def prefixEnd_1697438 : Nat := 4983230072969 + 3 ^ 40 * 1697438 * 2
def baseEnd_1697438 : Nat := 290533858402211666572877

theorem tailTrace_1697438 : CollatzResearch.WordTrace tailWord_1697438 prefixEnd_1697438 290533858402211666572877 := by
  unfold tailWord_1697438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7738831253059937521930621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41273766682986333450296645 7738831253059937521930621)
  ·
    refine ⟨2902061719897476570723983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7738831253059937521930621 2902061719897476570723983)
    ·
      refine ⟨4353092579846214856085975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902061719897476570723983 4353092579846214856085975)
      ·
        refine ⟨6529638869769322284128963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4353092579846214856085975 6529638869769322284128963)
        ·
          refine ⟨9794458304653983426193445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529638869769322284128963 9794458304653983426193445)
          ·
            refine ⟨1836460932122621892411271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9794458304653983426193445 1836460932122621892411271)
            ·
              refine ⟨2754691398183932838616907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836460932122621892411271 2754691398183932838616907)
              ·
                refine ⟨4132037097275899257925361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754691398183932838616907 4132037097275899257925361)
                ·
                  refine ⟨3099027822956924443444021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4132037097275899257925361 3099027822956924443444021)
                  ·
                    refine ⟨290533858402211666572877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3099027822956924443444021 290533858402211666572877)
                    ·
                      rfl

theorem cell23_1697438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1697438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697438 prefixEnd_1697438 := by exact prefixLift 1697438
  have htrace : WordTrace (prefixWord ++ tailWord_1697438) baseStart_1697438 baseEnd_1697438 := by
    simpa [prefixWord, tailWord_1697438, baseEnd_1697438] using wordTrace_append hprefix tailTrace_1697438
  have hstable : (prefixWord ++ tailWord_1697438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697438).length < 2 ^ (prefixWord ++ tailWord_1697438).sum := by decide
  have hdescent : baseEnd_1697438 < baseStart_1697438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697441 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1697441 : Nat := 118140960795 + 1697441 * 2 ^ 59
def prefixEnd_1697441 : Nat := 4983230072969 + 3 ^ 40 * 1697441 * 2
def baseEnd_1697441 : Nat := 871603115648598487981117

theorem tailTrace_1697441 : CollatzResearch.WordTrace tailWord_1697441 prefixEnd_1697441 871603115648598487981117 := by
  unfold tailWord_1697441
  simp only [CollatzResearch.WordTrace]
  refine ⟨61910759443468631687804177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41273839628979087791869451 61910759443468631687804177)
  ·
    refine ⟨46433069582601473765853133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61910759443468631687804177 46433069582601473765853133)
    ·
      refine ⟨17412401093475552662194925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46433069582601473765853133 17412401093475552662194925)
      ·
        refine ⟨6529650410053332248323097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17412401093475552662194925 6529650410053332248323097)
        ·
          refine ⟨4897237807539999186242323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6529650410053332248323097 4897237807539999186242323)
          ·
            refine ⟨7345856711309998779363485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897237807539999186242323 7345856711309998779363485)
            ·
              refine ⟨2754696266741249542261307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7345856711309998779363485 2754696266741249542261307)
              ·
                refine ⟨4132044400111874313391961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754696266741249542261307 4132044400111874313391961)
                ·
                  refine ⟨3099033300083905735043971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4132044400111874313391961 3099033300083905735043971)
                  ·
                    refine ⟨4648549950125858602565957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3099033300083905735043971 4648549950125858602565957)
                    ·
                      refine ⟨871603115648598487981117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4648549950125858602565957 871603115648598487981117)
                      ·
                        rfl

theorem cell23_1697441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1697441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697441 prefixEnd_1697441 := by exact prefixLift 1697441
  have htrace : WordTrace (prefixWord ++ tailWord_1697441) baseStart_1697441 baseEnd_1697441 := by
    simpa [prefixWord, tailWord_1697441, baseEnd_1697441] using wordTrace_append hprefix tailTrace_1697441
  have hstable : (prefixWord ++ tailWord_1697441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697441).length < 2 ^ (prefixWord ++ tailWord_1697441).sum := by decide
  have hdescent : baseEnd_1697441 < baseStart_1697441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697468 : List Nat := [2, 2, 2, 3, 1, 2, 2, 4, 1, 4]
def baseStart_1697468 : Nat := 118140960795 + 1697468 * 2 ^ 59
def prefixEnd_1697468 : Nat := 4983230072969 + 3 ^ 40 * 1697468 * 2
def baseEnd_1697468 : Nat := 290538993208756627447831

theorem tailTrace_1697468 : CollatzResearch.WordTrace tailWord_1697468 prefixEnd_1697468 290538993208756627447831 := by
  unfold tailWord_1697468
  simp only [CollatzResearch.WordTrace]
  refine ⟨30955872107185407649518529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41274496142913876866024705 30955872107185407649518529)
  ·
    refine ⟨23216904080389055737138897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30955872107185407649518529 23216904080389055737138897)
    ·
      refine ⟨17412678060291791802854173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23216904080389055737138897 17412678060291791802854173)
      ·
        refine ⟨6529754272609421926070315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17412678060291791802854173 6529754272609421926070315)
        ·
          refine ⟨9794631408914132889105473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529754272609421926070315 9794631408914132889105473)
          ·
            refine ⟨7345973556685599666829105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9794631408914132889105473 7345973556685599666829105)
            ·
              refine ⟨5509480167514199750121829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7345973556685599666829105 5509480167514199750121829)
              ·
                refine ⟨1033027531408912453147843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5509480167514199750121829 1033027531408912453147843)
                ·
                  refine ⟨1549541297113368679721765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033027531408912453147843 1549541297113368679721765)
                  ·
                    refine ⟨290538993208756627447831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1549541297113368679721765 290538993208756627447831)
                    ·
                      rfl

theorem cell23_1697468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_1697468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697468 prefixEnd_1697468 := by exact prefixLift 1697468
  have htrace : WordTrace (prefixWord ++ tailWord_1697468) baseStart_1697468 baseEnd_1697468 := by
    simpa [prefixWord, tailWord_1697468, baseEnd_1697468] using wordTrace_append hprefix tailTrace_1697468
  have hstable : (prefixWord ++ tailWord_1697468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697468).length < 2 ^ (prefixWord ++ tailWord_1697468).sum := by decide
  have hdescent : baseEnd_1697468 < baseStart_1697468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697487 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_1697487 : Nat := 118140960795 + 1697487 * 2 ^ 59
def prefixEnd_1697487 : Nat := 4983230072969 + 3 ^ 40 * 1697487 * 2
def baseEnd_1697487 : Nat := 871626735758705308005905

theorem tailTrace_1697487 : CollatzResearch.WordTrace tailWord_1697487 prefixEnd_1697487 871626735758705308005905 := by
  unfold tailWord_1697487
  simp only [CollatzResearch.WordTrace]
  refine ⟨61912437201301981543978715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41274958134201321029319143 61912437201301981543978715)
  ·
    refine ⟨92868655801952972315968073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61912437201301981543978715 92868655801952972315968073)
    ·
      refine ⟨69651491851464729236976055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92868655801952972315968073 69651491851464729236976055)
      ·
        refine ⟨104477237777197093855464083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69651491851464729236976055 104477237777197093855464083)
        ·
          refine ⟨156715856665795640783196125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104477237777197093855464083 156715856665795640783196125)
          ·
            refine ⟨58768446249673365293698547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156715856665795640783196125 58768446249673365293698547)
            ·
              refine ⟨88152669374510047940547821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58768446249673365293698547 88152669374510047940547821)
              ·
                refine ⟨33057251015441267977705433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88152669374510047940547821 33057251015441267977705433)
                ·
                  refine ⟨24792938261580950983279075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33057251015441267977705433 24792938261580950983279075)
                  ·
                    refine ⟨37189407392371426474918613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24792938261580950983279075 37189407392371426474918613)
                    ·
                      refine ⟨871626735758705308005905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37189407392371426474918613 871626735758705308005905)
                      ·
                        rfl

theorem cell23_1697487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_1697487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697487 prefixEnd_1697487 := by exact prefixLift 1697487
  have htrace : WordTrace (prefixWord ++ tailWord_1697487) baseStart_1697487 baseEnd_1697487 := by
    simpa [prefixWord, tailWord_1697487, baseEnd_1697487] using wordTrace_append hprefix tailTrace_1697487
  have hstable : (prefixWord ++ tailWord_1697487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697487).length < 2 ^ (prefixWord ++ tailWord_1697487).sum := by decide
  have hdescent : baseEnd_1697487 < baseStart_1697487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697518 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_1697518 : Nat := 118140960795 + 1697518 * 2 ^ 59
def prefixEnd_1697518 : Nat := 4983230072969 + 3 ^ 40 * 1697518 * 2
def baseEnd_1697518 : Nat := 871642653658994686718263

theorem tailTrace_1697518 : CollatzResearch.WordTrace tailWord_1697518 prefixEnd_1697518 871642653658994686718263 := by
  unfold tailWord_1697518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7739195983023709229794651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41275711909459782558904805 7739195983023709229794651)
  ·
    refine ⟨11608793974535563844691977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7739195983023709229794651 11608793974535563844691977)
    ·
      refine ⟨8706595480901672883518983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11608793974535563844691977 8706595480901672883518983)
      ·
        refine ⟨13059893221352509325278475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8706595480901672883518983 13059893221352509325278475)
        ·
          refine ⟨19589839832028763987917713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13059893221352509325278475 19589839832028763987917713)
          ·
            refine ⟨14692379874021572990938285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19589839832028763987917713 14692379874021572990938285)
            ·
              refine ⟨5509642452758089871601857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14692379874021572990938285 5509642452758089871601857)
              ·
                refine ⟨4132231839568567403701393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5509642452758089871601857 4132231839568567403701393)
                ·
                  refine ⟨3099173879676425552776045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4132231839568567403701393 3099173879676425552776045)
                  ·
                    refine ⟨1162190204878659582291017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3099173879676425552776045 1162190204878659582291017)
                    ·
                      refine ⟨871642653658994686718263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162190204878659582291017 871642653658994686718263)
                      ·
                        rfl

theorem cell23_1697518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_1697518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697518 prefixEnd_1697518 := by exact prefixLift 1697518
  have htrace : WordTrace (prefixWord ++ tailWord_1697518) baseStart_1697518 baseEnd_1697518 := by
    simpa [prefixWord, tailWord_1697518, baseEnd_1697518] using wordTrace_append hprefix tailTrace_1697518
  have hstable : (prefixWord ++ tailWord_1697518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697518).length < 2 ^ (prefixWord ++ tailWord_1697518).sum := by decide
  have hdescent : baseEnd_1697518 < baseStart_1697518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697544 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1697544 : Nat := 118140960795 + 1697544 * 2 ^ 59
def prefixEnd_1697544 : Nat := 4983230072969 + 3 ^ 40 * 1697544 * 2
def baseEnd_1697544 : Nat := 871656004156011584993143

theorem tailTrace_1697544 : CollatzResearch.WordTrace tailWord_1697544 prefixEnd_1697544 871656004156011584993143 := by
  unfold tailWord_1697544
  simp only [CollatzResearch.WordTrace]
  refine ⟨30957258081047740139401843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41276344108063653519202457 30957258081047740139401843)
  ·
    refine ⟨46435887121571610209102765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30957258081047740139401843 46435887121571610209102765)
    ·
      refine ⟨17413457670589353828413537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46435887121571610209102765 17413457670589353828413537)
      ·
        refine ⟨13060093252942015371310153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17413457670589353828413537 13060093252942015371310153)
        ·
          refine ⟨9795069939706511528482615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13060093252942015371310153 9795069939706511528482615)
          ·
            refine ⟨14692604909559767292723923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9795069939706511528482615 14692604909559767292723923)
            ·
              refine ⟨22038907364339650939085885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14692604909559767292723923 22038907364339650939085885)
              ·
                refine ⟨8264590261627369102157207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22038907364339650939085885 8264590261627369102157207)
                ·
                  refine ⟨12396885392441053653235811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8264590261627369102157207 12396885392441053653235811)
                  ·
                    refine ⟨18595328088661580479853717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12396885392441053653235811 18595328088661580479853717)
                    ·
                      refine ⟨871656004156011584993143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18595328088661580479853717 871656004156011584993143)
                      ·
                        rfl

theorem cell23_1697544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1697544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697544 prefixEnd_1697544 := by exact prefixLift 1697544
  have htrace : WordTrace (prefixWord ++ tailWord_1697544) baseStart_1697544 baseEnd_1697544 := by
    simpa [prefixWord, tailWord_1697544, baseEnd_1697544] using wordTrace_append hprefix tailTrace_1697544
  have hstable : (prefixWord ++ tailWord_1697544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697544).length < 2 ^ (prefixWord ++ tailWord_1697544).sum := by decide
  have hdescent : baseEnd_1697544 < baseStart_1697544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697548 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 3, 2, 2]
def baseStart_1697548 : Nat := 118140960795 + 1697548 * 2 ^ 59
def prefixEnd_1697548 : Nat := 4983230072969 + 3 ^ 40 * 1697548 * 2
def baseEnd_1697548 : Nat := 871658058078629569343125

theorem tailTrace_1697548 : CollatzResearch.WordTrace tailWord_1697548 prefixEnd_1697548 871658058078629569343125 := by
  unfold tailWord_1697548
  simp only [CollatzResearch.WordTrace]
  refine ⟨30957331027040494480974649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41276441369387325974632865 30957331027040494480974649)
  ·
    refine ⟨23217998270280370860730987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30957331027040494480974649 23217998270280370860730987)
    ·
      refine ⟨34826997405420556291096481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23217998270280370860730987 34826997405420556291096481)
      ·
        refine ⟨26120248054065417218322361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34826997405420556291096481 26120248054065417218322361)
        ·
          refine ⟨19590186040549062913741771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26120248054065417218322361 19590186040549062913741771)
          ·
            refine ⟨29385279060823594370612657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19590186040549062913741771 29385279060823594370612657)
            ·
              refine ⟨22038959295617695777959493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29385279060823594370612657 22038959295617695777959493)
              ·
                refine ⟨4132304867928317958367405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22038959295617695777959493 4132304867928317958367405)
                ·
                  refine ⟨1549614325473119234387777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4132304867928317958367405 1549614325473119234387777)
                  ·
                    refine ⟨1162210744104839425790833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1549614325473119234387777 1162210744104839425790833)
                    ·
                      refine ⟨871658058078629569343125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162210744104839425790833 871658058078629569343125)
                      ·
                        rfl

theorem cell23_1697548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_1697548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697548 prefixEnd_1697548 := by exact prefixLift 1697548
  have htrace : WordTrace (prefixWord ++ tailWord_1697548) baseStart_1697548 baseEnd_1697548 := by
    simpa [prefixWord, tailWord_1697548, baseEnd_1697548] using wordTrace_append hprefix tailTrace_1697548
  have hstable : (prefixWord ++ tailWord_1697548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697548).length < 2 ^ (prefixWord ++ tailWord_1697548).sum := by decide
  have hdescent : baseEnd_1697548 < baseStart_1697548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697551 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 1, 2, 3]
def baseStart_1697551 : Nat := 118140960795 + 1697551 * 2 ^ 59
def prefixEnd_1697551 : Nat := 4983230072969 + 3 ^ 40 * 1697551 * 2
def baseEnd_1697551 : Nat := 871659598520593057605611

theorem tailTrace_1697551 : CollatzResearch.WordTrace tailWord_1697551 prefixEnd_1697551 871659598520593057605611 := by
  unfold tailWord_1697551
  simp only [CollatzResearch.WordTrace]
  refine ⟨61914771473070120474308507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41276514315380080316205671 61914771473070120474308507)
  ·
    refine ⟨92872157209605180711462761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61914771473070120474308507 92872157209605180711462761)
    ·
      refine ⟨69654117907203885533597071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92872157209605180711462761 69654117907203885533597071)
      ·
        refine ⟨104481176860805828300395607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69654117907203885533597071 104481176860805828300395607)
        ·
          refine ⟨156721765291208742450593411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104481176860805828300395607 156721765291208742450593411)
          ·
            refine ⟨235082647936813113675890117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156721765291208742450593411 235082647936813113675890117)
            ·
              refine ⟨44077996488152458814229397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235082647936813113675890117 44077996488152458814229397)
              ·
                refine ⟨2066156085382146506917003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44077996488152458814229397 2066156085382146506917003)
                ·
                  refine ⟨3099234128073219760375505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066156085382146506917003 3099234128073219760375505)
                  ·
                    refine ⟨2324425596054914820281629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3099234128073219760375505 2324425596054914820281629)
                    ·
                      refine ⟨871659598520593057605611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2324425596054914820281629 871659598520593057605611)
                      ·
                        rfl

theorem cell23_1697551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 2, 3].length) (baseStart_1697551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697551 prefixEnd_1697551 := by exact prefixLift 1697551
  have htrace : WordTrace (prefixWord ++ tailWord_1697551) baseStart_1697551 baseEnd_1697551 := by
    simpa [prefixWord, tailWord_1697551, baseEnd_1697551] using wordTrace_append hprefix tailTrace_1697551
  have hstable : (prefixWord ++ tailWord_1697551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697551).length < 2 ^ (prefixWord ++ tailWord_1697551).sum := by decide
  have hdescent : baseEnd_1697551 < baseStart_1697551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697588 : List Nat := [2, 5, 1, 1, 2, 3, 1, 8]
def baseStart_1697588 : Nat := 118140960795 + 1697588 * 2 ^ 59
def prefixEnd_1697588 : Nat := 4983230072969 + 3 ^ 40 * 1697588 * 2
def baseEnd_1697588 : Nat := 32284392492770718994183

theorem tailTrace_1697588 : CollatzResearch.WordTrace tailWord_1697588 prefixEnd_1697588 32284392492770718994183 := by
  unfold tailWord_1697588
  simp only [CollatzResearch.WordTrace]
  refine ⟨30958060486968037896702709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41277413982624050528936945 30958060486968037896702709)
  ·
    refine ⟨2902318170653253552815879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30958060486968037896702709 2902318170653253552815879)
    ·
      refine ⟨4353477255979880329223819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902318170653253552815879 4353477255979880329223819)
      ·
        refine ⟨6530215883969820493835729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4353477255979880329223819 6530215883969820493835729)
        ·
          refine ⟨4897661912977365370376797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6530215883969820493835729 4897661912977365370376797)
          ·
            refine ⟨1836623217366512013891299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4897661912977365370376797 1836623217366512013891299)
            ·
              refine ⟨2754934826049768020836949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836623217366512013891299 2754934826049768020836949)
              ·
                refine ⟨32284392492770718994183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2754934826049768020836949 32284392492770718994183)
                ·
                  rfl

theorem cell23_1697588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 8].length) (baseStart_1697588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697588 prefixEnd_1697588 := by exact prefixLift 1697588
  have htrace : WordTrace (prefixWord ++ tailWord_1697588) baseStart_1697588 baseEnd_1697588 := by
    simpa [prefixWord, tailWord_1697588, baseEnd_1697588] using wordTrace_append hprefix tailTrace_1697588
  have hstable : (prefixWord ++ tailWord_1697588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697588).length < 2 ^ (prefixWord ++ tailWord_1697588).sum := by decide
  have hdescent : baseEnd_1697588 < baseStart_1697588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697598 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1697598 : Nat := 118140960795 + 1697598 * 2 ^ 59
def prefixEnd_1697598 : Nat := 4983230072969 + 3 ^ 40 * 1697598 * 2
def baseEnd_1697598 : Nat := 871683732111354373717895

theorem tailTrace_1697598 : CollatzResearch.WordTrace tailWord_1697598 prefixEnd_1697598 871683732111354373717895 := by
  unfold tailWord_1697598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7739560712987480937658681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41277657135933231667512965 7739560712987480937658681)
  ·
    refine ⟨5804670534740610703244011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7739560712987480937658681 5804670534740610703244011)
    ·
      refine ⟨8707005802110916054866017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5804670534740610703244011 8707005802110916054866017)
      ·
        refine ⟨6530254351583187041149513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8707005802110916054866017 6530254351583187041149513)
        ·
          refine ⟨4897690763687390280862135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6530254351583187041149513 4897690763687390280862135)
          ·
            refine ⟨7346536145531085421293203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897690763687390280862135 7346536145531085421293203)
            ·
              refine ⟨11019804218296628131939805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7346536145531085421293203 11019804218296628131939805)
              ·
                refine ⟨4132426581861235549477427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11019804218296628131939805 4132426581861235549477427)
                ·
                  refine ⟨6198639872791853324216141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4132426581861235549477427 6198639872791853324216141)
                  ·
                    refine ⟨2324489952296944996581053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6198639872791853324216141 2324489952296944996581053)
                    ·
                      refine ⟨871683732111354373717895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2324489952296944996581053 871683732111354373717895)
                      ·
                        rfl

theorem cell23_1697598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1697598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697598 prefixEnd_1697598 := by exact prefixLift 1697598
  have htrace : WordTrace (prefixWord ++ tailWord_1697598) baseStart_1697598 baseEnd_1697598 := by
    simpa [prefixWord, tailWord_1697598, baseEnd_1697598] using wordTrace_append hprefix tailTrace_1697598
  have hstable : (prefixWord ++ tailWord_1697598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697598).length < 2 ^ (prefixWord ++ tailWord_1697598).sum := by decide
  have hdescent : baseEnd_1697598 < baseStart_1697598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697608 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 3, 3, 2]
def baseStart_1697608 : Nat := 118140960795 + 1697608 * 2 ^ 59
def prefixEnd_1697608 : Nat := 4983230072969 + 3 ^ 40 * 1697608 * 2
def baseEnd_1697608 : Nat := 871688866917899334592849

theorem tailTrace_1697608 : CollatzResearch.WordTrace tailWord_1697608 prefixEnd_1697608 871688866917899334592849 := by
  unfold tailWord_1697608
  simp only [CollatzResearch.WordTrace]
  refine ⟨30958425216931809604566739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41277900289242412806088985 30958425216931809604566739)
  ·
    refine ⟨46437637825397714406850109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30958425216931809604566739 46437637825397714406850109)
    ·
      refine ⟨17414114184524142902568791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46437637825397714406850109 17414114184524142902568791)
      ·
        refine ⟨26121171276786214353853187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17414114184524142902568791 26121171276786214353853187)
        ·
          refine ⟨39181756915179321530779781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26121171276786214353853187 39181756915179321530779781)
          ·
            refine ⟨7346579421596122787021209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39181756915179321530779781 7346579421596122787021209)
            ·
              refine ⟨5509934566197092090265907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7346579421596122787021209 5509934566197092090265907)
              ·
                refine ⟨8264901849295638135398861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5509934566197092090265907 8264901849295638135398861)
                ·
                  refine ⟨3099338193485864300774573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8264901849295638135398861 3099338193485864300774573)
                  ·
                    refine ⟨1162251822557199112790465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3099338193485864300774573 1162251822557199112790465)
                    ·
                      refine ⟨871688866917899334592849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162251822557199112790465 871688866917899334592849)
                      ·
                        rfl

theorem cell23_1697608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_1697608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697608 prefixEnd_1697608 := by exact prefixLift 1697608
  have htrace : WordTrace (prefixWord ++ tailWord_1697608) baseStart_1697608 baseEnd_1697608 := by
    simpa [prefixWord, tailWord_1697608, baseEnd_1697608] using wordTrace_append hprefix tailTrace_1697608
  have hstable : (prefixWord ++ tailWord_1697608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697608).length < 2 ^ (prefixWord ++ tailWord_1697608).sum := by decide
  have hdescent : baseEnd_1697608 < baseStart_1697608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697695 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 7]
def baseStart_1697695 : Nat := 118140960795 + 1697695 * 2 ^ 59
def prefixEnd_1697695 : Nat := 4983230072969 + 3 ^ 40 * 1697695 * 2
def baseEnd_1697695 : Nat := 96859282192760054911661

theorem tailTrace_1697695 : CollatzResearch.WordTrace tailWord_1697695 prefixEnd_1697695 96859282192760054911661 := by
  unfold tailWord_1697695
  simp only [CollatzResearch.WordTrace]
  refine ⟨61920023584548433067550539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41280015723032288711700359 61920023584548433067550539)
  ·
    refine ⟨92880035376822649601325809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61920023584548433067550539 92880035376822649601325809)
    ·
      refine ⟨69660026532616987200994357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92880035376822649601325809 69660026532616987200994357)
      ·
        refine ⟨6530627487432842550093221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69660026532616987200994357 6530627487432842550093221)
        ·
          refine ⟨1224492653893657978142479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6530627487432842550093221 1224492653893657978142479)
          ·
            refine ⟨1836738980840486967213719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224492653893657978142479 1836738980840486967213719)
            ·
              refine ⟨2755108471260730450820579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836738980840486967213719 2755108471260730450820579)
              ·
                refine ⟨4132662706891095676230869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755108471260730450820579 4132662706891095676230869)
                ·
                  refine ⟨96859282192760054911661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4132662706891095676230869 96859282192760054911661)
                  ·
                    rfl

theorem cell23_1697695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 7].length) (baseStart_1697695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697695 prefixEnd_1697695 := by exact prefixLift 1697695
  have htrace : WordTrace (prefixWord ++ tailWord_1697695) baseStart_1697695 baseEnd_1697695 := by
    simpa [prefixWord, tailWord_1697695, baseEnd_1697695] using wordTrace_append hprefix tailTrace_1697695
  have hstable : (prefixWord ++ tailWord_1697695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697695).length < 2 ^ (prefixWord ++ tailWord_1697695).sum := by decide
  have hdescent : baseEnd_1697695 < baseStart_1697695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697711 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 4]
def baseStart_1697711 : Nat := 118140960795 + 1697711 * 2 ^ 59
def prefixEnd_1697711 : Nat := 4983230072969 + 3 ^ 40 * 1697711 * 2
def baseEnd_1697711 : Nat := 871741755425312431604875

theorem tailTrace_1697711 : CollatzResearch.WordTrace tailWord_1697711 prefixEnd_1697711 871741755425312431604875 := by
  unfold tailWord_1697711
  simp only [CollatzResearch.WordTrace]
  refine ⟨61920607152490467800132987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41280404768326978533421991 61920607152490467800132987)
  ·
    refine ⟨92880910728735701700199481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61920607152490467800132987 92880910728735701700199481)
    ·
      refine ⟨69660683046551776275149611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92880910728735701700199481 69660683046551776275149611)
      ·
        refine ⟨104491024569827664412724417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69660683046551776275149611 104491024569827664412724417)
        ·
          refine ⟨78368268427370748309543313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104491024569827664412724417 78368268427370748309543313)
          ·
            refine ⟨58776201320528061232157485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78368268427370748309543313 58776201320528061232157485)
            ·
              refine ⟨22041075495198022962059057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58776201320528061232157485 22041075495198022962059057)
              ·
                refine ⟨16530806621398517221544293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22041075495198022962059057 16530806621398517221544293)
                ·
                  refine ⟨3099526241512221979039555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16530806621398517221544293 3099526241512221979039555)
                  ·
                    refine ⟨4649289362268332968559333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3099526241512221979039555 4649289362268332968559333)
                    ·
                      refine ⟨871741755425312431604875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4649289362268332968559333 871741755425312431604875)
                      ·
                        rfl

theorem cell23_1697711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_1697711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697711 prefixEnd_1697711 := by exact prefixLift 1697711
  have htrace : WordTrace (prefixWord ++ tailWord_1697711) baseStart_1697711 baseEnd_1697711 := by
    simpa [prefixWord, tailWord_1697711, baseEnd_1697711] using wordTrace_append hprefix tailTrace_1697711
  have hstable : (prefixWord ++ tailWord_1697711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697711).length < 2 ^ (prefixWord ++ tailWord_1697711).sum := by decide
  have hdescent : baseEnd_1697711 < baseStart_1697711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697728 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 4]
def baseStart_1697728 : Nat := 118140960795 + 1697728 * 2 ^ 59
def prefixEnd_1697728 : Nat := 4983230072969 + 3 ^ 40 * 1697728 * 2
def baseEnd_1697728 : Nat := 871750484596438865092297

theorem tailTrace_1697728 : CollatzResearch.WordTrace tailWord_1697728 prefixEnd_1697728 871750484596438865092297 := by
  unfold tailWord_1697728
  simp only [CollatzResearch.WordTrace]
  refine ⟨30960613596714439851750919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41280818128952586469001225 30960613596714439851750919)
  ·
    refine ⟨46440920395071659777626379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30960613596714439851750919 46440920395071659777626379)
    ·
      refine ⟨69661380592607489666439569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46440920395071659777626379 69661380592607489666439569)
      ·
        refine ⟨52246035444455617249829677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69661380592607489666439569 52246035444455617249829677)
        ·
          refine ⟨19592263291670856468686129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52246035444455617249829677 19592263291670856468686129)
          ·
            refine ⟨14694197468753142351514597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19592263291670856468686129 14694197468753142351514597)
            ·
              refine ⟨2755162025391214190908987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14694197468753142351514597 2755162025391214190908987)
              ·
                refine ⟨4132743038086821286363481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755162025391214190908987 4132743038086821286363481)
                ·
                  refine ⟨3099557278565115964772611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4132743038086821286363481 3099557278565115964772611)
                  ·
                    refine ⟨4649335917847673947158917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3099557278565115964772611 4649335917847673947158917)
                    ·
                      refine ⟨871750484596438865092297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4649335917847673947158917 871750484596438865092297)
                      ·
                        rfl

theorem cell23_1697728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_1697728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697728 prefixEnd_1697728 := by exact prefixLift 1697728
  have htrace : WordTrace (prefixWord ++ tailWord_1697728) baseStart_1697728 baseEnd_1697728 := by
    simpa [prefixWord, tailWord_1697728, baseEnd_1697728] using wordTrace_append hprefix tailTrace_1697728
  have hstable : (prefixWord ++ tailWord_1697728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697728).length < 2 ^ (prefixWord ++ tailWord_1697728).sum := by decide
  have hdescent : baseEnd_1697728 < baseStart_1697728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697802 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 6]
def baseStart_1697802 : Nat := 118140960795 + 1697802 * 2 ^ 59
def prefixEnd_1697802 : Nat := 4983230072969 + 3 ^ 40 * 1697802 * 2
def baseEnd_1697802 : Nat := 96865386907207952840773

theorem tailTrace_1697802 : CollatzResearch.WordTrace tailWord_1697802 prefixEnd_1697802 96865386907207952840773 := by
  unfold tailWord_1697802
  simp only [CollatzResearch.WordTrace]
  refine ⟨15480981548790197585423915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41282617463440526894463773 15480981548790197585423915)
  ·
    refine ⟨23221472323185296378135873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15480981548790197585423915 23221472323185296378135873)
    ·
      refine ⟨17416104242388972283601905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23221472323185296378135873 17416104242388972283601905)
      ·
        refine ⟨13062078181791729212701429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17416104242388972283601905 13062078181791729212701429)
        ·
          refine ⟨1224569829542974613690759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13062078181791729212701429 1224569829542974613690759)
          ·
            refine ⟨1836854744314461920536139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224569829542974613690759 1836854744314461920536139)
            ·
              refine ⟨2755282116471692880804209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836854744314461920536139 2755282116471692880804209)
              ·
                refine ⟨2066461587353769660603157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2755282116471692880804209 2066461587353769660603157)
                ·
                  refine ⟨96865386907207952840773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2066461587353769660603157 96865386907207952840773)
                  ·
                    rfl

theorem cell23_1697802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_1697802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697802 prefixEnd_1697802 := by exact prefixLift 1697802
  have htrace : WordTrace (prefixWord ++ tailWord_1697802) baseStart_1697802 baseEnd_1697802 := by
    simpa [prefixWord, tailWord_1697802, baseEnd_1697802] using wordTrace_append hprefix tailTrace_1697802
  have hstable : (prefixWord ++ tailWord_1697802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697802).length < 2 ^ (prefixWord ++ tailWord_1697802).sum := by decide
  have hdescent : baseEnd_1697802 < baseStart_1697802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697811 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 3, 6]
def baseStart_1697811 : Nat := 118140960795 + 1697811 * 2 ^ 59
def prefixEnd_1697811 : Nat := 4983230072969 + 3 ^ 40 * 1697811 * 2
def baseEnd_1697811 : Nat := 290597701163587346784805

theorem tailTrace_1697811 : CollatzResearch.WordTrace tailWord_1697811 prefixEnd_1697811 290597701163587346784805 := by
  unfold tailWord_1697811
  simp only [CollatzResearch.WordTrace]
  refine ⟨61924254452128184878773287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41282836301418789919182191 61924254452128184878773287)
  ·
    refine ⟨92886381678192277318159931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61924254452128184878773287 92886381678192277318159931)
    ·
      refine ⟨139329572517288415977239897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92886381678192277318159931 139329572517288415977239897)
      ·
        refine ⟨104497179387966311982929923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139329572517288415977239897 104497179387966311982929923)
        ·
          refine ⟨156745769081949467974394885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104497179387966311982929923 156745769081949467974394885)
          ·
            refine ⟨29389831702865525245199041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156745769081949467974394885 29389831702865525245199041)
            ·
              refine ⟨22042373777149143933899281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29389831702865525245199041 22042373777149143933899281)
              ·
                refine ⟨16531780332861857950424461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22042373777149143933899281 16531780332861857950424461)
                ·
                  refine ⟨6199417624823196731409173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16531780332861857950424461 6199417624823196731409173)
                  ·
                    refine ⟨290597701163587346784805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6199417624823196731409173 290597701163587346784805)
                    ·
                      rfl

theorem cell23_1697811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 6].length) (baseStart_1697811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697811 prefixEnd_1697811 := by exact prefixLift 1697811
  have htrace : WordTrace (prefixWord ++ tailWord_1697811) baseStart_1697811 baseEnd_1697811 := by
    simpa [prefixWord, tailWord_1697811, baseEnd_1697811] using wordTrace_append hprefix tailTrace_1697811
  have hstable : (prefixWord ++ tailWord_1697811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697811).length < 2 ^ (prefixWord ++ tailWord_1697811).sum := by decide
  have hdescent : baseEnd_1697811 < baseStart_1697811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697835 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 5, 2, 2]
def baseStart_1697835 : Nat := 118140960795 + 1697835 * 2 ^ 59
def prefixEnd_1697835 : Nat := 4983230072969 + 3 ^ 40 * 1697835 * 2
def baseEnd_1697835 : Nat := 871805427026469946454305

theorem tailTrace_1697835 : CollatzResearch.WordTrace tailWord_1697835 prefixEnd_1697835 871805427026469946454305 := by
  unfold tailWord_1697835
  simp only [CollatzResearch.WordTrace]
  refine ⟨61925129804041236977646959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41283419869360824651764639 61925129804041236977646959)
  ·
    refine ⟨92887694706061855466470439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61925129804041236977646959 92887694706061855466470439)
    ·
      refine ⟨139331542059092783199705659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92887694706061855466470439 139331542059092783199705659)
      ·
        refine ⟨208997313088639174799558489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139331542059092783199705659 208997313088639174799558489)
        ·
          refine ⟨156747984816479381099668867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208997313088639174799558489 156747984816479381099668867)
          ·
            refine ⟨235121977224719071649503301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156747984816479381099668867 235121977224719071649503301)
            ·
              refine ⟨44085370729634825934281869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235121977224719071649503301 44085370729634825934281869)
              ·
                refine ⟨16532014023613059725355701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44085370729634825934281869 16532014023613059725355701)
                ·
                  refine ⟨1549876314713724349252097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16532014023613059725355701 1549876314713724349252097)
                  ·
                    refine ⟨1162407236035293261939073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1549876314713724349252097 1162407236035293261939073)
                    ·
                      refine ⟨871805427026469946454305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162407236035293261939073 871805427026469946454305)
                      ·
                        rfl

theorem cell23_1697835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 2, 2].length) (baseStart_1697835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697835 prefixEnd_1697835 := by exact prefixLift 1697835
  have htrace : WordTrace (prefixWord ++ tailWord_1697835) baseStart_1697835 baseEnd_1697835 := by
    simpa [prefixWord, tailWord_1697835, baseEnd_1697835] using wordTrace_append hprefix tailTrace_1697835
  have hstable : (prefixWord ++ tailWord_1697835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697835).length < 2 ^ (prefixWord ++ tailWord_1697835).sum := by decide
  have hdescent : baseEnd_1697835 < baseStart_1697835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697855 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 1, 2, 3]
def baseStart_1697855 : Nat := 118140960795 + 1697855 * 2 ^ 59
def prefixEnd_1697855 : Nat := 4983230072969 + 3 ^ 40 * 1697855 * 2
def baseEnd_1697855 : Nat := 871815696639559868204213

theorem tailTrace_1697855 : CollatzResearch.WordTrace tailWord_1697855 prefixEnd_1697855 871815696639559868204213 := by
  unfold tailWord_1697855
  simp only [CollatzResearch.WordTrace]
  refine ⟨61925859263968780393375019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41283906175979186928916679 61925859263968780393375019)
  ·
    refine ⟨92888788895953170590062529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61925859263968780393375019 92888788895953170590062529)
    ·
      refine ⟨69666591671964877942546897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92888788895953170590062529 69666591671964877942546897)
      ·
        refine ⟨52249943753973658456910173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69666591671964877942546897 52249943753973658456910173)
        ·
          refine ⟨19593728907740121921341315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52249943753973658456910173 19593728907740121921341315)
          ·
            refine ⟨29390593361610182882011973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19593728907740121921341315 29390593361610182882011973)
            ·
              refine ⟨5510736255301909290377245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29390593361610182882011973 5510736255301909290377245)
              ·
                refine ⟨2066526095738215983891467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5510736255301909290377245 2066526095738215983891467)
                ·
                  refine ⟨3099789143607323975837201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066526095738215983891467 3099789143607323975837201)
                  ·
                    refine ⟨2324841857705492981877901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3099789143607323975837201 2324841857705492981877901)
                    ·
                      refine ⟨871815696639559868204213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2324841857705492981877901 871815696639559868204213)
                      ·
                        rfl

theorem cell23_1697855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_1697855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697855 prefixEnd_1697855 := by exact prefixLift 1697855
  have htrace : WordTrace (prefixWord ++ tailWord_1697855) baseStart_1697855 baseEnd_1697855 := by
    simpa [prefixWord, tailWord_1697855, baseEnd_1697855] using wordTrace_append hprefix tailTrace_1697855
  have hstable : (prefixWord ++ tailWord_1697855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697855).length < 2 ^ (prefixWord ++ tailWord_1697855).sum := by decide
  have hdescent : baseEnd_1697855 < baseStart_1697855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697862 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1697862 : Nat := 118140960795 + 1697862 * 2 ^ 59
def prefixEnd_1697862 : Nat := 4983230072969 + 3 ^ 40 * 1697862 * 2
def baseEnd_1697862 : Nat := 290606430334713780272227

theorem tailTrace_1697862 : CollatzResearch.WordTrace tailWord_1697862 prefixEnd_1697862 290606430334713780272227 := by
  unfold tailWord_1697862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935191080466981893402495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41284076383295613725919893 1935191080466981893402495)
  ·
    refine ⟨2902786620700472840103743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935191080466981893402495 2902786620700472840103743)
    ·
      refine ⟨4354179931050709260155615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902786620700472840103743 4354179931050709260155615)
      ·
        refine ⟨6531269896576063890233423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4354179931050709260155615 6531269896576063890233423)
        ·
          refine ⟨9796904844864095835350135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6531269896576063890233423 9796904844864095835350135)
          ·
            refine ⟨14695357267296143753025203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9796904844864095835350135 14695357267296143753025203)
            ·
              refine ⟨22043035900944215629537805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14695357267296143753025203 22043035900944215629537805)
              ·
                refine ⟨8266138462854080861076677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22043035900944215629537805 8266138462854080861076677)
                ·
                  refine ⟨1549900961785140161451877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8266138462854080861076677 1549900961785140161451877)
                  ·
                    refine ⟨290606430334713780272227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1549900961785140161451877 290606430334713780272227)
                    ·
                      rfl

theorem cell23_1697862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1697862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697862 prefixEnd_1697862 := by exact prefixLift 1697862
  have htrace : WordTrace (prefixWord ++ tailWord_1697862) baseStart_1697862 baseEnd_1697862 := by
    simpa [prefixWord, tailWord_1697862, baseEnd_1697862] using wordTrace_append hprefix tailTrace_1697862
  have hstable : (prefixWord ++ tailWord_1697862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697862).length < 2 ^ (prefixWord ++ tailWord_1697862).sum := by decide
  have hdescent : baseEnd_1697862 < baseStart_1697862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697871 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 1, 9]
def baseStart_1697871 : Nat := 118140960795 + 1697871 * 2 ^ 59
def prefixEnd_1697871 : Nat := 4983230072969 + 3 ^ 40 * 1697871 * 2
def baseEnd_1697871 : Nat := 290607970776677268534713

theorem tailTrace_1697871 : CollatzResearch.WordTrace tailWord_1697871 prefixEnd_1697871 290607970776677268534713 := by
  unfold tailWord_1697871
  simp only [CollatzResearch.WordTrace]
  refine ⟨61926442831910815125957467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41284295221273876750638311 61926442831910815125957467)
  ·
    refine ⟨92889664247866222688936201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61926442831910815125957467 92889664247866222688936201)
    ·
      refine ⟨69667248185899667016702151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92889664247866222688936201 69667248185899667016702151)
      ·
        refine ⟨104500872278849500525053227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69667248185899667016702151 104500872278849500525053227)
        ·
          refine ⟨156751308418274250787579841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104500872278849500525053227 156751308418274250787579841)
          ·
            refine ⟨117563481313705688090684881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156751308418274250787579841 117563481313705688090684881)
            ·
              refine ⟨88172610985279266068013661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117563481313705688090684881 88172610985279266068013661)
              ·
                refine ⟨33064729119479724775505123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88172610985279266068013661 33064729119479724775505123)
                ·
                  refine ⟨49597093679219587163257685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33064729119479724775505123 49597093679219587163257685)
                  ·
                    refine ⟨290607970776677268534713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 49597093679219587163257685 290607970776677268534713)
                    ·
                      rfl

theorem cell23_1697871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_1697871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697871 prefixEnd_1697871 := by exact prefixLift 1697871
  have htrace : WordTrace (prefixWord ++ tailWord_1697871) baseStart_1697871 baseEnd_1697871 := by
    simpa [prefixWord, tailWord_1697871, baseEnd_1697871] using wordTrace_append hprefix tailTrace_1697871
  have hstable : (prefixWord ++ tailWord_1697871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697871).length < 2 ^ (prefixWord ++ tailWord_1697871).sum := by decide
  have hdescent : baseEnd_1697871 < baseStart_1697871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697975 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 3]
def baseStart_1697975 : Nat := 118140960795 + 1697975 * 2 ^ 59
def prefixEnd_1697975 : Nat := 4983230072969 + 3 ^ 40 * 1697975 * 2
def baseEnd_1697975 : Nat := 871877314318099398703661

theorem tailTrace_1697975 : CollatzResearch.WordTrace tailWord_1697975 prefixEnd_1697975 871877314318099398703661 := by
  unfold tailWord_1697975
  simp only [CollatzResearch.WordTrace]
  refine ⟨61930236023534040887743379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41286824015689360591828919 61930236023534040887743379)
  ·
    refine ⟨92895354035301061331615069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61930236023534040887743379 92895354035301061331615069)
    ·
      refine ⟨34835757763237897999355651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92895354035301061331615069 34835757763237897999355651)
      ·
        refine ⟨52253636644856846999033477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34835757763237897999355651 52253636644856846999033477)
        ·
          refine ⟨9797556870910658812318777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52253636644856846999033477 9797556870910658812318777)
          ·
            refine ⟨7348167653182994109239083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9797556870910658812318777 7348167653182994109239083)
            ·
              refine ⟨11022251479774491163858625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7348167653182994109239083 11022251479774491163858625)
              ·
                refine ⟨8266688609830868372893969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11022251479774491163858625 8266688609830868372893969)
                ·
                  refine ⟨6200016457373151279670477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8266688609830868372893969 6200016457373151279670477)
                  ·
                    refine ⟨2325006171514931729876429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6200016457373151279670477 2325006171514931729876429)
                    ·
                      refine ⟨871877314318099398703661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2325006171514931729876429 871877314318099398703661)
                      ·
                        rfl

theorem cell23_1697975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_1697975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697975 prefixEnd_1697975 := by exact prefixLift 1697975
  have htrace : WordTrace (prefixWord ++ tailWord_1697975) baseStart_1697975 baseEnd_1697975 := by
    simpa [prefixWord, tailWord_1697975, baseEnd_1697975] using wordTrace_append hprefix tailTrace_1697975
  have hstable : (prefixWord ++ tailWord_1697975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697975).length < 2 ^ (prefixWord ++ tailWord_1697975).sum := by decide
  have hdescent : baseEnd_1697975 < baseStart_1697975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697982 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_1697982 : Nat := 118140960795 + 1697982 * 2 ^ 59
def prefixEnd_1697982 : Nat := 4983230072969 + 3 ^ 40 * 1697982 * 2
def baseEnd_1697982 : Nat := 96875656520297874590681

theorem tailTrace_1697982 : CollatzResearch.WordTrace tailWord_1697982 prefixEnd_1697982 96875656520297874590681 := by
  unfold tailWord_1697982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7741311416813585135406025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41286994223005787388832133 7741311416813585135406025)
  ·
    refine ⟨5805983562610188851554519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7741311416813585135406025 5805983562610188851554519)
    ·
      refine ⟨8708975343915283277331779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5805983562610188851554519 8708975343915283277331779)
      ·
        refine ⟨13063463015872924915997669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8708975343915283277331779 13063463015872924915997669)
        ·
          refine ⟨2449399315476173421749563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13063463015872924915997669 2449399315476173421749563)
          ·
            refine ⟨3674098973214260132624345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449399315476173421749563 3674098973214260132624345)
            ·
              refine ⟨2755574229910695099468259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3674098973214260132624345 2755574229910695099468259)
              ·
                refine ⟨4133361344866042649202389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755574229910695099468259 4133361344866042649202389)
                ·
                  refine ⟨96875656520297874590681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4133361344866042649202389 96875656520297874590681)
                  ·
                    rfl

theorem cell23_1697982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_1697982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1697982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1697982 prefixEnd_1697982 := by exact prefixLift 1697982
  have htrace : WordTrace (prefixWord ++ tailWord_1697982) baseStart_1697982 baseEnd_1697982 := by
    simpa [prefixWord, tailWord_1697982, baseEnd_1697982] using wordTrace_append hprefix tailTrace_1697982
  have hstable : (prefixWord ++ tailWord_1697982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697982).length < 2 ^ (prefixWord ++ tailWord_1697982).sum := by decide
  have hdescent : baseEnd_1697982 < baseStart_1697982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698015 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 4]
def baseStart_1698015 : Nat := 118140960795 + 1698015 * 2 ^ 59
def prefixEnd_1698015 : Nat := 4983230072969 + 3 ^ 40 * 1698015 * 2
def baseEnd_1698015 : Nat := 871897853544279242203477

theorem tailTrace_1698015 : CollatzResearch.WordTrace tailWord_1698015 prefixEnd_1698015 871897853544279242203477 := by
  unfold tailWord_1698015
  simp only [CollatzResearch.WordTrace]
  refine ⟨61931694943389127719199499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41287796628926085146132999 61931694943389127719199499)
  ·
    refine ⟨92897542415083691578799249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61931694943389127719199499 92897542415083691578799249)
    ·
      refine ⟨69673156811312768684099437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92897542415083691578799249 69673156811312768684099437)
      ·
        refine ⟨26127433804242288256537289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69673156811312768684099437 26127433804242288256537289)
        ·
          refine ⟨19595575353181716192402967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26127433804242288256537289 19595575353181716192402967)
          ·
            refine ⟨29393363029772574288604451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19595575353181716192402967 29393363029772574288604451)
            ·
              refine ⟨44090044544658861432906677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29393363029772574288604451 44090044544658861432906677)
              ·
                refine ⟨4133441676061768259335001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44090044544658861432906677 4133441676061768259335001)
                ·
                  refine ⟨3100081257046326194501251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4133441676061768259335001 3100081257046326194501251)
                  ·
                    refine ⟨4650121885569489291751877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3100081257046326194501251 4650121885569489291751877)
                    ·
                      refine ⟨871897853544279242203477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4650121885569489291751877 871897853544279242203477)
                      ·
                        rfl

theorem cell23_1698015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_1698015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698015 prefixEnd_1698015 := by exact prefixLift 1698015
  have htrace : WordTrace (prefixWord ++ tailWord_1698015) baseStart_1698015 baseEnd_1698015 := by
    simpa [prefixWord, tailWord_1698015, baseEnd_1698015] using wordTrace_append hprefix tailTrace_1698015
  have hstable : (prefixWord ++ tailWord_1698015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698015).length < 2 ^ (prefixWord ++ tailWord_1698015).sum := by decide
  have hdescent : baseEnd_1698015 < baseStart_1698015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698042 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_1698042 : Nat := 118140960795 + 1698042 * 2 ^ 59
def prefixEnd_1698042 : Nat := 4983230072969 + 3 ^ 40 * 1698042 * 2
def baseEnd_1698042 : Nat := 290637239173983545521951

theorem tailTrace_1698042 : CollatzResearch.WordTrace tailWord_1698042 prefixEnd_1698042 290637239173983545521951 := by
  unfold tailWord_1698042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15483169928572827832608095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41288453142860874220288253 15483169928572827832608095)
  ·
    refine ⟨23224754892859241748912143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15483169928572827832608095 23224754892859241748912143)
    ·
      refine ⟨34837132339288862623368215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23224754892859241748912143 34837132339288862623368215)
      ·
        refine ⟨52255698508933293935052323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34837132339288862623368215 52255698508933293935052323)
        ·
          refine ⟨78383547763399940902578485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52255698508933293935052323 78383547763399940902578485)
          ·
            refine ⟨7348457602818744459616733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78383547763399940902578485 7348457602818744459616733)
            ·
              refine ⟨2755671601057029172356275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7348457602818744459616733 2755671601057029172356275)
              ·
                refine ⟨4133507401585543758534413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755671601057029172356275 4133507401585543758534413)
                ·
                  refine ⟨1550065275594578909450405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4133507401585543758534413 1550065275594578909450405)
                  ·
                    refine ⟨290637239173983545521951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1550065275594578909450405 290637239173983545521951)
                    ·
                      rfl

theorem cell23_1698042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_1698042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698042 prefixEnd_1698042 := by exact prefixLift 1698042
  have htrace : WordTrace (prefixWord ++ tailWord_1698042) baseStart_1698042 baseEnd_1698042 := by
    simpa [prefixWord, tailWord_1698042, baseEnd_1698042] using wordTrace_append hprefix tailTrace_1698042
  have hstable : (prefixWord ++ tailWord_1698042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698042).length < 2 ^ (prefixWord ++ tailWord_1698042).sum := by decide
  have hdescent : baseEnd_1698042 < baseStart_1698042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698093 : List Nat := [1, 5, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1698093 : Nat := 118140960795 + 1698093 * 2 ^ 59
def prefixEnd_1698093 : Nat := 4983230072969 + 3 ^ 40 * 1698093 * 2
def baseEnd_1698093 : Nat := 290645968345109979009373

theorem tailTrace_1698093 : CollatzResearch.WordTrace tailWord_1698093 prefixEnd_1698093 290645968345109979009373 := by
  unfold tailWord_1698093
  simp only [CollatzResearch.WordTrace]
  refine ⟨61934539837106547040538933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41289693224737698027025955 61934539837106547040538933)
  ·
    refine ⟨5806363109728738785050525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61934539837106547040538933 5806363109728738785050525)
    ·
      refine ⟨2177386166148277044393947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5806363109728738785050525 2177386166148277044393947)
      ·
        refine ⟨3266079249222415566590921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177386166148277044393947 3266079249222415566590921)
        ·
          refine ⟨2449559436916811674943191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3266079249222415566590921 2449559436916811674943191)
          ·
            refine ⟨3674339155375217512414787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449559436916811674943191 3674339155375217512414787)
            ·
              refine ⟨5511508733062826268622181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674339155375217512414787 5511508733062826268622181)
              ·
                refine ⟨1033407887449279925366659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5511508733062826268622181 1033407887449279925366659)
                ·
                  refine ⟨1550111831173919888049989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033407887449279925366659 1550111831173919888049989)
                  ·
                    refine ⟨290645968345109979009373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1550111831173919888049989 290645968345109979009373)
                    ·
                      rfl

theorem cell23_1698093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1698093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698093 prefixEnd_1698093 := by exact prefixLift 1698093
  have htrace : WordTrace (prefixWord ++ tailWord_1698093) baseStart_1698093 baseEnd_1698093 := by
    simpa [prefixWord, tailWord_1698093, baseEnd_1698093] using wordTrace_append hprefix tailTrace_1698093
  have hstable : (prefixWord ++ tailWord_1698093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698093).length < 2 ^ (prefixWord ++ tailWord_1698093).sum := by decide
  have hdescent : baseEnd_1698093 < baseStart_1698093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698115 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 1, 6]
def baseStart_1698115 : Nat := 118140960795 + 1698115 * 2 ^ 59
def prefixEnd_1698115 : Nat := 4983230072969 + 3 ^ 40 * 1698115 * 2
def baseEnd_1698115 : Nat := 290649733869909616984339

theorem tailTrace_1698115 : CollatzResearch.WordTrace tailWord_1698115 prefixEnd_1698115 290649733869909616984339 := by
  unfold tailWord_1698115
  simp only [CollatzResearch.WordTrace]
  refine ⟨61935342243026844797839799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41290228162017896531893199 61935342243026844797839799)
  ·
    refine ⟨92903013364540267196759699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61935342243026844797839799 92903013364540267196759699)
    ·
      refine ⟨139354520046810400795139549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92903013364540267196759699 139354520046810400795139549)
      ·
        refine ⟨52257945017553900298177331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139354520046810400795139549 52257945017553900298177331)
        ·
          refine ⟨78386917526330850447265997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52257945017553900298177331 78386917526330850447265997)
          ·
            refine ⟨29395094072374068917724749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78386917526330850447265997 29395094072374068917724749)
            ·
              refine ⟨11023160277140275844146781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29395094072374068917724749 11023160277140275844146781)
              ·
                refine ⟨4133685103927603441555043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11023160277140275844146781 4133685103927603441555043)
                ·
                  refine ⟨6200527655891405162332565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133685103927603441555043 6200527655891405162332565)
                  ·
                    refine ⟨290649733869909616984339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6200527655891405162332565 290649733869909616984339)
                    ·
                      rfl

theorem cell23_1698115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 6].length) (baseStart_1698115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698115 prefixEnd_1698115 := by exact prefixLift 1698115
  have htrace : WordTrace (prefixWord ++ tailWord_1698115) baseStart_1698115 baseEnd_1698115 := by
    simpa [prefixWord, tailWord_1698115, baseEnd_1698115] using wordTrace_append hprefix tailTrace_1698115
  have hstable : (prefixWord ++ tailWord_1698115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698115).length < 2 ^ (prefixWord ++ tailWord_1698115).sum := by decide
  have hdescent : baseEnd_1698115 < baseStart_1698115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698132 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_1698132 : Nat := 118140960795 + 1698132 * 2 ^ 59
def prefixEnd_1698132 : Nat := 4983230072969 + 3 ^ 40 * 1698132 * 2
def baseEnd_1698132 : Nat := 290652643593618428146813

theorem tailTrace_1698132 : CollatzResearch.WordTrace tailWord_1698132 prefixEnd_1698132 290652643593618428146813 := by
  unfold tailWord_1698132
  simp only [CollatzResearch.WordTrace]
  refine ⟨30967981141982628350604325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41290641522643504467472433 30967981141982628350604325)
  ·
    refine ⟨5806496464121742815738311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30967981141982628350604325 5806496464121742815738311)
    ·
      refine ⟨8709744696182614223607467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5806496464121742815738311 8709744696182614223607467)
      ·
        refine ⟨13064617044273921335411201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8709744696182614223607467 13064617044273921335411201)
        ·
          refine ⟨9798462783205441001558401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13064617044273921335411201 9798462783205441001558401)
          ·
            refine ⟨7348847087404080751168801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9798462783205441001558401 7348847087404080751168801)
            ·
              refine ⟨5511635315553060563376601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7348847087404080751168801 5511635315553060563376601)
              ·
                refine ⟨4133726486664795422532451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5511635315553060563376601 4133726486664795422532451)
                ·
                  refine ⟨6200589729997193133798677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133726486664795422532451 6200589729997193133798677)
                  ·
                    refine ⟨290652643593618428146813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6200589729997193133798677 290652643593618428146813)
                    ·
                      rfl

theorem cell23_1698132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_1698132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698132 prefixEnd_1698132 := by exact prefixLift 1698132
  have htrace : WordTrace (prefixWord ++ tailWord_1698132) baseStart_1698132 baseEnd_1698132 := by
    simpa [prefixWord, tailWord_1698132, baseEnd_1698132] using wordTrace_append hprefix tailTrace_1698132
  have hstable : (prefixWord ++ tailWord_1698132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698132).length < 2 ^ (prefixWord ++ tailWord_1698132).sum := by decide
  have hdescent : baseEnd_1698132 < baseStart_1698132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698133 : List Nat := [1, 3, 2, 2, 4, 1, 2, 3, 1, 1, 3]
def baseStart_1698133 : Nat := 118140960795 + 1698133 * 2 ^ 59
def prefixEnd_1698133 : Nat := 4983230072969 + 3 ^ 40 * 1698133 * 2
def baseEnd_1698133 : Nat := 871958444261509780527935

theorem tailTrace_1698133 : CollatzResearch.WordTrace tailWord_1698133 prefixEnd_1698133 871958444261509780527935 := by
  unfold tailWord_1698133
  simp only [CollatzResearch.WordTrace]
  refine ⟨61935998756961633871995053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41290665837974422581330035 61935998756961633871995053)
  ·
    refine ⟨23225999533860612701998145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61935998756961633871995053 23225999533860612701998145)
    ·
      refine ⟨17419499650395459526498609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23225999533860612701998145 17419499650395459526498609)
      ·
        refine ⟨13064624737796594644873957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17419499650395459526498609 13064624737796594644873957)
        ·
          refine ⟨2449617138336861495913867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13064624737796594644873957 2449617138336861495913867)
          ·
            refine ⟨3674425707505292243870801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449617138336861495913867 3674425707505292243870801)
            ·
              refine ⟨2755819280628969182903101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3674425707505292243870801 2755819280628969182903101)
              ·
                refine ⟨1033432230235863443588663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2755819280628969182903101 1033432230235863443588663)
                ·
                  refine ⟨1550148345353795165382995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033432230235863443588663 1550148345353795165382995)
                  ·
                    refine ⟨2325222518030692748074493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1550148345353795165382995 2325222518030692748074493)
                    ·
                      refine ⟨871958444261509780527935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2325222518030692748074493 871958444261509780527935)
                      ·
                        rfl

theorem cell23_1698133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_1698133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698133 prefixEnd_1698133 := by exact prefixLift 1698133
  have htrace : WordTrace (prefixWord ++ tailWord_1698133) baseStart_1698133 baseEnd_1698133 := by
    simpa [prefixWord, tailWord_1698133, baseEnd_1698133] using wordTrace_append hprefix tailTrace_1698133
  have hstable : (prefixWord ++ tailWord_1698133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698133).length < 2 ^ (prefixWord ++ tailWord_1698133).sum := by decide
  have hdescent : baseEnd_1698133 < baseStart_1698133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698149 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_1698149 : Nat := 118140960795 + 1698149 * 2 ^ 59
def prefixEnd_1698149 : Nat := 4983230072969 + 3 ^ 40 * 1698149 * 2
def baseEnd_1698149 : Nat := 290655553317327239309287

theorem tailTrace_1698149 : CollatzResearch.WordTrace tailWord_1698149 prefixEnd_1698149 290655553317327239309287 := by
  unfold tailWord_1698149
  simp only [CollatzResearch.WordTrace]
  refine ⟨61936582324903668604577501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41291054883269112403051667 61936582324903668604577501)
  ·
    refine ⟨23226218371838875726716563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61936582324903668604577501 23226218371838875726716563)
    ·
      refine ⟨34839327557758313590074845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23226218371838875726716563 34839327557758313590074845)
      ·
        refine ⟨13064747834159367596278067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34839327557758313590074845 13064747834159367596278067)
        ·
          refine ⟨19597121751239051394417101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13064747834159367596278067 19597121751239051394417101)
          ·
            refine ⟨7348920656714644272906413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19597121751239051394417101 7348920656714644272906413)
            ·
              refine ⟨2755845246267991602339905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7348920656714644272906413 2755845246267991602339905)
              ·
                refine ⟨2066883934700993701754929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2755845246267991602339905 2066883934700993701754929)
                ·
                  refine ⟨1550162951025745276316197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2066883934700993701754929 1550162951025745276316197)
                  ·
                    refine ⟨290655553317327239309287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1550162951025745276316197 290655553317327239309287)
                    ·
                      rfl

theorem cell23_1698149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_1698149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698149 prefixEnd_1698149 := by exact prefixLift 1698149
  have htrace : WordTrace (prefixWord ++ tailWord_1698149) baseStart_1698149 baseEnd_1698149 := by
    simpa [prefixWord, tailWord_1698149, baseEnd_1698149] using wordTrace_append hprefix tailTrace_1698149
  have hstable : (prefixWord ++ tailWord_1698149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698149).length < 2 ^ (prefixWord ++ tailWord_1698149).sum := by decide
  have hdescent : baseEnd_1698149 < baseStart_1698149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698172 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_1698172 : Nat := 118140960795 + 1698172 * 2 ^ 59
def prefixEnd_1698172 : Nat := 4983230072969 + 3 ^ 40 * 1698172 * 2
def baseEnd_1698172 : Nat := 871978470007035127940255

theorem tailTrace_1698172 : CollatzResearch.WordTrace tailWord_1698172 prefixEnd_1698172 871978470007035127940255 := by
  unfold tailWord_1698172
  simp only [CollatzResearch.WordTrace]
  refine ⟨30968710601910171766332385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41291614135880229021776513 30968710601910171766332385)
  ·
    refine ⟨23226532951432628824749289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30968710601910171766332385 23226532951432628824749289)
    ·
      refine ⟨17419899713574471618561967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23226532951432628824749289 17419899713574471618561967)
      ·
        refine ⟨26129849570361707427842951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17419899713574471618561967 26129849570361707427842951)
        ·
          refine ⟨39194774355542561141764427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26129849570361707427842951 39194774355542561141764427)
          ·
            refine ⟨58792161533313841712646641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39194774355542561141764427 58792161533313841712646641)
            ·
              refine ⟨44094121149985381284484981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58792161533313841712646641 44094121149985381284484981)
              ·
                refine ⟨4133823857811129495420467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44094121149985381284484981 4133823857811129495420467)
                ·
                  refine ⟨6200735786716694243130701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133823857811129495420467 6200735786716694243130701)
                  ·
                    refine ⟨2325275920018760341174013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6200735786716694243130701 2325275920018760341174013)
                    ·
                      refine ⟨871978470007035127940255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2325275920018760341174013 871978470007035127940255)
                      ·
                        rfl

theorem cell23_1698172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_1698172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698172 prefixEnd_1698172 := by exact prefixLift 1698172
  have htrace : WordTrace (prefixWord ++ tailWord_1698172) baseStart_1698172 baseEnd_1698172 := by
    simpa [prefixWord, tailWord_1698172, baseEnd_1698172] using wordTrace_append hprefix tailTrace_1698172
  have hstable : (prefixWord ++ tailWord_1698172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698172).length < 2 ^ (prefixWord ++ tailWord_1698172).sum := by decide
  have hdescent : baseEnd_1698172 < baseStart_1698172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698179 : List Nat := [1, 1, 1, 3, 6, 2, 2, 7]
def baseStart_1698179 : Nat := 118140960795 + 1698179 * 2 ^ 59
def prefixEnd_1698179 : Nat := 4983230072969 + 3 ^ 40 * 1698179 * 2
def baseEnd_1698179 : Nat := 32295632013763577798249

theorem tailTrace_1698179 : CollatzResearch.WordTrace tailWord_1698179 prefixEnd_1698179 32295632013763577798249 := by
  unfold tailWord_1698179
  simp only [CollatzResearch.WordTrace]
  refine ⟨61937676514794983728169591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41291784343196655818779727 61937676514794983728169591)
  ·
    refine ⟨92906514772192475592254387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61937676514794983728169591 92906514772192475592254387)
    ·
      refine ⟨139359772158288713388381581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92906514772192475592254387 139359772158288713388381581)
      ·
        refine ⟨52259914559358267520643093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139359772158288713388381581 52259914559358267520643093)
        ·
          refine ⟨2449683494969918790030145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52259914559358267520643093 2449683494969918790030145)
          ·
            refine ⟨1837262621227439092522609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2449683494969918790030145 1837262621227439092522609)
            ·
              refine ⟨1377946965920579319391957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1837262621227439092522609 1377946965920579319391957)
              ·
                refine ⟨32295632013763577798249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1377946965920579319391957 32295632013763577798249)
                ·
                  rfl

theorem cell23_1698179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 7].length) (baseStart_1698179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698179 prefixEnd_1698179 := by exact prefixLift 1698179
  have htrace : WordTrace (prefixWord ++ tailWord_1698179) baseStart_1698179 baseEnd_1698179 := by
    simpa [prefixWord, tailWord_1698179, baseEnd_1698179] using wordTrace_append hprefix tailTrace_1698179
  have hstable : (prefixWord ++ tailWord_1698179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698179).length < 2 ^ (prefixWord ++ tailWord_1698179).sum := by decide
  have hdescent : baseEnd_1698179 < baseStart_1698179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698190 : List Nat := [4, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1698190 : Nat := 118140960795 + 1698190 * 2 ^ 59
def prefixEnd_1698190 : Nat := 4983230072969 + 3 ^ 40 * 1698190 * 2
def baseEnd_1698190 : Nat := 871987712658816057515173

theorem tailTrace_1698190 : CollatzResearch.WordTrace tailWord_1698190 prefixEnd_1698190 871987712658816057515173 := by
  unfold tailWord_1698190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7742259714719391575852503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41292051811836755071213349 7742259714719391575852503)
  ·
    refine ⟨11613389572079087363778755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7742259714719391575852503 11613389572079087363778755)
    ·
      refine ⟨17420084358118631045668133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11613389572079087363778755 17420084358118631045668133)
      ·
        refine ⟨3266265817147243321062775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17420084358118631045668133 3266265817147243321062775)
        ·
          refine ⟨4899398725720864981594163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266265817147243321062775 4899398725720864981594163)
          ·
            refine ⟨7349098088581297472391245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899398725720864981594163 7349098088581297472391245)
            ·
              refine ⟨2755911783217986552146717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7349098088581297472391245 2755911783217986552146717)
              ·
                refine ⟨1033466918706744957055019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2755911783217986552146717 1033466918706744957055019)
                ·
                  refine ⟨1550200378060117435582529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033466918706744957055019 1550200378060117435582529)
                  ·
                    refine ⟨1162650283545088076686897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1550200378060117435582529 1162650283545088076686897)
                    ·
                      refine ⟨871987712658816057515173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162650283545088076686897 871987712658816057515173)
                      ·
                        rfl

theorem cell23_1698190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1698190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698190 prefixEnd_1698190 := by exact prefixLift 1698190
  have htrace : WordTrace (prefixWord ++ tailWord_1698190) baseStart_1698190 baseEnd_1698190 := by
    simpa [prefixWord, tailWord_1698190, baseEnd_1698190] using wordTrace_append hprefix tailTrace_1698190
  have hstable : (prefixWord ++ tailWord_1698190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698190).length < 2 ^ (prefixWord ++ tailWord_1698190).sum := by decide
  have hdescent : baseEnd_1698190 < baseStart_1698190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698233 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 1, 3, 2]
def baseStart_1698233 : Nat := 118140960795 + 1698233 * 2 ^ 59
def prefixEnd_1698233 : Nat := 4983230072969 + 3 ^ 40 * 1698233 * 2
def baseEnd_1698233 : Nat := 872009792326959389277475

theorem tailTrace_1698233 : CollatzResearch.WordTrace tailWord_1698233 prefixEnd_1698233 872009792326959389277475 := by
  unfold tailWord_1698233
  simp only [CollatzResearch.WordTrace]
  refine ⟨61939646056599350950635353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41293097371066233967090235 61939646056599350950635353)
  ·
    refine ⟨46454734542449513212976515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61939646056599350950635353 46454734542449513212976515)
    ·
      refine ⟨69682101813674269819464773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46454734542449513212976515 69682101813674269819464773)
      ·
        refine ⟨13065394090063925591149645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69682101813674269819464773 13065394090063925591149645)
        ·
          refine ⟨4899522783773972096681117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13065394090063925591149645 4899522783773972096681117)
          ·
            refine ⟨1837321043915239536255419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4899522783773972096681117 1837321043915239536255419)
            ·
              refine ⟨2755981565872859304383129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837321043915239536255419 2755981565872859304383129)
              ·
                refine ⟨2066986174404644478287347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2755981565872859304383129 2066986174404644478287347)
                ·
                  refine ⟨3100479261606966717431021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066986174404644478287347 3100479261606966717431021)
                  ·
                    refine ⟨1162679723102612519036633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3100479261606966717431021 1162679723102612519036633)
                    ·
                      refine ⟨872009792326959389277475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162679723102612519036633 872009792326959389277475)
                      ·
                        rfl

theorem cell23_1698233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_1698233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698233 prefixEnd_1698233 := by exact prefixLift 1698233
  have htrace : WordTrace (prefixWord ++ tailWord_1698233) baseStart_1698233 baseEnd_1698233 := by
    simpa [prefixWord, tailWord_1698233, baseEnd_1698233] using wordTrace_append hprefix tailTrace_1698233
  have hstable : (prefixWord ++ tailWord_1698233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698233).length < 2 ^ (prefixWord ++ tailWord_1698233).sum := by decide
  have hdescent : baseEnd_1698233 < baseStart_1698233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698279 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1698279 : Nat := 118140960795 + 1698279 * 2 ^ 59
def prefixEnd_1698279 : Nat := 4983230072969 + 3 ^ 40 * 1698279 * 2
def baseEnd_1698279 : Nat := 872033412437066209302263

theorem tailTrace_1698279 : CollatzResearch.WordTrace tailWord_1698279 prefixEnd_1698279 872033412437066209302263 := by
  unfold tailWord_1698279
  simp only [CollatzResearch.WordTrace]
  refine ⟨61941323814432700806809891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41294215876288467204539927 61941323814432700806809891)
  ·
    refine ⟨92911985721649051210214837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61941323814432700806809891 92911985721649051210214837)
    ·
      refine ⟨8710498661404598550957641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92911985721649051210214837 8710498661404598550957641)
      ·
        refine ⟨6532873996053448913218231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8710498661404598550957641 6532873996053448913218231)
        ·
          refine ⟨9799310994080173369827347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532873996053448913218231 9799310994080173369827347)
          ·
            refine ⟨14698966491120260054741021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9799310994080173369827347 14698966491120260054741021)
            ·
              refine ⟨5512112434170097520527883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14698966491120260054741021 5512112434170097520527883)
              ·
                refine ⟨8268168651255146280791825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5512112434170097520527883 8268168651255146280791825)
                ·
                  refine ⟨6201126488441359710593869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8268168651255146280791825 6201126488441359710593869)
                  ·
                    refine ⟨2325422433165509891472701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6201126488441359710593869 2325422433165509891472701)
                    ·
                      refine ⟨872033412437066209302263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2325422433165509891472701 872033412437066209302263)
                      ·
                        rfl

theorem cell23_1698279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1698279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698279 prefixEnd_1698279 := by exact prefixLift 1698279
  have htrace : WordTrace (prefixWord ++ tailWord_1698279) baseStart_1698279 baseEnd_1698279 := by
    simpa [prefixWord, tailWord_1698279, baseEnd_1698279] using wordTrace_append hprefix tailTrace_1698279
  have hstable : (prefixWord ++ tailWord_1698279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698279).length < 2 ^ (prefixWord ++ tailWord_1698279).sum := by decide
  have hdescent : baseEnd_1698279 < baseStart_1698279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698289 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 2, 5, 2]
def baseStart_1698289 : Nat := 118140960795 + 1698289 * 2 ^ 59
def prefixEnd_1698289 : Nat := 4983230072969 + 3 ^ 40 * 1698289 * 2
def baseEnd_1698289 : Nat := 872038547243611170177217

theorem tailTrace_1698289 : CollatzResearch.WordTrace tailWord_1698289 prefixEnd_1698289 872038547243611170177217 := by
  unfold tailWord_1698289
  simp only [CollatzResearch.WordTrace]
  refine ⟨61941688544396472514673921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41294459029597648343115947 61941688544396472514673921)
  ·
    refine ⟨46456266408297354386005441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61941688544396472514673921 46456266408297354386005441)
    ·
      refine ⟨34842199806223015789504081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46456266408297354386005441 34842199806223015789504081)
      ·
        refine ⟨26131649854667261842128061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34842199806223015789504081 26131649854667261842128061)
        ·
          refine ⟨9799368695500223190798023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26131649854667261842128061 9799368695500223190798023)
          ·
            refine ⟨14699053043250334786197035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9799368695500223190798023 14699053043250334786197035)
            ·
              refine ⟨22048579564875502179295553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14699053043250334786197035 22048579564875502179295553)
              ·
                refine ⟨16536434673656626634471665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22048579564875502179295553 16536434673656626634471665)
                ·
                  refine ⟨12402326005242469975853749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16536434673656626634471665 12402326005242469975853749)
                  ·
                    refine ⟨1162718062991481560236289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12402326005242469975853749 1162718062991481560236289)
                    ·
                      refine ⟨872038547243611170177217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162718062991481560236289 872038547243611170177217)
                      ·
                        rfl

theorem cell23_1698289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_1698289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698289 prefixEnd_1698289 := by exact prefixLift 1698289
  have htrace : WordTrace (prefixWord ++ tailWord_1698289) baseStart_1698289 baseEnd_1698289 := by
    simpa [prefixWord, tailWord_1698289, baseEnd_1698289] using wordTrace_append hprefix tailTrace_1698289
  have hstable : (prefixWord ++ tailWord_1698289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698289).length < 2 ^ (prefixWord ++ tailWord_1698289).sum := by decide
  have hdescent : baseEnd_1698289 < baseStart_1698289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698319 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 2, 4, 2]
def baseStart_1698319 : Nat := 118140960795 + 1698319 * 2 ^ 59
def prefixEnd_1698319 : Nat := 4983230072969 + 3 ^ 40 * 1698319 * 2
def baseEnd_1698319 : Nat := 872053951663246052802079

theorem tailTrace_1698319 : CollatzResearch.WordTrace tailWord_1698319 prefixEnd_1698319 872053951663246052802079 := by
  unfold tailWord_1698319
  simp only [CollatzResearch.WordTrace]
  refine ⟨61942782734287787638266011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41295188489525191758844007 61942782734287787638266011)
  ·
    refine ⟨92914174101431681457399017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61942782734287787638266011 92914174101431681457399017)
    ·
      refine ⟨69685630576073761093049263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92914174101431681457399017 69685630576073761093049263)
      ·
        refine ⟨104528445864110641639573895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69685630576073761093049263 104528445864110641639573895)
        ·
          refine ⟨156792668796165962459360843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104528445864110641639573895 156792668796165962459360843)
          ·
            refine ⟨235189003194248943689041265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156792668796165962459360843 235189003194248943689041265)
            ·
              refine ⟨176391752395686707766780949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235189003194248943689041265 176391752395686707766780949)
              ·
                refine ⟨8268363393547814426567857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 176391752395686707766780949 8268363393547814426567857)
                ·
                  refine ⟨6201272545160860819925893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8268363393547814426567857 6201272545160860819925893)
                  ·
                    refine ⟨1162738602217661403736105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6201272545160860819925893 1162738602217661403736105)
                    ·
                      refine ⟨872053951663246052802079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162738602217661403736105 872053951663246052802079)
                      ·
                        rfl

theorem cell23_1698319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 4, 2].length) (baseStart_1698319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698319 prefixEnd_1698319 := by exact prefixLift 1698319
  have htrace : WordTrace (prefixWord ++ tailWord_1698319) baseStart_1698319 baseEnd_1698319 := by
    simpa [prefixWord, tailWord_1698319, baseEnd_1698319] using wordTrace_append hprefix tailTrace_1698319
  have hstable : (prefixWord ++ tailWord_1698319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698319).length < 2 ^ (prefixWord ++ tailWord_1698319).sum := by decide
  have hdescent : baseEnd_1698319 < baseStart_1698319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698339 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1698339 : Nat := 118140960795 + 1698339 * 2 ^ 59
def prefixEnd_1698339 : Nat := 4983230072969 + 3 ^ 40 * 1698339 * 2
def baseEnd_1698339 : Nat := 872064221276335974551987

theorem tailTrace_1698339 : CollatzResearch.WordTrace tailWord_1698339 prefixEnd_1698339 872064221276335974551987 := by
  unfold tailWord_1698339
  simp only [CollatzResearch.WordTrace]
  refine ⟨61943512194215331053994071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41295674796143554035996047 61943512194215331053994071)
  ·
    refine ⟨92915268291322996580991107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61943512194215331053994071 92915268291322996580991107)
    ·
      refine ⟨139372902436984494871486661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92915268291322996580991107 139372902436984494871486661)
      ·
        refine ⟨26132419206934592788403749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139372902436984494871486661 26132419206934592788403749)
        ·
          refine ⟨4899828601300236147825703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26132419206934592788403749 4899828601300236147825703)
          ·
            refine ⟨7349742901950354221738555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899828601300236147825703 7349742901950354221738555)
            ·
              refine ⟨11024614352925531332607833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349742901950354221738555 11024614352925531332607833)
              ·
                refine ⟨8268460764694148499455875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11024614352925531332607833 8268460764694148499455875)
                ·
                  refine ⟨12402691147041222749183813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8268460764694148499455875 12402691147041222749183813)
                  ·
                    refine ⟨2325504590070229265471965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12402691147041222749183813 2325504590070229265471965)
                    ·
                      refine ⟨872064221276335974551987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2325504590070229265471965 872064221276335974551987)
                      ·
                        rfl

theorem cell23_1698339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1698339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698339 prefixEnd_1698339 := by exact prefixLift 1698339
  have htrace : WordTrace (prefixWord ++ tailWord_1698339) baseStart_1698339 baseEnd_1698339 := by
    simpa [prefixWord, tailWord_1698339, baseEnd_1698339] using wordTrace_append hprefix tailTrace_1698339
  have hstable : (prefixWord ++ tailWord_1698339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698339).length < 2 ^ (prefixWord ++ tailWord_1698339).sum := by decide
  have hdescent : baseEnd_1698339 < baseStart_1698339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698346 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1698346 : Nat := 118140960795 + 1698346 * 2 ^ 59
def prefixEnd_1698346 : Nat := 4983230072969 + 3 ^ 40 * 1698346 * 2
def baseEnd_1698346 : Nat := 290689271880305815721485

theorem tailTrace_1698346 : CollatzResearch.WordTrace tailWord_1698346 prefixEnd_1698346 290689271880305815721485 := by
  unfold tailWord_1698346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15485941876297492812374723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41295845003459980832999261 15485941876297492812374723)
  ·
    refine ⟨23228912814446239218562085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15485941876297492812374723 23228912814446239218562085)
    ·
      refine ⟨4355421152708669853480391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23228912814446239218562085 4355421152708669853480391)
      ·
        refine ⟨6533131729063004780220587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4355421152708669853480391 6533131729063004780220587)
        ·
          refine ⟨9799697593594507170330881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533131729063004780220587 9799697593594507170330881)
          ·
            refine ⟨7349773195195880377748161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9799697593594507170330881 7349773195195880377748161)
            ·
              refine ⟨5512329896396910283311121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7349773195195880377748161 5512329896396910283311121)
              ·
                refine ⟨4134247422297682712483341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5512329896396910283311121 4134247422297682712483341)
                ·
                  refine ⟨1550342783361631017181253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4134247422297682712483341 1550342783361631017181253)
                  ·
                    refine ⟨290689271880305815721485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1550342783361631017181253 290689271880305815721485)
                    ·
                      rfl

theorem cell23_1698346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1698346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698346 prefixEnd_1698346 := by exact prefixLift 1698346
  have htrace : WordTrace (prefixWord ++ tailWord_1698346) baseStart_1698346 baseEnd_1698346 := by
    simpa [prefixWord, tailWord_1698346, baseEnd_1698346] using wordTrace_append hprefix tailTrace_1698346
  have hstable : (prefixWord ++ tailWord_1698346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698346).length < 2 ^ (prefixWord ++ tailWord_1698346).sum := by decide
  have hdescent : baseEnd_1698346 < baseStart_1698346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698413 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_1698413 : Nat := 118140960795 + 1698413 * 2 ^ 59
def prefixEnd_1698413 : Nat := 4983230072969 + 3 ^ 40 * 1698413 * 2
def baseEnd_1698413 : Nat := 872102218844768685026647

theorem tailTrace_1698413 : CollatzResearch.WordTrace tailWord_1698413 prefixEnd_1698413 872102218844768685026647 := by
  unfold tailWord_1698413
  simp only [CollatzResearch.WordTrace]
  refine ⟨61946211195947241692187893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41297474130631494461458595 61946211195947241692187893)
  ·
    refine ⟨5807457299620053908642615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61946211195947241692187893 5807457299620053908642615)
    ·
      refine ⟨8711185949430080862963923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5807457299620053908642615 8711185949430080862963923)
      ·
        refine ⟨13066778924145121294445885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8711185949430080862963923 13066778924145121294445885)
        ·
          refine ⟨4900042096554420485417207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13066778924145121294445885 4900042096554420485417207)
          ·
            refine ⟨7350063144831630728125811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900042096554420485417207 7350063144831630728125811)
            ·
              refine ⟨11025094717247446092188717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350063144831630728125811 11025094717247446092188717)
              ·
                refine ⟨4134410518967792284570769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11025094717247446092188717 4134410518967792284570769)
                ·
                  refine ⟨3100807889225844213428077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4134410518967792284570769 3100807889225844213428077)
                  ·
                    refine ⟨1162802958459691580035529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3100807889225844213428077 1162802958459691580035529)
                    ·
                      refine ⟨872102218844768685026647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162802958459691580035529 872102218844768685026647)
                      ·
                        rfl

theorem cell23_1698413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_1698413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698413 prefixEnd_1698413 := by exact prefixLift 1698413
  have htrace : WordTrace (prefixWord ++ tailWord_1698413) baseStart_1698413 baseEnd_1698413 := by
    simpa [prefixWord, tailWord_1698413, baseEnd_1698413] using wordTrace_append hprefix tailTrace_1698413
  have hstable : (prefixWord ++ tailWord_1698413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698413).length < 2 ^ (prefixWord ++ tailWord_1698413).sum := by decide
  have hdescent : baseEnd_1698413 < baseStart_1698413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698419 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 4, 4]
def baseStart_1698419 : Nat := 118140960795 + 1698419 * 2 ^ 59
def prefixEnd_1698419 : Nat := 4983230072969 + 3 ^ 40 * 1698419 * 2
def baseEnd_1698419 : Nat := 290701766576231887183873

theorem tailTrace_1698419 : CollatzResearch.WordTrace tailWord_1698419 prefixEnd_1698419 290701766576231887183873 := by
  unfold tailWord_1698419
  simp only [CollatzResearch.WordTrace]
  refine ⟨61946430033925504716906311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41297620022617003144604207 61946430033925504716906311)
  ·
    refine ⟨92919645050888257075359467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61946430033925504716906311 92919645050888257075359467)
    ·
      refine ⟨139379467576332385613039201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92919645050888257075359467 139379467576332385613039201)
      ·
        refine ⟨104534600682249289209779401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139379467576332385613039201 104534600682249289209779401)
        ·
          refine ⟨78400950511686966907334551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104534600682249289209779401 78400950511686966907334551)
          ·
            refine ⟨117601425767530450361001827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78400950511686966907334551 117601425767530450361001827)
            ·
              refine ⟨176402138651295675541502741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117601425767530450361001827 176402138651295675541502741)
              ·
                refine ⟨8268850249279484791007941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 176402138651295675541502741 8268850249279484791007941)
                ·
                  refine ⟨1550409421739903398313989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8268850249279484791007941 1550409421739903398313989)
                  ·
                    refine ⟨290701766576231887183873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1550409421739903398313989 290701766576231887183873)
                    ·
                      rfl

theorem cell23_1698419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 4].length) (baseStart_1698419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698419 prefixEnd_1698419 := by exact prefixLift 1698419
  have htrace : WordTrace (prefixWord ++ tailWord_1698419) baseStart_1698419 baseEnd_1698419 := by
    simpa [prefixWord, tailWord_1698419, baseEnd_1698419] using wordTrace_append hprefix tailTrace_1698419
  have hstable : (prefixWord ++ tailWord_1698419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698419).length < 2 ^ (prefixWord ++ tailWord_1698419).sum := by decide
  have hdescent : baseEnd_1698419 < baseStart_1698419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698432 : List Nat := [2, 1, 1, 2, 1, 16]
def baseStart_1698432 : Nat := 118140960795 + 1698432 * 2 ^ 59
def prefixEnd_1698432 : Nat := 4983230072969 + 3 ^ 40 * 1698432 * 2
def baseEnd_1698432 : Nat := 3588938168630469591313

theorem tailTrace_1698432 : CollatzResearch.WordTrace tailWord_1698432 prefixEnd_1698432 3588938168630469591313 := by
  unfold tailWord_1698432
  simp only [CollatzResearch.WordTrace]
  refine ⟨30973452091439203968564775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41297936121918938624753033 30973452091439203968564775)
  ·
    refine ⟨46460178137158805952847163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30973452091439203968564775 46460178137158805952847163)
    ·
      refine ⟨69690267205738208929270745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46460178137158805952847163 69690267205738208929270745)
      ·
        refine ⟨52267700404303656696953059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69690267205738208929270745 52267700404303656696953059)
        ·
          refine ⟨78401550606455485045429589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52267700404303656696953059 78401550606455485045429589)
          ·
            refine ⟨3588938168630469591313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 78401550606455485045429589 3588938168630469591313)
            ·
              rfl

theorem cell23_1698432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 16].length) (baseStart_1698432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698432 prefixEnd_1698432 := by exact prefixLift 1698432
  have htrace : WordTrace (prefixWord ++ tailWord_1698432) baseStart_1698432 baseEnd_1698432 := by
    simpa [prefixWord, tailWord_1698432, baseEnd_1698432] using wordTrace_append hprefix tailTrace_1698432
  have hstable : (prefixWord ++ tailWord_1698432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698432).length < 2 ^ (prefixWord ++ tailWord_1698432).sum := by decide
  have hdescent : baseEnd_1698432 < baseStart_1698432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698437 : List Nat := [1, 3, 1, 1, 4, 4, 2, 2, 1, 1, 3]
def baseStart_1698437 : Nat := 118140960795 + 1698437 * 2 ^ 59
def prefixEnd_1698437 : Nat := 4983230072969 + 3 ^ 40 * 1698437 * 2
def baseEnd_1698437 : Nat := 872114542380476591126537

theorem tailTrace_1698437 : CollatzResearch.WordTrace tailWord_1698437 prefixEnd_1698437 872114542380476591126537 := by
  unfold tailWord_1698437
  simp only [CollatzResearch.WordTrace]
  refine ⟨61947086547860293791061565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41298057698573529194041043 61947086547860293791061565)
  ·
    refine ⟨23230157455447610171648087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61947086547860293791061565 23230157455447610171648087)
    ·
      refine ⟨34845236183171415257472131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23230157455447610171648087 34845236183171415257472131)
      ·
        refine ⟨52267854274757122886208197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34845236183171415257472131 52267854274757122886208197)
        ·
          refine ⟨9800222676516960541164037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52267854274757122886208197 9800222676516960541164037)
          ·
            refine ⟨1837541751846930101468257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9800222676516960541164037 1837541751846930101468257)
            ·
              refine ⟨1378156313885197576101193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1837541751846930101468257 1378156313885197576101193)
              ·
                refine ⟨1033617235413898182075895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378156313885197576101193 1033617235413898182075895)
                ·
                  refine ⟨1550425853120847273113843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033617235413898182075895 1550425853120847273113843)
                  ·
                    refine ⟨2325638779681270909670765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1550425853120847273113843 2325638779681270909670765)
                    ·
                      refine ⟨872114542380476591126537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2325638779681270909670765 872114542380476591126537)
                      ·
                        rfl

theorem cell23_1698437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 1, 1, 3].length) (baseStart_1698437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698437 prefixEnd_1698437 := by exact prefixLift 1698437
  have htrace : WordTrace (prefixWord ++ tailWord_1698437) baseStart_1698437 baseEnd_1698437 := by
    simpa [prefixWord, tailWord_1698437, baseEnd_1698437] using wordTrace_append hprefix tailTrace_1698437
  have hstable : (prefixWord ++ tailWord_1698437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698437).length < 2 ^ (prefixWord ++ tailWord_1698437).sum := by decide
  have hdescent : baseEnd_1698437 < baseStart_1698437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698439 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_1698439 : Nat := 118140960795 + 1698439 * 2 ^ 59
def prefixEnd_1698439 : Nat := 4983230072969 + 3 ^ 40 * 1698439 * 2
def baseEnd_1698439 : Nat := 872115569341785583301527

theorem tailTrace_1698439 : CollatzResearch.WordTrace tailWord_1698439 prefixEnd_1698439 872115569341785583301527 := by
  unfold tailWord_1698439
  simp only [CollatzResearch.WordTrace]
  refine ⟨61947159493853048132634371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41298106329235365421756247 61947159493853048132634371)
  ·
    refine ⟨92920739240779572198951557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61947159493853048132634371 92920739240779572198951557)
    ·
      refine ⟨17422638607646169787303417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92920739240779572198951557 17422638607646169787303417)
      ·
        refine ⟨13066978955734627340477563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17422638607646169787303417 13066978955734627340477563)
        ·
          refine ⟨19600468433601941010716345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13066978955734627340477563 19600468433601941010716345)
          ·
            refine ⟨14700351325201455758037259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19600468433601941010716345 14700351325201455758037259)
            ·
              refine ⟨22050526987802183637055889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14700351325201455758037259 22050526987802183637055889)
              ·
                refine ⟨16537895240851637727791917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22050526987802183637055889 16537895240851637727791917)
                ·
                  refine ⟨6201710715319364147921969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16537895240851637727791917 6201710715319364147921969)
                  ·
                    refine ⟨4651283036489523110941477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6201710715319364147921969 4651283036489523110941477)
                    ·
                      refine ⟨872115569341785583301527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4651283036489523110941477 872115569341785583301527)
                      ·
                        rfl

theorem cell23_1698439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_1698439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698439 prefixEnd_1698439 := by exact prefixLift 1698439
  have htrace : WordTrace (prefixWord ++ tailWord_1698439) baseStart_1698439 baseEnd_1698439 := by
    simpa [prefixWord, tailWord_1698439, baseEnd_1698439] using wordTrace_append hprefix tailTrace_1698439
  have hstable : (prefixWord ++ tailWord_1698439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698439).length < 2 ^ (prefixWord ++ tailWord_1698439).sum := by decide
  have hdescent : baseEnd_1698439 < baseStart_1698439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698446 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1698446 : Nat := 118140960795 + 1698446 * 2 ^ 59
def prefixEnd_1698446 : Nat := 4983230072969 + 3 ^ 40 * 1698446 * 2
def baseEnd_1698446 : Nat := 872119163706367055913995

theorem tailTrace_1698446 : CollatzResearch.WordTrace tailWord_1698446 prefixEnd_1698446 872119163706367055913995 := by
  unfold tailWord_1698446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7743426850603461041017399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41298276536551792218759461 7743426850603461041017399)
  ·
    refine ⟨11615140275905191561526099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7743426850603461041017399 11615140275905191561526099)
    ·
      refine ⟨17422710413857787342289149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11615140275905191561526099 17422710413857787342289149)
      ·
        refine ⟨6533516405196670253358431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17422710413857787342289149 6533516405196670253358431)
        ·
          refine ⟨9800274607795005380037647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533516405196670253358431 9800274607795005380037647)
          ·
            refine ⟨14700411911692508070056471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9800274607795005380037647 14700411911692508070056471)
            ·
              refine ⟨22050617867538762105084707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14700411911692508070056471 22050617867538762105084707)
              ·
                refine ⟨33075926801308143157627061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22050617867538762105084707 33075926801308143157627061)
                ·
                  refine ⟨3100868137622638421027537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33075926801308143157627061 3100868137622638421027537)
                  ·
                    refine ⟨2325651103216978815770653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3100868137622638421027537 2325651103216978815770653)
                    ·
                      refine ⟨872119163706367055913995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2325651103216978815770653 872119163706367055913995)
                      ·
                        rfl

theorem cell23_1698446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1698446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698446 prefixEnd_1698446 := by exact prefixLift 1698446
  have htrace : WordTrace (prefixWord ++ tailWord_1698446) baseStart_1698446 baseEnd_1698446 := by
    simpa [prefixWord, tailWord_1698446, baseEnd_1698446] using wordTrace_append hprefix tailTrace_1698446
  have hstable : (prefixWord ++ tailWord_1698446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698446).length < 2 ^ (prefixWord ++ tailWord_1698446).sum := by decide
  have hdescent : baseEnd_1698446 < baseStart_1698446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698456 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1698456 : Nat := 118140960795 + 1698456 * 2 ^ 59
def prefixEnd_1698456 : Nat := 4983230072969 + 3 ^ 40 * 1698456 * 2
def baseEnd_1698456 : Nat := 872124298512912016788949

theorem tailTrace_1698456 : CollatzResearch.WordTrace tailWord_1698456 prefixEnd_1698456 872124298512912016788949 := by
  unfold tailWord_1698456
  simp only [CollatzResearch.WordTrace]
  refine ⟨30973889767395730018001611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41298519689860973357335481 30973889767395730018001611)
  ·
    refine ⟨46460834651093595027002417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30973889767395730018001611 46460834651093595027002417)
    ·
      refine ⟨34845625988320196270251813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46460834651093595027002417 34845625988320196270251813)
      ·
        refine ⟨6533554872810036800672215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34845625988320196270251813 6533554872810036800672215)
        ·
          refine ⟨9800332309215055201008323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533554872810036800672215 9800332309215055201008323)
          ·
            refine ⟨14700498463822582801512485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9800332309215055201008323 14700498463822582801512485)
            ·
              refine ⟨2756343461966734275283591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14700498463822582801512485 2756343461966734275283591)
              ·
                refine ⟨4134515192950101412925387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756343461966734275283591 4134515192950101412925387)
                ·
                  refine ⟨6201772789425152119388081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134515192950101412925387 6201772789425152119388081)
                  ·
                    refine ⟨4651329592068864089541061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6201772789425152119388081 4651329592068864089541061)
                    ·
                      refine ⟨872124298512912016788949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4651329592068864089541061 872124298512912016788949)
                      ·
                        rfl

theorem cell23_1698456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1698456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698456 prefixEnd_1698456 := by exact prefixLift 1698456
  have htrace : WordTrace (prefixWord ++ tailWord_1698456) baseStart_1698456 baseEnd_1698456 := by
    simpa [prefixWord, tailWord_1698456, baseEnd_1698456] using wordTrace_append hprefix tailTrace_1698456
  have hstable : (prefixWord ++ tailWord_1698456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698456).length < 2 ^ (prefixWord ++ tailWord_1698456).sum := by decide
  have hdescent : baseEnd_1698456 < baseStart_1698456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698460 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_1698460 : Nat := 118140960795 + 1698460 * 2 ^ 59
def prefixEnd_1698460 : Nat := 4983230072969 + 3 ^ 40 * 1698460 * 2
def baseEnd_1698460 : Nat := 872126352435530001138931

theorem tailTrace_1698460 : CollatzResearch.WordTrace tailWord_1698460 prefixEnd_1698460 872126352435530001138931 := by
  unfold tailWord_1698460
  simp only [CollatzResearch.WordTrace]
  refine ⟨30973962713388484359574417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41298616951184645812765889 30973962713388484359574417)
  ·
    refine ⟨23230472035041363269680813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30973962713388484359574417 23230472035041363269680813)
    ·
      refine ⟨8711427013140511226130305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23230472035041363269680813 8711427013140511226130305)
      ·
        refine ⟨6533570259855383419597729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8711427013140511226130305 6533570259855383419597729)
        ·
          refine ⟨4900177694891537564698297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6533570259855383419597729 4900177694891537564698297)
          ·
            refine ⟨3675133271168653173523723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4900177694891537564698297 3675133271168653173523723)
            ·
              refine ⟨5512699906752979760285585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675133271168653173523723 5512699906752979760285585)
              ·
                refine ⟨4134524930064734820214189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5512699906752979760285585 4134524930064734820214189)
                ·
                  refine ⟨1550446848774275557580321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4134524930064734820214189 1550446848774275557580321)
                  ·
                    refine ⟨1162835136580706668185241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1550446848774275557580321 1162835136580706668185241)
                    ·
                      refine ⟨872126352435530001138931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162835136580706668185241 872126352435530001138931)
                      ·
                        rfl

theorem cell23_1698460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_1698460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698460 prefixEnd_1698460 := by exact prefixLift 1698460
  have htrace : WordTrace (prefixWord ++ tailWord_1698460) baseStart_1698460 baseEnd_1698460 := by
    simpa [prefixWord, tailWord_1698460, baseEnd_1698460] using wordTrace_append hprefix tailTrace_1698460
  have hstable : (prefixWord ++ tailWord_1698460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698460).length < 2 ^ (prefixWord ++ tailWord_1698460).sum := by decide
  have hdescent : baseEnd_1698460 < baseStart_1698460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698474 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1698474 : Nat := 118140960795 + 1698474 * 2 ^ 59
def prefixEnd_1698474 : Nat := 4983230072969 + 3 ^ 40 * 1698474 * 2
def baseEnd_1698474 : Nat := 290711180388230982121289

theorem tailTrace_1698474 : CollatzResearch.WordTrace tailWord_1698474 prefixEnd_1698474 290711180388230982121289 := by
  unfold tailWord_1698474
  simp only [CollatzResearch.WordTrace]
  refine ⟨15487109012181562277539619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41298957365817499406772317 15487109012181562277539619)
  ·
    refine ⟨23230663518272343416309429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15487109012181562277539619 23230663518272343416309429)
    ·
      refine ⟨2177874704838032195279009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23230663518272343416309429 2177874704838032195279009)
      ·
        refine ⟨1633406028628524146459257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2177874704838032195279009 1633406028628524146459257)
        ·
          refine ⟨1225054521471393109844443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1633406028628524146459257 1225054521471393109844443)
          ·
            refine ⟨1837581782207089664766665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225054521471393109844443 1837581782207089664766665)
            ·
              refine ⟨1378186336655317248574999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1837581782207089664766665 1378186336655317248574999)
              ·
                refine ⟨2067279504982975872862499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378186336655317248574999 2067279504982975872862499)
                ·
                  refine ⟨3100919257474463809293749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067279504982975872862499 3100919257474463809293749)
                  ·
                    refine ⟨290711180388230982121289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3100919257474463809293749 290711180388230982121289)
                    ·
                      rfl

theorem cell23_1698474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1698474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698474 prefixEnd_1698474 := by exact prefixLift 1698474
  have htrace : WordTrace (prefixWord ++ tailWord_1698474) baseStart_1698474 baseEnd_1698474 := by
    simpa [prefixWord, tailWord_1698474, baseEnd_1698474] using wordTrace_append hprefix tailTrace_1698474
  have hstable : (prefixWord ++ tailWord_1698474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698474).length < 2 ^ (prefixWord ++ tailWord_1698474).sum := by decide
  have hdescent : baseEnd_1698474 < baseStart_1698474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698477 : List Nat := [1, 5, 2, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_1698477 : Nat := 118140960795 + 1698477 * 2 ^ 59
def prefixEnd_1698477 : Nat := 4983230072969 + 3 ^ 40 * 1698477 * 2
def baseEnd_1698477 : Nat := 872135081606656434626353

theorem tailTrace_1698477 : CollatzResearch.WordTrace tailWord_1698477 prefixEnd_1698477 872135081606656434626353 := by
  unfold tailWord_1698477
  simp only [CollatzResearch.WordTrace]
  refine ⟨61948545467715380622517685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41299030311810253748345123 61948545467715380622517685)
  ·
    refine ⟨5807676137598316933361033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61948545467715380622517685 5807676137598316933361033)
    ·
      refine ⟨4355757103198737700020775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5807676137598316933361033 4355757103198737700020775)
      ·
        refine ⟨6533635654798106550031163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4355757103198737700020775 6533635654798106550031163)
        ·
          refine ⟨9800453482197159825046745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533635654798106550031163 9800453482197159825046745)
          ·
            refine ⟨7350340111647869868785059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9800453482197159825046745 7350340111647869868785059)
            ·
              refine ⟨11025510167471804803177589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350340111647869868785059 11025510167471804803177589)
              ·
                refine ⟨1033641578200481700297899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11025510167471804803177589 1033641578200481700297899)
                ·
                  refine ⟨1550462367300722550446849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033641578200481700297899 1550462367300722550446849)
                  ·
                    refine ⟨1162846775475541912835137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1550462367300722550446849 1162846775475541912835137)
                    ·
                      refine ⟨872135081606656434626353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162846775475541912835137 872135081606656434626353)
                      ·
                        rfl

theorem cell23_1698477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_1698477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698477 prefixEnd_1698477 := by exact prefixLift 1698477
  have htrace : WordTrace (prefixWord ++ tailWord_1698477) baseStart_1698477 baseEnd_1698477 := by
    simpa [prefixWord, tailWord_1698477, baseEnd_1698477] using wordTrace_append hprefix tailTrace_1698477
  have hstable : (prefixWord ++ tailWord_1698477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698477).length < 2 ^ (prefixWord ++ tailWord_1698477).sum := by decide
  have hdescent : baseEnd_1698477 < baseStart_1698477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698493 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_1698493 : Nat := 118140960795 + 1698493 * 2 ^ 59
def prefixEnd_1698493 : Nat := 4983230072969 + 3 ^ 40 * 1698493 * 2
def baseEnd_1698493 : Nat := 872143297297128372026279

theorem tailTrace_1698493 : CollatzResearch.WordTrace tailWord_1698493 prefixEnd_1698493 872143297297128372026279 := by
  unfold tailWord_1698493
  simp only [CollatzResearch.WordTrace]
  refine ⟨61949129035657415355100133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41299419357104943570066755 61949129035657415355100133)
  ·
    refine ⟨11615461694185765379081275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61949129035657415355100133 11615461694185765379081275)
    ·
      refine ⟨17423192541278648068621913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11615461694185765379081275 17423192541278648068621913)
      ·
        refine ⟨13067394405958986051466435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17423192541278648068621913 13067394405958986051466435)
        ·
          refine ⟨19601091608938479077199653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13067394405958986051466435 19601091608938479077199653)
          ·
            refine ⟨3675204676675964826974935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19601091608938479077199653 3675204676675964826974935)
            ·
              refine ⟨5512807015013947240462403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675204676675964826974935 5512807015013947240462403)
              ·
                refine ⟨8269210522520920860693605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5512807015013947240462403 8269210522520920860693605)
                ·
                  refine ⟨1550476972972672661380051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8269210522520920860693605 1550476972972672661380051)
                  ·
                    refine ⟨2325715459459008992070077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1550476972972672661380051 2325715459459008992070077)
                    ·
                      refine ⟨872143297297128372026279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2325715459459008992070077 872143297297128372026279)
                      ·
                        rfl

theorem cell23_1698493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_1698493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698493 prefixEnd_1698493 := by exact prefixLift 1698493
  have htrace : WordTrace (prefixWord ++ tailWord_1698493) baseStart_1698493 baseEnd_1698493 := by
    simpa [prefixWord, tailWord_1698493, baseEnd_1698493] using wordTrace_append hprefix tailTrace_1698493
  have hstable : (prefixWord ++ tailWord_1698493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698493).length < 2 ^ (prefixWord ++ tailWord_1698493).sum := by decide
  have hdescent : baseEnd_1698493 < baseStart_1698493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698520 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 1, 3, 2]
def baseStart_1698520 : Nat := 118140960795 + 1698520 * 2 ^ 59
def prefixEnd_1698520 : Nat := 4983230072969 + 3 ^ 40 * 1698520 * 2
def baseEnd_1698520 : Nat := 872157161274799766388655

theorem tailTrace_1698520 : CollatzResearch.WordTrace tailWord_1698520 prefixEnd_1698520 872157161274799766388655 := by
  unfold tailWord_1698520
  simp only [CollatzResearch.WordTrace]
  refine ⟨30975056903279799483166507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41300075871039732644222009 30975056903279799483166507)
  ·
    refine ⟨46462585354919699224749761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30975056903279799483166507 46462585354919699224749761)
    ·
      refine ⟨34846939016189774418562321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46462585354919699224749761 34846939016189774418562321)
      ·
        refine ⟨26135204262142330813921741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34846939016189774418562321 26135204262142330813921741)
        ·
          refine ⟨9800701598303374055220653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26135204262142330813921741 9800701598303374055220653)
          ·
            refine ⟨3675263099363765270707745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9800701598303374055220653 3675263099363765270707745)
            ·
              refine ⟨2756447324522823953030809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675263099363765270707745 2756447324522823953030809)
              ·
                refine ⟨2067335493392117964773107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2756447324522823953030809 2067335493392117964773107)
                ·
                  refine ⟨3101003240088176947159661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067335493392117964773107 3101003240088176947159661)
                  ·
                    refine ⟨1162876215033066355184873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101003240088176947159661 1162876215033066355184873)
                    ·
                      refine ⟨872157161274799766388655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162876215033066355184873 872157161274799766388655)
                      ·
                        rfl

theorem cell23_1698520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_1698520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698520 prefixEnd_1698520 := by exact prefixLift 1698520
  have htrace : WordTrace (prefixWord ++ tailWord_1698520) baseStart_1698520 baseEnd_1698520 := by
    simpa [prefixWord, tailWord_1698520, baseEnd_1698520] using wordTrace_append hprefix tailTrace_1698520
  have hstable : (prefixWord ++ tailWord_1698520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698520).length < 2 ^ (prefixWord ++ tailWord_1698520).sum := by decide
  have hdescent : baseEnd_1698520 < baseStart_1698520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698550 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_1698550 : Nat := 118140960795 + 1698550 * 2 ^ 59
def prefixEnd_1698550 : Nat := 4983230072969 + 3 ^ 40 * 1698550 * 2
def baseEnd_1698550 : Nat := 872172565694434649013517

theorem tailTrace_1698550 : CollatzResearch.WordTrace tailWord_1698550 prefixEnd_1698550 872172565694434649013517 := by
  unfold tailWord_1698550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871950499778182130620319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41300805330967276059950069 3871950499778182130620319)
  ·
    refine ⟨5807925749667273195930479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3871950499778182130620319 5807925749667273195930479)
    ·
      refine ⟨8711888624500909793895719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5807925749667273195930479 8711888624500909793895719)
      ·
        refine ⟨13067832936751364690843579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8711888624500909793895719 13067832936751364690843579)
        ·
          refine ⟨19601749405127047036265369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13067832936751364690843579 19601749405127047036265369)
          ·
            refine ⟨14701312053845285277199027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19601749405127047036265369 14701312053845285277199027)
            ·
              refine ⟨22051968080767927915798541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14701312053845285277199027 22051968080767927915798541)
              ·
                refine ⟨8269488030287972968424453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22051968080767927915798541 8269488030287972968424453)
                ·
                  refine ⟨1550529005678994931579585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8269488030287972968424453 1550529005678994931579585)
                  ·
                    refine ⟨1162896754259246198684689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1550529005678994931579585 1162896754259246198684689)
                    ·
                      refine ⟨872172565694434649013517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162896754259246198684689 872172565694434649013517)
                      ·
                        rfl

theorem cell23_1698550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_1698550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698550 prefixEnd_1698550 := by exact prefixLift 1698550
  have htrace : WordTrace (prefixWord ++ tailWord_1698550) baseStart_1698550 baseEnd_1698550 := by
    simpa [prefixWord, tailWord_1698550, baseEnd_1698550] using wordTrace_append hprefix tailTrace_1698550
  have hstable : (prefixWord ++ tailWord_1698550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698550).length < 2 ^ (prefixWord ++ tailWord_1698550).sum := by decide
  have hdescent : baseEnd_1698550 < baseStart_1698550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698556 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 7]
def baseStart_1698556 : Nat := 118140960795 + 1698556 * 2 ^ 59
def prefixEnd_1698556 : Nat := 4983230072969 + 3 ^ 40 * 1698556 * 2
def baseEnd_1698556 : Nat := 96908405175373513948721

theorem tailTrace_1698556 : CollatzResearch.WordTrace tailWord_1698556 prefixEnd_1698556 96908405175373513948721 := by
  unfold tailWord_1698556
  simp only [CollatzResearch.WordTrace]
  refine ⟨30975713417214588557321761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41300951222952784743095681 30975713417214588557321761)
  ·
    refine ⟨23231785062910941417991321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30975713417214588557321761 23231785062910941417991321)
    ·
      refine ⟨17423838797183206063493491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23231785062910941417991321 17423838797183206063493491)
      ·
        refine ⟨26135758195774809095240237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17423838797183206063493491 26135758195774809095240237)
        ·
          refine ⟨9800909323415553410715089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26135758195774809095240237 9800909323415553410715089)
          ·
            refine ⟨7350681992561665058036317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9800909323415553410715089 7350681992561665058036317)
            ·
              refine ⟨2756505747210624396763619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7350681992561665058036317 2756505747210624396763619)
              ·
                refine ⟨4134758620815936595145429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756505747210624396763619 4134758620815936595145429)
                ·
                  refine ⟨96908405175373513948721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4134758620815936595145429 96908405175373513948721)
                  ·
                    rfl

theorem cell23_1698556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_1698556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698556 prefixEnd_1698556 := by exact prefixLift 1698556
  have htrace : WordTrace (prefixWord ++ tailWord_1698556) baseStart_1698556 baseEnd_1698556 := by
    simpa [prefixWord, tailWord_1698556, baseEnd_1698556] using wordTrace_append hprefix tailTrace_1698556
  have hstable : (prefixWord ++ tailWord_1698556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698556).length < 2 ^ (prefixWord ++ tailWord_1698556).sum := by decide
  have hdescent : baseEnd_1698556 < baseStart_1698556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698567 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1698567 : Nat := 118140960795 + 1698567 * 2 ^ 59
def prefixEnd_1698567 : Nat := 4983230072969 + 3 ^ 40 * 1698567 * 2
def baseEnd_1698567 : Nat := 872181294865561082500939

theorem tailTrace_1698567 : CollatzResearch.WordTrace tailWord_1698567 prefixEnd_1698567 872181294865561082500939 := by
  unfold tailWord_1698567
  simp only [CollatzResearch.WordTrace]
  refine ⟨61951828037389325993293955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41301218691592883995529303 61951828037389325993293955)
  ·
    refine ⟨92927742056083988989940933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61951828037389325993293955 92927742056083988989940933)
    ·
      refine ⟨17423951635515747935613925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92927742056083988989940933 17423951635515747935613925)
      ·
        refine ⟨3266990931659202737927611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17423951635515747935613925 3266990931659202737927611)
        ·
          refine ⟨4900486397488804106891417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266990931659202737927611 4900486397488804106891417)
          ·
            refine ⟨3675364798116603080168563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4900486397488804106891417 3675364798116603080168563)
            ·
              refine ⟨5513047197174904620252845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675364798116603080168563 5513047197174904620252845)
              ·
                refine ⟨2067392698940589232594817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5513047197174904620252845 2067392698940589232594817)
                ·
                  refine ⟨1550544524205441924446113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2067392698940589232594817 1550544524205441924446113)
                  ·
                    refine ⟨1162908393154081443334585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1550544524205441924446113 1162908393154081443334585)
                    ·
                      refine ⟨872181294865561082500939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162908393154081443334585 872181294865561082500939)
                      ·
                        rfl

theorem cell23_1698567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1698567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698567 prefixEnd_1698567 := by exact prefixLift 1698567
  have htrace : WordTrace (prefixWord ++ tailWord_1698567) baseStart_1698567 baseEnd_1698567 := by
    simpa [prefixWord, tailWord_1698567, baseEnd_1698567] using wordTrace_append hprefix tailTrace_1698567
  have hstable : (prefixWord ++ tailWord_1698567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698567).length < 2 ^ (prefixWord ++ tailWord_1698567).sum := by decide
  have hdescent : baseEnd_1698567 < baseStart_1698567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698569 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 3, 7]
def baseStart_1698569 : Nat := 118140960795 + 1698569 * 2 ^ 59
def prefixEnd_1698569 : Nat := 4983230072969 + 3 ^ 40 * 1698569 * 2
def baseEnd_1698569 : Nat := 290727440608956691558643

theorem tailTrace_1698569 : CollatzResearch.WordTrace tailWord_1698569 prefixEnd_1698569 290727440608956691558643 := by
  unfold tailWord_1698569
  simp only [CollatzResearch.WordTrace]
  refine ⟨61951900983382080334866761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41301267322254720223244507 61951900983382080334866761)
  ·
    refine ⟨46463925737536560251150071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61951900983382080334866761 46463925737536560251150071)
    ·
      refine ⟨69695888606304840376725107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46463925737536560251150071 69695888606304840376725107)
      ·
        refine ⟨104543832909457260565087661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69695888606304840376725107 104543832909457260565087661)
        ·
          refine ⟨39203937341046472711907873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104543832909457260565087661 39203937341046472711907873)
          ·
            refine ⟨29402953005784854533930905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39203937341046472711907873 29402953005784854533930905)
            ·
              refine ⟨22052214754338640900448179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29402953005784854533930905 22052214754338640900448179)
              ·
                refine ⟨33078322131507961350672269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22052214754338640900448179 33078322131507961350672269)
                ·
                  refine ⟨12404370799315485506502101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33078322131507961350672269 12404370799315485506502101)
                  ·
                    refine ⟨290727440608956691558643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12404370799315485506502101 290727440608956691558643)
                    ·
                      rfl

theorem cell23_1698569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_1698569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698569 prefixEnd_1698569 := by exact prefixLift 1698569
  have htrace : WordTrace (prefixWord ++ tailWord_1698569) baseStart_1698569 baseEnd_1698569 := by
    simpa [prefixWord, tailWord_1698569, baseEnd_1698569] using wordTrace_append hprefix tailTrace_1698569
  have hstable : (prefixWord ++ tailWord_1698569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698569).length < 2 ^ (prefixWord ++ tailWord_1698569).sum := by decide
  have hdescent : baseEnd_1698569 < baseStart_1698569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698579 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 7]
def baseStart_1698579 : Nat := 118140960795 + 1698579 * 2 ^ 59
def prefixEnd_1698579 : Nat := 4983230072969 + 3 ^ 40 * 1698579 * 2
def baseEnd_1698579 : Nat := 872187456633415035550883

theorem tailTrace_1698579 : CollatzResearch.WordTrace tailWord_1698579 prefixEnd_1698579 872187456633415035550883 := by
  unfold tailWord_1698579
  simp only [CollatzResearch.WordTrace]
  refine ⟨61952265713345852042730791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41301510475563901361820527 61952265713345852042730791)
  ·
    refine ⟨92928398570018778064096187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61952265713345852042730791 92928398570018778064096187)
    ·
      refine ⟨139392597855028167096144281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92928398570018778064096187 139392597855028167096144281)
      ·
        refine ⟨104544448391271125322108211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139392597855028167096144281 104544448391271125322108211)
        ·
          refine ⟨156816672586906687983162317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104544448391271125322108211 156816672586906687983162317)
          ·
            refine ⟨58806252220090007993685869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156816672586906687983162317 58806252220090007993685869)
            ·
              refine ⟨22052344582533752997632201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58806252220090007993685869 22052344582533752997632201)
              ·
                refine ⟨16539258436900314748224151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22052344582533752997632201 16539258436900314748224151)
                ·
                  refine ⟨24808887655350472122336227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16539258436900314748224151 24808887655350472122336227)
                  ·
                    refine ⟨37213331483025708183504341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24808887655350472122336227 37213331483025708183504341)
                    ·
                      refine ⟨872187456633415035550883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37213331483025708183504341 872187456633415035550883)
                      ·
                        rfl

theorem cell23_1698579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_1698579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698579 prefixEnd_1698579 := by exact prefixLift 1698579
  have htrace : WordTrace (prefixWord ++ tailWord_1698579) baseStart_1698579 baseEnd_1698579 := by
    simpa [prefixWord, tailWord_1698579, baseEnd_1698579] using wordTrace_append hprefix tailTrace_1698579
  have hstable : (prefixWord ++ tailWord_1698579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698579).length < 2 ^ (prefixWord ++ tailWord_1698579).sum := by decide
  have hdescent : baseEnd_1698579 < baseStart_1698579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698623 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 1, 6, 2]
def baseStart_1698623 : Nat := 118140960795 + 1698623 * 2 ^ 59
def prefixEnd_1698623 : Nat := 4983230072969 + 3 ^ 40 * 1698623 * 2
def baseEnd_1698623 : Nat := 872210049782212863400681

theorem tailTrace_1698623 : CollatzResearch.WordTrace tailWord_1698623 prefixEnd_1698623 872210049782212863400681 := by
  unfold tailWord_1698623
  simp only [CollatzResearch.WordTrace]
  refine ⟨61953870525186447557332523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41302580350124298371555015 61953870525186447557332523)
  ·
    refine ⟨92930805787779671335998785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61953870525186447557332523 92930805787779671335998785)
    ·
      refine ⟨69698104340834753501999089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92930805787779671335998785 69698104340834753501999089)
      ·
        refine ⟨52273578255626065126499317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69698104340834753501999089 52273578255626065126499317)
        ·
          refine ⟨4900647961464943605609311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52273578255626065126499317 4900647961464943605609311)
          ·
            refine ⟨7350971942197415408413967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900647961464943605609311 7350971942197415408413967)
            ·
              refine ⟨11026457913296123112620951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350971942197415408413967 11026457913296123112620951)
              ·
                refine ⟨16539686869944184668931427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11026457913296123112620951 16539686869944184668931427)
                ·
                  refine ⟨24809530304916277003397141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16539686869944184668931427 24809530304916277003397141)
                  ·
                    refine ⟨1162946733042950484534241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24809530304916277003397141 1162946733042950484534241)
                    ·
                      refine ⟨872210049782212863400681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162946733042950484534241 872210049782212863400681)
                      ·
                        rfl

theorem cell23_1698623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_1698623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698623 prefixEnd_1698623 := by exact prefixLift 1698623
  have htrace : WordTrace (prefixWord ++ tailWord_1698623) baseStart_1698623 baseEnd_1698623 := by
    simpa [prefixWord, tailWord_1698623, baseEnd_1698623] using wordTrace_append hprefix tailTrace_1698623
  have hstable : (prefixWord ++ tailWord_1698623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698623).length < 2 ^ (prefixWord ++ tailWord_1698623).sum := by decide
  have hdescent : baseEnd_1698623 < baseStart_1698623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698633 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 3, 4]
def baseStart_1698633 : Nat := 118140960795 + 1698633 * 2 ^ 59
def prefixEnd_1698633 : Nat := 4983230072969 + 3 ^ 40 * 1698633 * 2
def baseEnd_1698633 : Nat := 290738394862919274758545

theorem tailTrace_1698633 : CollatzResearch.WordTrace tailWord_1698633 prefixEnd_1698633 290738394862919274758545 := by
  unfold tailWord_1698633
  simp only [CollatzResearch.WordTrace]
  refine ⟨61954235255150219265196553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41302823503433479510131035 61954235255150219265196553)
  ·
    refine ⟨46465676441362664448897415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61954235255150219265196553 46465676441362664448897415)
    ·
      refine ⟨69698514662043996673346123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46465676441362664448897415 69698514662043996673346123)
      ·
        refine ⟨104547771993065995010019185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69698514662043996673346123 104547771993065995010019185)
        ·
          refine ⟨78410828994799496257514389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104547771993065995010019185 78410828994799496257514389)
          ·
            refine ⟨3675507609131226387070987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78410828994799496257514389 3675507609131226387070987)
            ·
              refine ⟨5513261413696839580606481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675507609131226387070987 5513261413696839580606481)
              ·
                refine ⟨4134946060272629685454861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5513261413696839580606481 4134946060272629685454861)
                ·
                  refine ⟨1550604772602236132045573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4134946060272629685454861 1550604772602236132045573)
                  ·
                    refine ⟨290738394862919274758545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1550604772602236132045573 290738394862919274758545)
                    ·
                      rfl

theorem cell23_1698633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 4].length) (baseStart_1698633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698633 prefixEnd_1698633 := by exact prefixLift 1698633
  have htrace : WordTrace (prefixWord ++ tailWord_1698633) baseStart_1698633 baseEnd_1698633 := by
    simpa [prefixWord, tailWord_1698633, baseEnd_1698633] using wordTrace_append hprefix tailTrace_1698633
  have hstable : (prefixWord ++ tailWord_1698633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698633).length < 2 ^ (prefixWord ++ tailWord_1698633).sum := by decide
  have hdescent : baseEnd_1698633 < baseStart_1698633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698637 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_1698637 : Nat := 118140960795 + 1698637 * 2 ^ 59
def prefixEnd_1698637 : Nat := 4983230072969 + 3 ^ 40 * 1698637 * 2
def baseEnd_1698637 : Nat := 290739079503791936208539

theorem tailTrace_1698637 : CollatzResearch.WordTrace tailWord_1698637 prefixEnd_1698637 290739079503791936208539 := by
  unfold tailWord_1698637
  simp only [CollatzResearch.WordTrace]
  refine ⟨61954381147135727948342165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41302920764757151965561443 61954381147135727948342165)
  ·
    refine ⟨2904111616271987247578539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61954381147135727948342165 2904111616271987247578539)
    ·
      refine ⟨4356167424407980871367809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2904111616271987247578539 4356167424407980871367809)
      ·
        refine ⟨3267125568305985653525857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4356167424407980871367809 3267125568305985653525857)
        ·
          refine ⟨2450344176229489240144393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3267125568305985653525857 2450344176229489240144393)
          ·
            refine ⟨1837758132172116930108295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2450344176229489240144393 1837758132172116930108295)
            ·
              refine ⟨2756637198258175395162443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837758132172116930108295 2756637198258175395162443)
              ·
                refine ⟨4134955797387263092743665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756637198258175395162443 4134955797387263092743665)
                ·
                  refine ⟨3101216848040447319557749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4134955797387263092743665 3101216848040447319557749)
                  ·
                    refine ⟨290739079503791936208539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3101216848040447319557749 290739079503791936208539)
                    ·
                      rfl

theorem cell23_1698637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_1698637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698637 prefixEnd_1698637 := by exact prefixLift 1698637
  have htrace : WordTrace (prefixWord ++ tailWord_1698637) baseStart_1698637 baseEnd_1698637 := by
    simpa [prefixWord, tailWord_1698637, baseEnd_1698637] using wordTrace_append hprefix tailTrace_1698637
  have hstable : (prefixWord ++ tailWord_1698637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698637).length < 2 ^ (prefixWord ++ tailWord_1698637).sum := by decide
  have hdescent : baseEnd_1698637 < baseStart_1698637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698650 : List Nat := [3, 1, 1, 2, 1, 4, 1, 5, 1, 4]
def baseStart_1698650 : Nat := 118140960795 + 1698650 * 2 ^ 59
def prefixEnd_1698650 : Nat := 4983230072969 + 3 ^ 40 * 1698650 * 2
def baseEnd_1698650 : Nat := 290741304586628085921019

theorem tailTrace_1698650 : CollatzResearch.WordTrace tailWord_1698650 prefixEnd_1698650 290741304586628085921019 := by
  unfold tailWord_1698650
  simp only [CollatzResearch.WordTrace]
  refine ⟨15488713824022157792141351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41303236864059087445710269 15488713824022157792141351)
  ·
    refine ⟨23233070736033236688212027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15488713824022157792141351 23233070736033236688212027)
    ·
      refine ⟨34849606104049855032318041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23233070736033236688212027 34849606104049855032318041)
      ·
        refine ⟨26137204578037391274238531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34849606104049855032318041 26137204578037391274238531)
        ·
          refine ⟨39205806867056086911357797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26137204578037391274238531 39205806867056086911357797)
          ·
            refine ⟨7351088787573016295879587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39205806867056086911357797 7351088787573016295879587)
            ·
              refine ⟨11026633181359524443819381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351088787573016295879587 11026633181359524443819381)
              ·
                refine ⟨1033746860752455416608067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11026633181359524443819381 1033746860752455416608067)
                ·
                  refine ⟨1550620291128683124912101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033746860752455416608067 1550620291128683124912101)
                  ·
                    refine ⟨290741304586628085921019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1550620291128683124912101 290741304586628085921019)
                    ·
                      rfl

theorem cell23_1698650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_1698650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698650 prefixEnd_1698650 := by exact prefixLift 1698650
  have htrace : WordTrace (prefixWord ++ tailWord_1698650) baseStart_1698650 baseEnd_1698650 := by
    simpa [prefixWord, tailWord_1698650, baseEnd_1698650] using wordTrace_append hprefix tailTrace_1698650
  have hstable : (prefixWord ++ tailWord_1698650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698650).length < 2 ^ (prefixWord ++ tailWord_1698650).sum := by decide
  have hdescent : baseEnd_1698650 < baseStart_1698650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698663 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 6]
def baseStart_1698663 : Nat := 118140960795 + 1698663 * 2 ^ 59
def prefixEnd_1698663 : Nat := 4983230072969 + 3 ^ 40 * 1698663 * 2
def baseEnd_1698663 : Nat := 96914509889821411877833

theorem tailTrace_1698663 : CollatzResearch.WordTrace tailWord_1698663 prefixEnd_1698663 96914509889821411877833 := by
  unfold tailWord_1698663
  simp only [CollatzResearch.WordTrace]
  refine ⟨61955329445041534388788643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41303552963361022925859095 61955329445041534388788643)
  ·
    refine ⟨92932994167562301583182965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61955329445041534388788643 92932994167562301583182965)
    ·
      refine ⟨8712468203208965773423403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92932994167562301583182965 8712468203208965773423403)
      ·
        refine ⟨13068702304813448660135105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8712468203208965773423403 13068702304813448660135105)
        ·
          refine ⟨9801526728610086495101329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13068702304813448660135105 9801526728610086495101329)
          ·
            refine ⟨7351145046457564871325997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9801526728610086495101329 7351145046457564871325997)
            ·
              refine ⟨2756679392421586826747249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7351145046457564871325997 2756679392421586826747249)
              ·
                refine ⟨2067509544316190120060437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2756679392421586826747249 2067509544316190120060437)
                ·
                  refine ⟨96914509889821411877833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2067509544316190120060437 96914509889821411877833)
                  ·
                    rfl

theorem cell23_1698663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 6].length) (baseStart_1698663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698663 prefixEnd_1698663 := by exact prefixLift 1698663
  have htrace : WordTrace (prefixWord ++ tailWord_1698663) baseStart_1698663 baseEnd_1698663 := by
    simpa [prefixWord, tailWord_1698663, baseEnd_1698663] using wordTrace_append hprefix tailTrace_1698663
  have hstable : (prefixWord ++ tailWord_1698663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698663).length < 2 ^ (prefixWord ++ tailWord_1698663).sum := by decide
  have hdescent : baseEnd_1698663 < baseStart_1698663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698683 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 1, 5, 2]
def baseStart_1698683 : Nat := 118140960795 + 1698683 * 2 ^ 59
def prefixEnd_1698683 : Nat := 4983230072969 + 3 ^ 40 * 1698683 * 2
def baseEnd_1698683 : Nat := 872240858621482628650405

theorem tailTrace_1698683 : CollatzResearch.WordTrace tailWord_1698683 prefixEnd_1698683 872240858621482628650405 := by
  unfold tailWord_1698683
  simp only [CollatzResearch.WordTrace]
  refine ⟨61956058904969077804516703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41304039269979385203011135 61956058904969077804516703)
  ·
    refine ⟨92934088357453616706775055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61956058904969077804516703 92934088357453616706775055)
    ·
      refine ⟨139401132536180425060162583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92934088357453616706775055 139401132536180425060162583)
      ·
        refine ⟨209101698804270637590243875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139401132536180425060162583 209101698804270637590243875)
        ·
          refine ⟨313652548206405956385365813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209101698804270637590243875 313652548206405956385365813)
          ·
            refine ⟨29404926394350558411128045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 313652548206405956385365813 29404926394350558411128045)
            ·
              refine ⟨11026847397881459404173017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29404926394350558411128045 11026847397881459404173017)
              ·
                refine ⟨8270135548411094553129763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11026847397881459404173017 8270135548411094553129763)
                ·
                  refine ⟨12405203322616641829694645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8270135548411094553129763 12405203322616641829694645)
                  ·
                    refine ⟨1162987811495310171533873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12405203322616641829694645 1162987811495310171533873)
                    ·
                      refine ⟨872240858621482628650405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1162987811495310171533873 872240858621482628650405)
                      ·
                        rfl

theorem cell23_1698683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 5, 2].length) (baseStart_1698683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698683 prefixEnd_1698683 := by exact prefixLift 1698683
  have htrace : WordTrace (prefixWord ++ tailWord_1698683) baseStart_1698683 baseEnd_1698683 := by
    simpa [prefixWord, tailWord_1698683, baseEnd_1698683] using wordTrace_append hprefix tailTrace_1698683
  have hstable : (prefixWord ++ tailWord_1698683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698683).length < 2 ^ (prefixWord ++ tailWord_1698683).sum := by decide
  have hdescent : baseEnd_1698683 < baseStart_1698683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698693 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_1698693 : Nat := 118140960795 + 1698693 * 2 ^ 59
def prefixEnd_1698693 : Nat := 4983230072969 + 3 ^ 40 * 1698693 * 2
def baseEnd_1698693 : Nat := 290748664476009196508453

theorem tailTrace_1698693 : CollatzResearch.WordTrace tailWord_1698693 prefixEnd_1698693 290748664476009196508453 := by
  unfold tailWord_1698693
  simp only [CollatzResearch.WordTrace]
  refine ⟨61956423634932849512380733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41304282423288566341587155 61956423634932849512380733)
  ·
    refine ⟨23233658863099818567142775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61956423634932849512380733 23233658863099818567142775)
    ·
      refine ⟨34850488294649727850714163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23233658863099818567142775 34850488294649727850714163)
      ·
        refine ⟨52275732441974591776071245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34850488294649727850714163 52275732441974591776071245)
        ·
          refine ⟨19603399665740471916026717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52275732441974591776071245 19603399665740471916026717)
          ·
            refine ⟨7351274874652676968510019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19603399665740471916026717 7351274874652676968510019)
            ·
              refine ⟨11026912311979015452765029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351274874652676968510019 11026912311979015452765029)
              ·
                refine ⟨2067546058496065397393443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11026912311979015452765029 2067546058496065397393443)
                ·
                  refine ⟨3101319087744098096090165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067546058496065397393443 3101319087744098096090165)
                  ·
                    refine ⟨290748664476009196508453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3101319087744098096090165 290748664476009196508453)
                    ·
                      rfl

theorem cell23_1698693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_1698693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698693 prefixEnd_1698693 := by exact prefixLift 1698693
  have htrace : WordTrace (prefixWord ++ tailWord_1698693) baseStart_1698693 baseEnd_1698693 := by
    simpa [prefixWord, tailWord_1698693, baseEnd_1698693] using wordTrace_append hprefix tailTrace_1698693
  have hstable : (prefixWord ++ tailWord_1698693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698693).length < 2 ^ (prefixWord ++ tailWord_1698693).sum := by decide
  have hdescent : baseEnd_1698693 < baseStart_1698693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698723 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 4, 4]
def baseStart_1698723 : Nat := 118140960795 + 1698723 * 2 ^ 59
def prefixEnd_1698723 : Nat := 4983230072969 + 3 ^ 40 * 1698723 * 2
def baseEnd_1698723 : Nat := 290753799282554157383407

theorem tailTrace_1698723 : CollatzResearch.WordTrace tailWord_1698723 prefixEnd_1698723 290753799282554157383407 := by
  unfold tailWord_1698723
  simp only [CollatzResearch.WordTrace]
  refine ⟨61957517824824164635972823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41305011883216109757315215 61957517824824164635972823)
  ·
    refine ⟨92936276737236246953959235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61957517824824164635972823 92936276737236246953959235)
    ·
      refine ⟨139404415105854370430938853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92936276737236246953959235 139404415105854370430938853)
      ·
        refine ⟨26138327832347694455801035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139404415105854370430938853 26138327832347694455801035)
        ·
          refine ⟨39207491748521541683701553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26138327832347694455801035 39207491748521541683701553)
          ·
            refine ⟨29405618811391156262776165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39207491748521541683701553 29405618811391156262776165)
            ·
              refine ⟨5513553527135841799270531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29405618811391156262776165 5513553527135841799270531)
              ·
                refine ⟨8270330290703762698905797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513553527135841799270531 8270330290703762698905797)
                ·
                  refine ⟨1550686929506955506044837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8270330290703762698905797 1550686929506955506044837)
                  ·
                    refine ⟨290753799282554157383407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1550686929506955506044837 290753799282554157383407)
                    ·
                      rfl

theorem cell23_1698723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 4].length) (baseStart_1698723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698723 prefixEnd_1698723 := by exact prefixLift 1698723
  have htrace : WordTrace (prefixWord ++ tailWord_1698723) baseStart_1698723 baseEnd_1698723 := by
    simpa [prefixWord, tailWord_1698723, baseEnd_1698723] using wordTrace_append hprefix tailTrace_1698723
  have hstable : (prefixWord ++ tailWord_1698723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698723).length < 2 ^ (prefixWord ++ tailWord_1698723).sum := by decide
  have hdescent : baseEnd_1698723 < baseStart_1698723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698724 : List Nat := [2, 3, 1, 2, 1, 2, 5, 2, 1, 1, 3]
def baseStart_1698724 : Nat := 118140960795 + 1698724 * 2 ^ 59
def prefixEnd_1698724 : Nat := 4983230072969 + 3 ^ 40 * 1698724 * 2
def baseEnd_1698724 : Nat := 872261911328316968237717

theorem tailTrace_1698724 : CollatzResearch.WordTrace tailWord_1698724 prefixEnd_1698724 872261911328316968237717 := by
  unfold tailWord_1698724
  simp only [CollatzResearch.WordTrace]
  refine ⟨30978777148910270903379613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41305036198547027871172817 30978777148910270903379613)
  ·
    refine ⟨11617041430841351588767355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30978777148910270903379613 11617041430841351588767355)
    ·
      refine ⟨17425562146262027383151033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11617041430841351588767355 17425562146262027383151033)
      ·
        refine ⟨13069171609696520537363275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17425562146262027383151033 13069171609696520537363275)
        ·
          refine ⟨19603757414544780806044913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13069171609696520537363275 19603757414544780806044913)
          ·
            refine ⟨14702818060908585604533685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19603757414544780806044913 14702818060908585604533685)
            ·
              refine ⟨1378389193210179900425033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14702818060908585604533685 1378389193210179900425033)
              ·
                refine ⟨1033791894907634925318775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378389193210179900425033 1033791894907634925318775)
                ·
                  refine ⟨1550687842361452387978163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033791894907634925318775 1550687842361452387978163)
                  ·
                    refine ⟨2326031763542178581967245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1550687842361452387978163 2326031763542178581967245)
                    ·
                      refine ⟨872261911328316968237717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2326031763542178581967245 872261911328316968237717)
                      ·
                        rfl

theorem cell23_1698724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_1698724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698724 prefixEnd_1698724 := by exact prefixLift 1698724
  have htrace : WordTrace (prefixWord ++ tailWord_1698724) baseStart_1698724 baseEnd_1698724 := by
    simpa [prefixWord, tailWord_1698724, baseEnd_1698724] using wordTrace_append hprefix tailTrace_1698724
  have hstable : (prefixWord ++ tailWord_1698724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698724).length < 2 ^ (prefixWord ++ tailWord_1698724).sum := by decide
  have hdescent : baseEnd_1698724 < baseStart_1698724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698750 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_1698750 : Nat := 118140960795 + 1698750 * 2 ^ 59
def prefixEnd_1698750 : Nat := 4983230072969 + 3 ^ 40 * 1698750 * 2
def baseEnd_1698750 : Nat := 872275261825333866512597

theorem tailTrace_1698750 : CollatzResearch.WordTrace tailWord_1698750 prefixEnd_1698750 872275261825333866512597 := by
  unfold tailWord_1698750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7744812824465793530900713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41305668397150898831470469 7744812824465793530900713)
  ·
    refine ⟨5808609618349345148175535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7744812824465793530900713 5808609618349345148175535)
    ·
      refine ⟨8712914427524017722263303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5808609618349345148175535 8712914427524017722263303)
      ·
        refine ⟨13069371641286026583394955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8712914427524017722263303 13069371641286026583394955)
        ·
          refine ⟨19604057461929039875092433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13069371641286026583394955 19604057461929039875092433)
          ·
            refine ⟨14703043096446779906319325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19604057461929039875092433 14703043096446779906319325)
            ·
              refine ⟨5513641161167542464869747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14703043096446779906319325 5513641161167542464869747)
              ·
                refine ⟨8270461741751313697304621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513641161167542464869747 8270461741751313697304621)
                ·
                  refine ⟨3101423153156742636489233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8270461741751313697304621 3101423153156742636489233)
                  ·
                    refine ⟨2326067364867556977366925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3101423153156742636489233 2326067364867556977366925)
                    ·
                      refine ⟨872275261825333866512597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2326067364867556977366925 872275261825333866512597)
                      ·
                        rfl

theorem cell23_1698750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_1698750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698750 prefixEnd_1698750 := by exact prefixLift 1698750
  have htrace : WordTrace (prefixWord ++ tailWord_1698750) baseStart_1698750 baseEnd_1698750 := by
    simpa [prefixWord, tailWord_1698750, baseEnd_1698750] using wordTrace_append hprefix tailTrace_1698750
  have hstable : (prefixWord ++ tailWord_1698750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698750).length < 2 ^ (prefixWord ++ tailWord_1698750).sum := by decide
  have hdescent : baseEnd_1698750 < baseStart_1698750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698760 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_1698760 : Nat := 118140960795 + 1698760 * 2 ^ 59
def prefixEnd_1698760 : Nat := 4983230072969 + 3 ^ 40 * 1698760 * 2
def baseEnd_1698760 : Nat := 872280396631878827387551

theorem tailTrace_1698760 : CollatzResearch.WordTrace tailWord_1698760 prefixEnd_1698760 872280396631878827387551 := by
  unfold tailWord_1698760
  simp only [CollatzResearch.WordTrace]
  refine ⟨30979433662845059977534867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41305911550460079970046489 30979433662845059977534867)
  ·
    refine ⟨46469150494267589966302301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30979433662845059977534867 46469150494267589966302301)
    ·
      refine ⟨17425931435350346237363363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46469150494267589966302301 17425931435350346237363363)
      ·
        refine ⟨26138897153025519356045045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17425931435350346237363363 26138897153025519356045045)
        ·
          refine ⟨2450521608096142439629223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26138897153025519356045045 2450521608096142439629223)
          ·
            refine ⟨3675782412144213659443835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450521608096142439629223 3675782412144213659443835)
            ·
              refine ⟨5513673618216320489165753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675782412144213659443835 5513673618216320489165753)
              ·
                refine ⟨4135255213662240366874315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5513673618216320489165753 4135255213662240366874315)
                ·
                  refine ⟨6202882820493360550311473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135255213662240366874315 6202882820493360550311473)
                  ·
                    refine ⟨4652162115370020412733605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6202882820493360550311473 4652162115370020412733605)
                    ·
                      refine ⟨872280396631878827387551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4652162115370020412733605 872280396631878827387551)
                      ·
                        rfl

theorem cell23_1698760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_1698760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698760 prefixEnd_1698760 := by exact prefixLift 1698760
  have htrace : WordTrace (prefixWord ++ tailWord_1698760) baseStart_1698760 baseEnd_1698760 := by
    simpa [prefixWord, tailWord_1698760, baseEnd_1698760] using wordTrace_append hprefix tailTrace_1698760
  have hstable : (prefixWord ++ tailWord_1698760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698760).length < 2 ^ (prefixWord ++ tailWord_1698760).sum := by decide
  have hdescent : baseEnd_1698760 < baseStart_1698760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698763 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 3]
def baseStart_1698763 : Nat := 118140960795 + 1698763 * 2 ^ 59
def prefixEnd_1698763 : Nat := 4983230072969 + 3 ^ 40 * 1698763 * 2
def baseEnd_1698763 : Nat := 872281937073842315650037

theorem tailTrace_1698763 : CollatzResearch.WordTrace tailWord_1698763 prefixEnd_1698763 872281937073842315650037 := by
  unfold tailWord_1698763
  simp only [CollatzResearch.WordTrace]
  refine ⟨61958976744679251467428943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41305984496452834311619295 61958976744679251467428943)
  ·
    refine ⟨92938465117018877201143415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61958976744679251467428943 92938465117018877201143415)
    ·
      refine ⟨139407697675528315801715123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92938465117018877201143415 139407697675528315801715123)
      ·
        refine ⟨209111546513292473702572685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139407697675528315801715123 209111546513292473702572685)
        ·
          refine ⟨78416829942484677638464757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209111546513292473702572685 78416829942484677638464757)
          ·
            refine ⟨7351577807107938528606071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78416829942484677638464757 7351577807107938528606071)
            ·
              refine ⟨11027366710661907792909107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351577807107938528606071 11027366710661907792909107)
              ·
                refine ⟨16541050065992861689363661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11027366710661907792909107 16541050065992861689363661)
                ·
                  refine ⟨6202893774747323133511373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16541050065992861689363661 6202893774747323133511373)
                  ·
                    refine ⟨2326085165530246175066765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6202893774747323133511373 2326085165530246175066765)
                    ·
                      refine ⟨872281937073842315650037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2326085165530246175066765 872281937073842315650037)
                      ·
                        rfl

theorem cell23_1698763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 3].length) (baseStart_1698763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698763 prefixEnd_1698763 := by exact prefixLift 1698763
  have htrace : WordTrace (prefixWord ++ tailWord_1698763) baseStart_1698763 baseEnd_1698763 := by
    simpa [prefixWord, tailWord_1698763, baseEnd_1698763] using wordTrace_append hprefix tailTrace_1698763
  have hstable : (prefixWord ++ tailWord_1698763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698763).length < 2 ^ (prefixWord ++ tailWord_1698763).sum := by decide
  have hdescent : baseEnd_1698763 < baseStart_1698763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698764 : List Nat := [2, 2, 1, 4, 1, 1, 2, 5, 1, 2, 2]
def baseStart_1698764 : Nat := 118140960795 + 1698764 * 2 ^ 59
def prefixEnd_1698764 : Nat := 4983230072969 + 3 ^ 40 * 1698764 * 2
def baseEnd_1698764 : Nat := 872282450554496811737533

theorem tailTrace_1698764 : CollatzResearch.WordTrace tailWord_1698764 prefixEnd_1698764 872282450554496811737533 := by
  unfold tailWord_1698764
  simp only [CollatzResearch.WordTrace]
  refine ⟨30979506608837814319107673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41306008811783752425476897 30979506608837814319107673)
  ·
    refine ⟨23234629956628360739330755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30979506608837814319107673 23234629956628360739330755)
    ·
      refine ⟨34851944934942541108996133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23234629956628360739330755 34851944934942541108996133)
      ·
        refine ⟨6534739675301726457936775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34851944934942541108996133 6534739675301726457936775)
        ·
          refine ⟨9802109512952589686905163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6534739675301726457936775 9802109512952589686905163)
          ·
            refine ⟨14703164269428884530357745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9802109512952589686905163 14703164269428884530357745)
            ·
              refine ⟨11027373202071663397768309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14703164269428884530357745 11027373202071663397768309)
              ·
                refine ⟨1033816237694218443540779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11027373202071663397768309 1033816237694218443540779)
                ·
                  refine ⟨1550724356541327665311169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033816237694218443540779 1550724356541327665311169)
                  ·
                    refine ⟨1163043267405995748983377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1550724356541327665311169 1163043267405995748983377)
                    ·
                      refine ⟨872282450554496811737533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163043267405995748983377 872282450554496811737533)
                      ·
                        rfl

theorem cell23_1698764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_1698764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698764 prefixEnd_1698764 := by exact prefixLift 1698764
  have htrace : WordTrace (prefixWord ++ tailWord_1698764) baseStart_1698764 baseEnd_1698764 := by
    simpa [prefixWord, tailWord_1698764, baseEnd_1698764] using wordTrace_append hprefix tailTrace_1698764
  have hstable : (prefixWord ++ tailWord_1698764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698764).length < 2 ^ (prefixWord ++ tailWord_1698764).sum := by decide
  have hdescent : baseEnd_1698764 < baseStart_1698764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698767 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 1, 2, 3]
def baseStart_1698767 : Nat := 118140960795 + 1698767 * 2 ^ 59
def prefixEnd_1698767 : Nat := 4983230072969 + 3 ^ 40 * 1698767 * 2
def baseEnd_1698767 : Nat := 872283990996460300000019

theorem tailTrace_1698767 : CollatzResearch.WordTrace tailWord_1698767 prefixEnd_1698767 872283990996460300000019 := by
  unfold tailWord_1698767
  simp only [CollatzResearch.WordTrace]
  refine ⟨61959122636664760150574555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41306081757776506767049703 61959122636664760150574555)
  ·
    refine ⟨92938683954997140225861833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61959122636664760150574555 92938683954997140225861833)
    ·
      refine ⟨69704012966247855169396375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92938683954997140225861833 69704012966247855169396375)
      ·
        refine ⟨104556019449371782754094563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69704012966247855169396375 104556019449371782754094563)
        ·
          refine ⟨156834029174057674131141845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104556019449371782754094563 156834029174057674131141845)
          ·
            refine ⟨3675797558766976737448637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 156834029174057674131141845 3675797558766976737448637)
            ·
              refine ⟨1378424084537616276543239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3675797558766976737448637 1378424084537616276543239)
              ·
                refine ⟨2067636126806424414814859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378424084537616276543239 2067636126806424414814859)
                ·
                  refine ⟨3101454190209636622222289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067636126806424414814859 3101454190209636622222289)
                  ·
                    refine ⟨2326090642657227466666717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3101454190209636622222289 2326090642657227466666717)
                    ·
                      refine ⟨872283990996460300000019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2326090642657227466666717 872283990996460300000019)
                      ·
                        rfl

theorem cell23_1698767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 2, 3].length) (baseStart_1698767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698767 prefixEnd_1698767 := by exact prefixLift 1698767
  have htrace : WordTrace (prefixWord ++ tailWord_1698767) baseStart_1698767 baseEnd_1698767 := by
    simpa [prefixWord, tailWord_1698767, baseEnd_1698767] using wordTrace_append hprefix tailTrace_1698767
  have hstable : (prefixWord ++ tailWord_1698767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698767).length < 2 ^ (prefixWord ++ tailWord_1698767).sum := by decide
  have hdescent : baseEnd_1698767 < baseStart_1698767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698774 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1698774 : Nat := 118140960795 + 1698774 * 2 ^ 59
def prefixEnd_1698774 : Nat := 4983230072969 + 3 ^ 40 * 1698774 * 2
def baseEnd_1698774 : Nat := 290762528453680590870829

theorem tailTrace_1698774 : CollatzResearch.WordTrace tailWord_1698774 prefixEnd_1698774 290762528453680590870829 := by
  unfold tailWord_1698774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3872461121727462521629961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41306251965092933564052917 3872461121727462521629961)
  ·
    refine ⟨2904345841295596891222471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3872461121727462521629961 2904345841295596891222471)
    ·
      refine ⟨4356518761943395336833707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2904345841295596891222471 4356518761943395336833707)
      ·
        refine ⟨6534778142915093005250561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356518761943395336833707 6534778142915093005250561)
        ·
          refine ⟨4901083607186319753937921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6534778142915093005250561 4901083607186319753937921)
          ·
            refine ⟨3675812705389739815453441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4901083607186319753937921 3675812705389739815453441)
            ·
              refine ⟨2756859529042304861590081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675812705389739815453441 2756859529042304861590081)
              ·
                refine ⟨2067644646781728646192561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2756859529042304861590081 2067644646781728646192561)
                ·
                  refine ⟨1550733485086296484644421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2067644646781728646192561 1550733485086296484644421)
                  ·
                    refine ⟨290762528453680590870829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1550733485086296484644421 290762528453680590870829)
                    ·
                      rfl

theorem cell23_1698774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1698774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698774 prefixEnd_1698774 := by exact prefixLift 1698774
  have htrace : WordTrace (prefixWord ++ tailWord_1698774) baseStart_1698774 baseEnd_1698774 := by
    simpa [prefixWord, tailWord_1698774, baseEnd_1698774] using wordTrace_append hprefix tailTrace_1698774
  have hstable : (prefixWord ++ tailWord_1698774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698774).length < 2 ^ (prefixWord ++ tailWord_1698774).sum := by decide
  have hdescent : baseEnd_1698774 < baseStart_1698774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698781 : List Nat := [1, 4, 3, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_1698781 : Nat := 118140960795 + 1698781 * 2 ^ 59
def prefixEnd_1698781 : Nat := 4983230072969 + 3 ^ 40 * 1698781 * 2
def baseEnd_1698781 : Nat := 872291179725623245224955

theorem tailTrace_1698781 : CollatzResearch.WordTrace tailWord_1698781 prefixEnd_1698781 872291179725623245224955 := by
  unfold tailWord_1698781
  simp only [CollatzResearch.WordTrace]
  refine ⟨61959633258614040541584197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41306422172409360361056131 61959633258614040541584197)
  ·
    refine ⟨11617431235990132601547037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61959633258614040541584197 11617431235990132601547037)
    ·
      refine ⟨4356536713496299725580139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11617431235990132601547037 4356536713496299725580139)
      ·
        refine ⟨6534805070244449588370209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356536713496299725580139 6534805070244449588370209)
        ·
          refine ⟨4901103802683337191277657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6534805070244449588370209 4901103802683337191277657)
          ·
            refine ⟨3675827852012502893458243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4901103802683337191277657 3675827852012502893458243)
            ·
              refine ⟨5513741778018754340187365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675827852012502893458243 5513741778018754340187365)
              ·
                refine ⟨1033826583378516438785131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5513741778018754340187365 1033826583378516438785131)
                ·
                  refine ⟨1550739875067774658177697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033826583378516438785131 1550739875067774658177697)
                  ·
                    refine ⟨1163054906300830993633273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1550739875067774658177697 1163054906300830993633273)
                    ·
                      refine ⟨872291179725623245224955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163054906300830993633273 872291179725623245224955)
                      ·
                        rfl

theorem cell23_1698781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_1698781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698781 prefixEnd_1698781 := by exact prefixLift 1698781
  have htrace : WordTrace (prefixWord ++ tailWord_1698781) baseStart_1698781 baseEnd_1698781 := by
    simpa [prefixWord, tailWord_1698781, baseEnd_1698781] using wordTrace_append hprefix tailTrace_1698781
  have hstable : (prefixWord ++ tailWord_1698781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698781).length < 2 ^ (prefixWord ++ tailWord_1698781).sum := by decide
  have hdescent : baseEnd_1698781 < baseStart_1698781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698818 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1698818 : Nat := 118140960795 + 1698818 * 2 ^ 59
def prefixEnd_1698818 : Nat := 4983230072969 + 3 ^ 40 * 1698818 * 2
def baseEnd_1698818 : Nat := 872310178509839600462285

theorem tailTrace_1698818 : CollatzResearch.WordTrace tailWord_1698818 prefixEnd_1698818 872310178509839600462285 := by
  unfold tailWord_1698818
  simp only [CollatzResearch.WordTrace]
  refine ⟨15490245689869998965170277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41307321839653330573787405 15490245689869998965170277)
  ·
    refine ⟨2904421066850624805969427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15490245689869998965170277 2904421066850624805969427)
    ·
      refine ⟨4356631600275937208954141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2904421066850624805969427 4356631600275937208954141)
      ·
        refine ⟨1633736850103476453357803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4356631600275937208954141 1633736850103476453357803)
        ·
          refine ⟨2450605275155214680036705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1633736850103476453357803 2450605275155214680036705)
          ·
            refine ⟨1837953956366411010027529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2450605275155214680036705 1837953956366411010027529)
            ·
              refine ⟨1378465467274808257520647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1837953956366411010027529 1378465467274808257520647)
              ·
                refine ⟨2067698200912212386280971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378465467274808257520647 2067698200912212386280971)
                ·
                  refine ⟨3101547301368318579421457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067698200912212386280971 3101547301368318579421457)
                  ·
                    refine ⟨2326160476026238934566093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3101547301368318579421457 2326160476026238934566093)
                    ·
                      refine ⟨872310178509839600462285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2326160476026238934566093 872310178509839600462285)
                      ·
                        rfl

theorem cell23_1698818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1698818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698818 prefixEnd_1698818 := by exact prefixLift 1698818
  have htrace : WordTrace (prefixWord ++ tailWord_1698818) baseStart_1698818 baseEnd_1698818 := by
    simpa [prefixWord, tailWord_1698818, baseEnd_1698818] using wordTrace_append hprefix tailTrace_1698818
  have hstable : (prefixWord ++ tailWord_1698818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698818).length < 2 ^ (prefixWord ++ tailWord_1698818).sum := by decide
  have hdescent : baseEnd_1698818 < baseStart_1698818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698823 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1698823 : Nat := 118140960795 + 1698823 * 2 ^ 59
def prefixEnd_1698823 : Nat := 4983230072969 + 3 ^ 40 * 1698823 * 2
def baseEnd_1698823 : Nat := 872312745913112080899761

theorem tailTrace_1698823 : CollatzResearch.WordTrace tailWord_1698823 prefixEnd_1698823 872312745913112080899761 := by
  unfold tailWord_1698823
  simp only [CollatzResearch.WordTrace]
  refine ⟨61961165124461881714613123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41307443416307921143075415 61961165124461881714613123)
  ·
    refine ⟨92941747686692822571919685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61961165124461881714613123 92941747686692822571919685)
    ·
      refine ⟨17426577691254904232234941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92941747686692822571919685 17426577691254904232234941)
      ·
        refine ⟨6534966634220589087088103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17426577691254904232234941 6534966634220589087088103)
        ·
          refine ⟨9802449951330883630632155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6534966634220589087088103 9802449951330883630632155)
          ·
            refine ⟨14703674926996325445948233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9802449951330883630632155 14703674926996325445948233)
            ·
              refine ⟨11027756195247244084461175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14703674926996325445948233 11027756195247244084461175)
              ·
                refine ⟨16541634292870866126691763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11027756195247244084461175 16541634292870866126691763)
                ·
                  refine ⟨24812451439306299190037645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16541634292870866126691763 24812451439306299190037645)
                  ·
                    refine ⟨9304669289739862196264117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24812451439306299190037645 9304669289739862196264117)
                    ·
                      refine ⟨872312745913112080899761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9304669289739862196264117 872312745913112080899761)
                      ·
                        rfl

theorem cell23_1698823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1698823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698823 prefixEnd_1698823 := by exact prefixLift 1698823
  have htrace : WordTrace (prefixWord ++ tailWord_1698823) baseStart_1698823 baseEnd_1698823 := by
    simpa [prefixWord, tailWord_1698823, baseEnd_1698823] using wordTrace_append hprefix tailTrace_1698823
  have hstable : (prefixWord ++ tailWord_1698823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698823).length < 2 ^ (prefixWord ++ tailWord_1698823).sum := by decide
  have hdescent : baseEnd_1698823 < baseStart_1698823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698824 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 1, 3, 2]
def baseStart_1698824 : Nat := 118140960795 + 1698824 * 2 ^ 59
def prefixEnd_1698824 : Nat := 4983230072969 + 3 ^ 40 * 1698824 * 2
def baseEnd_1698824 : Nat := 872313259393766576987257

theorem tailTrace_1698824 : CollatzResearch.WordTrace tailWord_1698824 prefixEnd_1698824 872313259393766576987257 := by
  unfold tailWord_1698824
  simp only [CollatzResearch.WordTrace]
  refine ⟨30980600798729129442699763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41307467731638839256933017 30980600798729129442699763)
  ·
    refine ⟨46470901198093694164049645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30980600798729129442699763 46470901198093694164049645)
    ·
      refine ⟨17426587949285135311518617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46470901198093694164049645 17426587949285135311518617)
      ·
        refine ⟨13069940961963851483638963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17426587949285135311518617 13069940961963851483638963)
        ·
          refine ⟨19604911442945777225458445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13069940961963851483638963 19604911442945777225458445)
          ·
            refine ⟨7351841791104666459546917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19604911442945777225458445 7351841791104666459546917)
            ·
              refine ⟨1378470335832124961165047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7351841791104666459546917 1378470335832124961165047)
              ·
                refine ⟨2067705503748187441747571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378470335832124961165047 2067705503748187441747571)
                ·
                  refine ⟨3101558255622281162621357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067705503748187441747571 3101558255622281162621357)
                  ·
                    refine ⟨1163084345858355435983009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101558255622281162621357 1163084345858355435983009)
                    ·
                      refine ⟨872313259393766576987257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163084345858355435983009 872313259393766576987257)
                      ·
                        rfl

theorem cell23_1698824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_1698824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698824 prefixEnd_1698824 := by exact prefixLift 1698824
  have htrace : WordTrace (prefixWord ++ tailWord_1698824) baseStart_1698824 baseEnd_1698824 := by
    simpa [prefixWord, tailWord_1698824, baseEnd_1698824] using wordTrace_append hprefix tailTrace_1698824
  have hstable : (prefixWord ++ tailWord_1698824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698824).length < 2 ^ (prefixWord ++ tailWord_1698824).sum := by decide
  have hdescent : baseEnd_1698824 < baseStart_1698824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698850 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1698850 : Nat := 118140960795 + 1698850 * 2 ^ 59
def prefixEnd_1698850 : Nat := 4983230072969 + 3 ^ 40 * 1698850 * 2
def baseEnd_1698850 : Nat := 872326609890783475262137

theorem tailTrace_1698850 : CollatzResearch.WordTrace tailWord_1698850 prefixEnd_1698850 872326609890783475262137 := by
  unfold tailWord_1698850
  simp only [CollatzResearch.WordTrace]
  refine ⟨15490537473841016331461501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41308099930242710217230669 15490537473841016331461501)
  ·
    refine ⟨5808951552690381124298063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15490537473841016331461501 5808951552690381124298063)
    ·
      refine ⟨8713427329035571686447095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5808951552690381124298063 8713427329035571686447095)
      ·
        refine ⟨13070140993553357529670643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8713427329035571686447095 13070140993553357529670643)
        ·
          refine ⟨19605211490330036294505965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13070140993553357529670643 19605211490330036294505965)
          ·
            refine ⟨7351954308873763610439737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19605211490330036294505965 7351954308873763610439737)
            ·
              refine ⟨5513965731655322707829803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7351954308873763610439737 5513965731655322707829803)
              ·
                refine ⟨8270948597482984061744705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513965731655322707829803 8270948597482984061744705)
                ·
                  refine ⟨6203211448112238046308529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8270948597482984061744705 6203211448112238046308529)
                  ·
                    refine ⟨4652408586084178534731397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6203211448112238046308529 4652408586084178534731397)
                    ·
                      refine ⟨872326609890783475262137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4652408586084178534731397 872326609890783475262137)
                      ·
                        rfl

theorem cell23_1698850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1698850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698850 prefixEnd_1698850 := by exact prefixLift 1698850
  have htrace : WordTrace (prefixWord ++ tailWord_1698850) baseStart_1698850 baseEnd_1698850 := by
    simpa [prefixWord, tailWord_1698850, baseEnd_1698850] using wordTrace_append hprefix tailTrace_1698850
  have hstable : (prefixWord ++ tailWord_1698850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698850).length < 2 ^ (prefixWord ++ tailWord_1698850).sum := by decide
  have hdescent : baseEnd_1698850 < baseStart_1698850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698877 : List Nat := [1, 4, 1, 3, 1, 2, 3, 3, 5]
def baseStart_1698877 : Nat := 118140960795 + 1698877 * 2 ^ 59
def prefixEnd_1698877 : Nat := 4983230072969 + 3 ^ 40 * 1698877 * 2
def baseEnd_1698877 : Nat := 96926719318717207736057

theorem tailTrace_1698877 : CollatzResearch.WordTrace tailWord_1698877 prefixEnd_1698877 96926719318717207736057 := by
  unfold tailWord_1698877
  simp only [CollatzResearch.WordTrace]
  refine ⟨61963134666266248937078885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41308756444177499291385923 61963134666266248937078885)
  ·
    refine ⟨11618087749924921675702291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61963134666266248937078885 11618087749924921675702291)
    ·
      refine ⟨17427131624887382513553437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11618087749924921675702291 17427131624887382513553437)
      ·
        refine ⟨6535174359332768442582539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17427131624887382513553437 6535174359332768442582539)
        ·
          refine ⟨9802761538999152663873809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6535174359332768442582539 9802761538999152663873809)
          ·
            refine ⟨7352071154249364497905357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9802761538999152663873809 7352071154249364497905357)
            ·
              refine ⟨2757026682843511686714509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7352071154249364497905357 2757026682843511686714509)
              ·
                refine ⟨1033885006066316882517941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2757026682843511686714509 1033885006066316882517941)
                ·
                  refine ⟨96926719318717207736057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1033885006066316882517941 96926719318717207736057)
                  ·
                    rfl

theorem cell23_1698877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_1698877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698877 prefixEnd_1698877 := by exact prefixLift 1698877
  have htrace : WordTrace (prefixWord ++ tailWord_1698877) baseStart_1698877 baseEnd_1698877 := by
    simpa [prefixWord, tailWord_1698877, baseEnd_1698877] using wordTrace_append hprefix tailTrace_1698877
  have hstable : (prefixWord ++ tailWord_1698877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698877).length < 2 ^ (prefixWord ++ tailWord_1698877).sum := by decide
  have hdescent : baseEnd_1698877 < baseStart_1698877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698883 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 5]
def baseStart_1698883 : Nat := 118140960795 + 1698883 * 2 ^ 59
def prefixEnd_1698883 : Nat := 4983230072969 + 3 ^ 40 * 1698883 * 2
def baseEnd_1698883 : Nat := 872343554752381846149485

theorem tailTrace_1698883 : CollatzResearch.WordTrace tailWord_1698883 prefixEnd_1698883 872343554752381846149485 := by
  unfold tailWord_1698883
  simp only [CollatzResearch.WordTrace]
  refine ⟨61963353504244511961797303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41308902336163007974531535 61963353504244511961797303)
  ·
    refine ⟨92945030256366767942695955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61963353504244511961797303 92945030256366767942695955)
    ·
      refine ⟨139417545384550151914043933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92945030256366767942695955 139417545384550151914043933)
      ·
        refine ⟨52281579519206306967766475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139417545384550151914043933 52281579519206306967766475)
        ·
          refine ⟨78422369278809460451649713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52281579519206306967766475 78422369278809460451649713)
          ·
            refine ⟨58816776959107095338737285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78422369278809460451649713 58816776959107095338737285)
            ·
              refine ⟨11028145679832580376013241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58816776959107095338737285 11028145679832580376013241)
              ·
                refine ⟨8271109259874435282009931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11028145679832580376013241 8271109259874435282009931)
                ·
                  refine ⟨12406663889811652923014897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8271109259874435282009931 12406663889811652923014897)
                  ·
                    refine ⟨9304997917358739692261173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12406663889811652923014897 9304997917358739692261173)
                    ·
                      refine ⟨872343554752381846149485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9304997917358739692261173 872343554752381846149485)
                      ·
                        rfl

theorem cell23_1698883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_1698883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698883 prefixEnd_1698883 := by exact prefixLift 1698883
  have htrace : WordTrace (prefixWord ++ tailWord_1698883) baseStart_1698883 baseEnd_1698883 := by
    simpa [prefixWord, tailWord_1698883, baseEnd_1698883] using wordTrace_append hprefix tailTrace_1698883
  have hstable : (prefixWord ++ tailWord_1698883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698883).length < 2 ^ (prefixWord ++ tailWord_1698883).sum := by decide
  have hdescent : baseEnd_1698883 < baseStart_1698883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698954 : List Nat := [3, 1, 2, 3, 1, 1, 3, 4, 1, 4]
def baseStart_1698954 : Nat := 118140960795 + 1698954 * 2 ^ 59
def prefixEnd_1698954 : Nat := 4983230072969 + 3 ^ 40 * 1698954 * 2
def baseEnd_1698954 : Nat := 290793337292950356120553

theorem tailTrace_1698954 : CollatzResearch.WordTrace tailWord_1698954 prefixEnd_1698954 290793337292950356120553 := by
  unfold tailWord_1698954
  simp only [CollatzResearch.WordTrace]
  refine ⟨15491485771746822771907979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41310628724658194058421277 15491485771746822771907979)
  ·
    refine ⟨23237228657620234157861969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15491485771746822771907979 23237228657620234157861969)
    ·
      refine ⟨17427921493215175618396477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23237228657620234157861969 17427921493215175618396477)
      ·
        refine ⟨6535470559955690856898679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17427921493215175618396477 6535470559955690856898679)
        ·
          refine ⟨9803205839933536285348019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6535470559955690856898679 9803205839933536285348019)
          ·
            refine ⟨14704808759900304428022029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9803205839933536285348019 14704808759900304428022029)
            ·
              refine ⟨5514303284962614160508261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14704808759900304428022029 5514303284962614160508261)
              ·
                refine ⟨1033931865930490155095299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5514303284962614160508261 1033931865930490155095299)
                ·
                  refine ⟨1550897798895735232642949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033931865930490155095299 1550897798895735232642949)
                  ·
                    refine ⟨290793337292950356120553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1550897798895735232642949 290793337292950356120553)
                    ·
                      rfl

theorem cell23_1698954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_1698954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1698954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1698954 prefixEnd_1698954 := by exact prefixLift 1698954
  have htrace : WordTrace (prefixWord ++ tailWord_1698954) baseStart_1698954 baseEnd_1698954 := by
    simpa [prefixWord, tailWord_1698954, baseEnd_1698954] using wordTrace_append hprefix tailTrace_1698954
  have hstable : (prefixWord ++ tailWord_1698954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698954).length < 2 ^ (prefixWord ++ tailWord_1698954).sum := by decide
  have hdescent : baseEnd_1698954 < baseStart_1698954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699000 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_1699000 : Nat := 118140960795 + 1699000 * 2 ^ 59
def prefixEnd_1699000 : Nat := 4983230072969 + 3 ^ 40 * 1699000 * 2
def baseEnd_1699000 : Nat := 872403631988957888386447

theorem tailTrace_1699000 : CollatzResearch.WordTrace tailWord_1699000 prefixEnd_1699000 872403631988957888386447 := by
  unfold tailWord_1699000
  simp only [CollatzResearch.WordTrace]
  refine ⟨30983810422410320471903227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41311747229880427295870969 30983810422410320471903227)
  ·
    refine ⟨46475715633615480707854841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30983810422410320471903227 46475715633615480707854841)
    ·
      refine ⟨34856786725211610530891131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46475715633615480707854841 34856786725211610530891131)
      ·
        refine ⟨52285180087817415796336697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34856786725211610530891131 52285180087817415796336697)
        ·
          refine ⟨39213885065863061847252523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52285180087817415796336697 39213885065863061847252523)
          ·
            refine ⟨58820827598794592770878785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39213885065863061847252523 58820827598794592770878785)
            ·
              refine ⟨44115620699095944578159089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58820827598794592770878785 44115620699095944578159089)
              ·
                refine ⟨33086715524321958433619317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44115620699095944578159089 33086715524321958433619317)
                ·
                  refine ⟨3101879580405183603151811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33086715524321958433619317 3101879580405183603151811)
                  ·
                    refine ⟨4652819370607775404727717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3101879580405183603151811 4652819370607775404727717)
                    ·
                      refine ⟨872403631988957888386447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4652819370607775404727717 872403631988957888386447)
                      ·
                        rfl

theorem cell23_1699000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_1699000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699000 prefixEnd_1699000 := by exact prefixLift 1699000
  have htrace : WordTrace (prefixWord ++ tailWord_1699000) baseStart_1699000 baseEnd_1699000 := by
    simpa [prefixWord, tailWord_1699000, baseEnd_1699000] using wordTrace_append hprefix tailTrace_1699000
  have hstable : (prefixWord ++ tailWord_1699000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699000).length < 2 ^ (prefixWord ++ tailWord_1699000).sum := by decide
  have hdescent : baseEnd_1699000 < baseStart_1699000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699040 : List Nat := [2, 1, 1, 3, 1, 5, 1, 9]
def baseStart_1699040 : Nat := 118140960795 + 1699040 * 2 ^ 59
def prefixEnd_1699040 : Nat := 4983230072969 + 3 ^ 40 * 1699040 * 2
def baseEnd_1699040 : Nat := 32312006341301397477269

theorem tailTrace_1699040 : CollatzResearch.WordTrace tailWord_1699040 prefixEnd_1699040 32312006341301397477269 := by
  unfold tailWord_1699040
  simp only [CollatzResearch.WordTrace]
  refine ⟨30984539882337863887631287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41312719843117151850175049 30984539882337863887631287)
  ·
    refine ⟨46476809823506795831446931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30984539882337863887631287 46476809823506795831446931)
    ·
      refine ⟨69715214735260193747170397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46476809823506795831446931 69715214735260193747170397)
      ·
        refine ⟨26143205525722572655188899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69715214735260193747170397 26143205525722572655188899)
        ·
          refine ⟨39214808288583858982783349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26143205525722572655188899 39214808288583858982783349)
          ·
            refine ⟨3676388277054736779635939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39214808288583858982783349 3676388277054736779635939)
            ·
              refine ⟨5514582415582105169453909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3676388277054736779635939 5514582415582105169453909)
              ·
                refine ⟨32312006341301397477269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5514582415582105169453909 32312006341301397477269)
                ·
                  rfl

theorem cell23_1699040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 9].length) (baseStart_1699040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699040 prefixEnd_1699040 := by exact prefixLift 1699040
  have htrace : WordTrace (prefixWord ++ tailWord_1699040) baseStart_1699040 baseEnd_1699040 := by
    simpa [prefixWord, tailWord_1699040, baseEnd_1699040] using wordTrace_append hprefix tailTrace_1699040
  have hstable : (prefixWord ++ tailWord_1699040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699040).length < 2 ^ (prefixWord ++ tailWord_1699040).sum := by decide
  have hdescent : baseEnd_1699040 < baseStart_1699040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699045 : List Nat := [1, 3, 1, 4, 4, 1, 1, 3, 1, 1, 3]
def baseStart_1699045 : Nat := 118140960795 + 1699045 * 2 ^ 59
def prefixEnd_1699045 : Nat := 4983230072969 + 3 ^ 40 * 1699045 * 2
def baseEnd_1699045 : Nat := 872426738618410212323741

theorem tailTrace_1699045 : CollatzResearch.WordTrace tailWord_1699045 prefixEnd_1699045 872426738618410212323741 := by
  unfold tailWord_1699045
  simp only [CollatzResearch.WordTrace]
  refine ⟨61969262129657613629194589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41312841419771742419463059 61969262129657613629194589)
  ·
    refine ⟨23238473298621605110947971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61969262129657613629194589 23238473298621605110947971)
    ·
      refine ⟨34857709947932407666421957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23238473298621605110947971 34857709947932407666421957)
      ·
        refine ⟨6535820615237326437454117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34857709947932407666421957 6535820615237326437454117)
        ·
          refine ⟨1225466365356998707022647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6535820615237326437454117 1225466365356998707022647)
          ·
            refine ⟨1838199548035498060533971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225466365356998707022647 1838199548035498060533971)
            ·
              refine ⟨2757299322053247090800957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838199548035498060533971 2757299322053247090800957)
              ·
                refine ⟨1033987245769967659050359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2757299322053247090800957 1033987245769967659050359)
                ·
                  refine ⟨1550980868654951488575539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033987245769967659050359 1550980868654951488575539)
                  ·
                    refine ⟨2326471302982427232863309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1550980868654951488575539 2326471302982427232863309)
                    ·
                      refine ⟨872426738618410212323741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2326471302982427232863309 872426738618410212323741)
                      ·
                        rfl

theorem cell23_1699045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_1699045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699045 prefixEnd_1699045 := by exact prefixLift 1699045
  have htrace : WordTrace (prefixWord ++ tailWord_1699045) baseStart_1699045 baseEnd_1699045 := by
    simpa [prefixWord, tailWord_1699045, baseEnd_1699045] using wordTrace_append hprefix tailTrace_1699045
  have hstable : (prefixWord ++ tailWord_1699045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699045).length < 2 ^ (prefixWord ++ tailWord_1699045).sum := by decide
  have hdescent : baseEnd_1699045 < baseStart_1699045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699054 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_1699054 : Nat := 118140960795 + 1699054 * 2 ^ 59
def prefixEnd_1699054 : Nat := 4983230072969 + 3 ^ 40 * 1699054 * 2
def baseEnd_1699054 : Nat := 872431359944300677111199

theorem tailTrace_1699054 : CollatzResearch.WordTrace tailWord_1699054 prefixEnd_1699054 872431359944300677111199 := by
  unfold tailWord_1699054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7746198798328126020784027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41313060257750005444181477 7746198798328126020784027)
  ·
    refine ⟨11619298197492189031176041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7746198798328126020784027 11619298197492189031176041)
    ·
      refine ⟨8714473648119141773382031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11619298197492189031176041 8714473648119141773382031)
      ·
        refine ⟨13071710472178712660073047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8714473648119141773382031 13071710472178712660073047)
        ·
          refine ⟨19607565708268068990109571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071710472178712660073047 19607565708268068990109571)
          ·
            refine ⟨29411348562402103485164357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19607565708268068990109571 29411348562402103485164357)
            ·
              refine ⟨5514627855450394403468317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29411348562402103485164357 5514627855450394403468317)
              ·
                refine ⟨2067985445793897901300619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5514627855450394403468317 2067985445793897901300619)
                ·
                  refine ⟨3101978168690846851950929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067985445793897901300619 3101978168690846851950929)
                  ·
                    refine ⟨2326483626518135138963197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3101978168690846851950929 2326483626518135138963197)
                    ·
                      refine ⟨872431359944300677111199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2326483626518135138963197 872431359944300677111199)
                      ·
                        rfl

theorem cell23_1699054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_1699054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699054 prefixEnd_1699054 := by exact prefixLift 1699054
  have htrace : WordTrace (prefixWord ++ tailWord_1699054) baseStart_1699054 baseEnd_1699054 := by
    simpa [prefixWord, tailWord_1699054, baseEnd_1699054] using wordTrace_append hprefix tailTrace_1699054
  have hstable : (prefixWord ++ tailWord_1699054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699054).length < 2 ^ (prefixWord ++ tailWord_1699054).sum := by decide
  have hdescent : baseEnd_1699054 < baseStart_1699054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699068 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 3, 2, 2]
def baseStart_1699068 : Nat := 118140960795 + 1699068 * 2 ^ 59
def prefixEnd_1699068 : Nat := 4983230072969 + 3 ^ 40 * 1699068 * 2
def baseEnd_1699068 : Nat := 872438548673463622336135

theorem tailTrace_1699068 : CollatzResearch.WordTrace tailWord_1699068 prefixEnd_1699068 872438548673463622336135 := by
  unfold tailWord_1699068
  simp only [CollatzResearch.WordTrace]
  refine ⟨30985050504287144278640929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41313400672382859038187905 30985050504287144278640929)
  ·
    refine ⟨23238787878215358208980697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30985050504287144278640929 23238787878215358208980697)
    ·
      refine ⟨17429090908661518656735523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23238787878215358208980697 17429090908661518656735523)
      ·
        refine ⟨26143636362992277985103285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17429090908661518656735523 26143636362992277985103285)
        ·
          refine ⟨2450965909030526061103433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26143636362992277985103285 2450965909030526061103433)
          ·
            refine ⟨1838224431772894545827575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2450965909030526061103433 1838224431772894545827575)
            ·
              refine ⟨2757336647659341818741363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838224431772894545827575 2757336647659341818741363)
              ·
                refine ⟨4136004971489012728112045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757336647659341818741363 4136004971489012728112045)
                ·
                  refine ⟨1551001864308379773042017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4136004971489012728112045 1551001864308379773042017)
                  ·
                    refine ⟨1163251398231284829781513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1551001864308379773042017 1163251398231284829781513)
                    ·
                      refine ⟨872438548673463622336135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163251398231284829781513 872438548673463622336135)
                      ·
                        rfl

theorem cell23_1699068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_1699068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699068 prefixEnd_1699068 := by exact prefixLift 1699068
  have htrace : WordTrace (prefixWord ++ tailWord_1699068) baseStart_1699068 baseEnd_1699068 := by
    simpa [prefixWord, tailWord_1699068, baseEnd_1699068] using wordTrace_append hprefix tailTrace_1699068
  have hstable : (prefixWord ++ tailWord_1699068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699068).length < 2 ^ (prefixWord ++ tailWord_1699068).sum := by decide
  have hdescent : baseEnd_1699068 < baseStart_1699068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699074 : List Nat := [3, 4, 1, 1, 3, 1, 2, 8]
def baseStart_1699074 : Nat := 118140960795 + 1699074 * 2 ^ 59
def prefixEnd_1699074 : Nat := 4983230072969 + 3 ^ 40 * 1699074 * 2
def baseEnd_1699074 : Nat := 32312652946570022180041

theorem tailTrace_1699074 : CollatzResearch.WordTrace tailWord_1699074 prefixEnd_1699074 32312652946570022180041 := by
  unfold tailWord_1699074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15492579961638137895500069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41313546564368367721333517 15492579961638137895500069)
  ·
    refine ⟨2904858742807150855406263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15492579961638137895500069 2904858742807150855406263)
    ·
      refine ⟨4357288114210726283109395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2904858742807150855406263 4357288114210726283109395)
      ·
        refine ⟨6535932171316089424664093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4357288114210726283109395 6535932171316089424664093)
        ·
          refine ⟨2450974564243533534249035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6535932171316089424664093 2450974564243533534249035)
          ·
            refine ⟨3676461846365300301373553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450974564243533534249035 3676461846365300301373553)
            ·
              refine ⟨2757346384773975226030165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3676461846365300301373553 2757346384773975226030165)
              ·
                refine ⟨32312652946570022180041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2757346384773975226030165 32312652946570022180041)
                ·
                  rfl

theorem cell23_1699074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 8].length) (baseStart_1699074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699074 prefixEnd_1699074 := by exact prefixLift 1699074
  have htrace : WordTrace (prefixWord ++ tailWord_1699074) baseStart_1699074 baseEnd_1699074 := by
    simpa [prefixWord, tailWord_1699074, baseEnd_1699074] using wordTrace_append hprefix tailTrace_1699074
  have hstable : (prefixWord ++ tailWord_1699074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699074).length < 2 ^ (prefixWord ++ tailWord_1699074).sum := by decide
  have hdescent : baseEnd_1699074 < baseStart_1699074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699175 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_1699175 : Nat := 118140960795 + 1699175 * 2 ^ 59
def prefixEnd_1699175 : Nat := 4983230072969 + 3 ^ 40 * 1699175 * 2
def baseEnd_1699175 : Nat := 872493491103494703698143

theorem tailTrace_1699175 : CollatzResearch.WordTrace tailWord_1699175 prefixEnd_1699175 872493491103494703698143 := by
  unfold tailWord_1699175
  simp only [CollatzResearch.WordTrace]
  refine ⟨61974003619186645831426979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41316002412791097220951319 61974003619186645831426979)
  ·
    refine ⟨92961005428779968747140469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61974003619186645831426979 92961005428779968747140469)
    ·
      refine ⟨8715094258948122070044419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92961005428779968747140469 8715094258948122070044419)
      ·
        refine ⟨13072641388422183105066629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8715094258948122070044419 13072641388422183105066629)
        ·
          refine ⟨2451120260329159332199993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13072641388422183105066629 2451120260329159332199993)
          ·
            refine ⟨1838340195246869499149995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2451120260329159332199993 1838340195246869499149995)
            ·
              refine ⟨2757510292870304248724993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838340195246869499149995 2757510292870304248724993)
              ·
                refine ⟨2068132719652728186543745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2757510292870304248724993 2068132719652728186543745)
                ·
                  refine ⟨1551099539739546139907809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2068132719652728186543745 1551099539739546139907809)
                  ·
                    refine ⟨1163324654804659604930857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1551099539739546139907809 1163324654804659604930857)
                    ·
                      refine ⟨872493491103494703698143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163324654804659604930857 872493491103494703698143)
                      ·
                        rfl

theorem cell23_1699175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_1699175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699175 prefixEnd_1699175 := by exact prefixLift 1699175
  have htrace : WordTrace (prefixWord ++ tailWord_1699175) baseStart_1699175 baseEnd_1699175 := by
    simpa [prefixWord, tailWord_1699175, baseEnd_1699175] using wordTrace_append hprefix tailTrace_1699175
  have hstable : (prefixWord ++ tailWord_1699175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699175).length < 2 ^ (prefixWord ++ tailWord_1699175).sum := by decide
  have hdescent : baseEnd_1699175 < baseStart_1699175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699197 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_1699197 : Nat := 118140960795 + 1699197 * 2 ^ 59
def prefixEnd_1699197 : Nat := 4983230072969 + 3 ^ 40 * 1699197 * 2
def baseEnd_1699197 : Nat := 872504787677893617623041

theorem tailTrace_1699197 : CollatzResearch.WordTrace tailWord_1699197 prefixEnd_1699197 872504787677893617623041 := by
  unfold tailWord_1699197
  simp only [CollatzResearch.WordTrace]
  refine ⟨61974806025106943588727845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41316537350071295725818563 61974806025106943588727845)
  ·
    refine ⟨11620276129707551922886471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61974806025106943588727845 11620276129707551922886471)
    ·
      refine ⟨17430414194561327884329707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11620276129707551922886471 17430414194561327884329707)
      ·
        refine ⟨26145621291841991826494561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17430414194561327884329707 26145621291841991826494561)
        ·
          refine ⟨19609215968881493869870921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26145621291841991826494561 19609215968881493869870921)
          ·
            refine ⟨14706911976661120402403191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19609215968881493869870921 14706911976661120402403191)
            ·
              refine ⟨22060367964991680603604787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14706911976661120402403191 22060367964991680603604787)
              ·
                refine ⟨33090551947487520905407181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22060367964991680603604787 33090551947487520905407181)
                ·
                  refine ⟨12408956980307820339527693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33090551947487520905407181 12408956980307820339527693)
                  ·
                    refine ⟨4653358867615432627322885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12408956980307820339527693 4653358867615432627322885)
                    ·
                      refine ⟨872504787677893617623041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4653358867615432627322885 872504787677893617623041)
                      ·
                        rfl

theorem cell23_1699197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_1699197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699197 prefixEnd_1699197 := by exact prefixLift 1699197
  have htrace : WordTrace (prefixWord ++ tailWord_1699197) baseStart_1699197 baseEnd_1699197 := by
    simpa [prefixWord, tailWord_1699197, baseEnd_1699197] using wordTrace_append hprefix tailTrace_1699197
  have hstable : (prefixWord ++ tailWord_1699197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699197).length < 2 ^ (prefixWord ++ tailWord_1699197).sum := by decide
  have hdescent : baseEnd_1699197 < baseStart_1699197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699268 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1699268 : Nat := 118140960795 + 1699268 * 2 ^ 59
def prefixEnd_1699268 : Nat := 4983230072969 + 3 ^ 40 * 1699268 * 2
def baseEnd_1699268 : Nat := 872541244804362839835215

theorem tailTrace_1699268 : CollatzResearch.WordTrace tailWord_1699268 prefixEnd_1699268 872541244804362839835215 := by
  unfold tailWord_1699268
  simp only [CollatzResearch.WordTrace]
  refine ⟨30988697803924861357281229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41318263738566481809708305 30988697803924861357281229)
  ·
    refine ⟨11620761676471823008980461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30988697803924861357281229 11620761676471823008980461)
    ·
      refine ⟨4357785628676933628367673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11620761676471823008980461 4357785628676933628367673)
      ·
        refine ⟨3268339221507700221275755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4357785628676933628367673 3268339221507700221275755)
        ·
          refine ⟨4902508832261550331913633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268339221507700221275755 4902508832261550331913633)
          ·
            refine ⟨3676881624196162748935225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4902508832261550331913633 3676881624196162748935225)
            ·
              refine ⟨2757661218147122061701419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3676881624196162748935225 2757661218147122061701419)
              ·
                refine ⟨4136491827220683092552129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757661218147122061701419 4136491827220683092552129)
                ·
                  refine ⟨3102368870415512319414097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4136491827220683092552129 3102368870415512319414097)
                  ·
                    refine ⟨2326776652811634239560573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3102368870415512319414097 2326776652811634239560573)
                    ·
                      refine ⟨872541244804362839835215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2326776652811634239560573 872541244804362839835215)
                      ·
                        rfl

theorem cell23_1699268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1699268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699268 prefixEnd_1699268 := by exact prefixLift 1699268
  have htrace : WordTrace (prefixWord ++ tailWord_1699268) baseStart_1699268 baseEnd_1699268 := by
    simpa [prefixWord, tailWord_1699268, baseEnd_1699268] using wordTrace_append hprefix tailTrace_1699268
  have hstable : (prefixWord ++ tailWord_1699268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699268).length < 2 ^ (prefixWord ++ tailWord_1699268).sum := by decide
  have hdescent : baseEnd_1699268 < baseStart_1699268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699304 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1699304 : Nat := 118140960795 + 1699304 * 2 ^ 59
def prefixEnd_1699304 : Nat := 4983230072969 + 3 ^ 40 * 1699304 * 2
def baseEnd_1699304 : Nat := 872559730107924698985049

theorem tailTrace_1699304 : CollatzResearch.WordTrace tailWord_1699304 prefixEnd_1699304 872559730107924698985049 := by
  unfold tailWord_1699304
  simp only [CollatzResearch.WordTrace]
  refine ⟨30989354317859650431436483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41319139090479533908581977 30989354317859650431436483)
  ·
    refine ⟨46484031476789475647154725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30989354317859650431436483 46484031476789475647154725)
    ·
      refine ⟨8715755901898026683841511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46484031476789475647154725 8715755901898026683841511)
      ·
        refine ⟨13073633852847040025762267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8715755901898026683841511 13073633852847040025762267)
        ·
          refine ⟨19610450779270560038643401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13073633852847040025762267 19610450779270560038643401)
          ·
            refine ⟨14707838084452920028982551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19610450779270560038643401 14707838084452920028982551)
            ·
              refine ⟨22061757126679380043473827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14707838084452920028982551 22061757126679380043473827)
              ·
                refine ⟨33092635690019070065210741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22061757126679380043473827 33092635690019070065210741)
                ·
                  refine ⟨3102434595939287818613507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33092635690019070065210741 3102434595939287818613507)
                  ·
                    refine ⟨4653651893908931727920261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3102434595939287818613507 4653651893908931727920261)
                    ·
                      refine ⟨872559730107924698985049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4653651893908931727920261 872559730107924698985049)
                      ·
                        rfl

theorem cell23_1699304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1699304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699304 prefixEnd_1699304 := by exact prefixLift 1699304
  have htrace : WordTrace (prefixWord ++ tailWord_1699304) baseStart_1699304 baseEnd_1699304 := by
    simpa [prefixWord, tailWord_1699304, baseEnd_1699304] using wordTrace_append hprefix tailTrace_1699304
  have hstable : (prefixWord ++ tailWord_1699304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699304).length < 2 ^ (prefixWord ++ tailWord_1699304).sum := by decide
  have hdescent : baseEnd_1699304 < baseStart_1699304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699332 : List Nat := [2, 3, 2, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_1699332 : Nat := 118140960795 + 1699332 * 2 ^ 59
def prefixEnd_1699332 : Nat := 4983230072969 + 3 ^ 40 * 1699332 * 2
def baseEnd_1699332 : Nat := 872574107566250589434921

theorem tailTrace_1699332 : CollatzResearch.WordTrace tailWord_1699332 prefixEnd_1699332 872574107566250589434921 := by
  unfold tailWord_1699332
  simp only [CollatzResearch.WordTrace]
  refine ⟨30989864939808930822446125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41319819919745241096594833 30989864939808930822446125)
  ·
    refine ⟨11621199352428349058417297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30989864939808930822446125 11621199352428349058417297)
    ·
      refine ⟨8715899514321261793812973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11621199352428349058417297 8715899514321261793812973)
      ·
        refine ⟨3268462317870473172679865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8715899514321261793812973 3268462317870473172679865)
        ·
          refine ⟨2451346738402854879509899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3268462317870473172679865 2451346738402854879509899)
          ·
            refine ⟨3677020107604282319264849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451346738402854879509899 3677020107604282319264849)
            ·
              refine ⟨2757765080703211739448637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3677020107604282319264849 2757765080703211739448637)
              ·
                refine ⟨1034161905263704402293239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2757765080703211739448637 1034161905263704402293239)
                ·
                  refine ⟨1551242857895556603439859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034161905263704402293239 1551242857895556603439859)
                  ·
                    refine ⟨2326864286843334905159789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1551242857895556603439859 2326864286843334905159789)
                    ·
                      refine ⟨872574107566250589434921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2326864286843334905159789 872574107566250589434921)
                      ·
                        rfl

theorem cell23_1699332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_1699332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699332 prefixEnd_1699332 := by exact prefixLift 1699332
  have htrace : WordTrace (prefixWord ++ tailWord_1699332) baseStart_1699332 baseEnd_1699332 := by
    simpa [prefixWord, tailWord_1699332, baseEnd_1699332] using wordTrace_append hprefix tailTrace_1699332
  have hstable : (prefixWord ++ tailWord_1699332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699332).length < 2 ^ (prefixWord ++ tailWord_1699332).sum := by decide
  have hdescent : baseEnd_1699332 < baseStart_1699332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699338 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4]
def baseStart_1699338 : Nat := 118140960795 + 1699338 * 2 ^ 59
def prefixEnd_1699338 : Nat := 4983230072969 + 3 ^ 40 * 1699338 * 2
def baseEnd_1699338 : Nat := 872577188450177565959893

theorem tailTrace_1699338 : CollatzResearch.WordTrace tailWord_1699338 prefixEnd_1699338 872577188450177565959893 := by
  unfold tailWord_1699338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15494987179399031167402667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41319965811730749779740445 15494987179399031167402667)
  ·
    refine ⟨23242480769098546751104001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15494987179399031167402667 23242480769098546751104001)
    ·
      refine ⟨17431860576823910063328001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23242480769098546751104001 17431860576823910063328001)
      ·
        refine ⟨13073895432617932547496001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17431860576823910063328001 13073895432617932547496001)
        ·
          refine ⟨9805421574463449410622001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13073895432617932547496001 9805421574463449410622001)
          ·
            refine ⟨7354066180847587057966501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9805421574463449410622001 7354066180847587057966501)
            ·
              refine ⟨1378887408908922573368719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7354066180847587057966501 1378887408908922573368719)
              ·
                refine ⟨2068331113363383860053079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378887408908922573368719 2068331113363383860053079)
                ·
                  refine ⟨3102496670045075790079619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068331113363383860053079 3102496670045075790079619)
                  ·
                    refine ⟨4653745005067613685119429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3102496670045075790079619 4653745005067613685119429)
                    ·
                      refine ⟨872577188450177565959893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4653745005067613685119429 872577188450177565959893)
                      ·
                        rfl

theorem cell23_1699338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_1699338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699338 prefixEnd_1699338 := by exact prefixLift 1699338
  have htrace : WordTrace (prefixWord ++ tailWord_1699338) baseStart_1699338 baseEnd_1699338 := by
    simpa [prefixWord, tailWord_1699338, baseEnd_1699338] using wordTrace_append hprefix tailTrace_1699338
  have hstable : (prefixWord ++ tailWord_1699338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699338).length < 2 ^ (prefixWord ++ tailWord_1699338).sum := by decide
  have hdescent : baseEnd_1699338 < baseStart_1699338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699384 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_1699384 : Nat := 118140960795 + 1699384 * 2 ^ 59
def prefixEnd_1699384 : Nat := 4983230072969 + 3 ^ 40 * 1699384 * 2
def baseEnd_1699384 : Nat := 872600808560284385984681

theorem tailTrace_1699384 : CollatzResearch.WordTrace tailWord_1699384 prefixEnd_1699384 872600808560284385984681 := by
  unfold tailWord_1699384
  simp only [CollatzResearch.WordTrace]
  refine ⟨30990813237714737262892603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41321084316952983017190137 30990813237714737262892603)
  ·
    refine ⟨46486219856572105894338905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30990813237714737262892603 46486219856572105894338905)
    ·
      refine ⟨34864664892429079420754179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46486219856572105894338905 34864664892429079420754179)
      ·
        refine ⟨52296997338643619131131269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34864664892429079420754179 52296997338643619131131269)
        ·
          refine ⟨9805687000995678587087113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52296997338643619131131269 9805687000995678587087113)
          ·
            refine ⟨7354265250746758940315335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9805687000995678587087113 7354265250746758940315335)
            ·
              refine ⟨11031397876120138410473003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354265250746758940315335 11031397876120138410473003)
              ·
                refine ⟨16547096814180207615709505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031397876120138410473003 16547096814180207615709505)
                ·
                  refine ⟨12410322610635155711782129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16547096814180207615709505 12410322610635155711782129)
                  ·
                    refine ⟨9307741957976366783836597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12410322610635155711782129 9307741957976366783836597)
                    ·
                      refine ⟨872600808560284385984681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9307741957976366783836597 872600808560284385984681)
                      ·
                        rfl

theorem cell23_1699384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_1699384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699384 prefixEnd_1699384 := by exact prefixLift 1699384
  have htrace : WordTrace (prefixWord ++ tailWord_1699384) baseStart_1699384 baseEnd_1699384 := by
    simpa [prefixWord, tailWord_1699384, baseEnd_1699384] using wordTrace_append hprefix tailTrace_1699384
  have hstable : (prefixWord ++ tailWord_1699384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699384).length < 2 ^ (prefixWord ++ tailWord_1699384).sum := by decide
  have hdescent : baseEnd_1699384 < baseStart_1699384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699389 : List Nat := [1, 4, 1, 3, 3, 2, 1, 3, 1, 2, 2]
def baseStart_1699389 : Nat := 118140960795 + 1699389 * 2 ^ 59
def prefixEnd_1699389 : Nat := 4983230072969 + 3 ^ 40 * 1699389 * 2
def baseEnd_1699389 : Nat := 872603375963556866422159

theorem tailTrace_1699389 : CollatzResearch.WordTrace tailWord_1699389 prefixEnd_1699389 872603375963556866422159 := by
  unfold tailWord_1699389
  simp only [CollatzResearch.WordTrace]
  refine ⟨61981808840411360379717221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41321205893607573586478147 61981808840411360379717221)
  ·
    refine ⟨11621589157577130071196979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61981808840411360379717221 11621589157577130071196979)
    ·
      refine ⟨17432383736365695106795469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11621589157577130071196979 17432383736365695106795469)
      ·
        refine ⟨6537143901137135665048301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17432383736365695106795469 6537143901137135665048301)
        ·
          refine ⟨2451428962926425874393113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6537143901137135665048301 2451428962926425874393113)
          ·
            refine ⟨1838571722194819405794835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2451428962926425874393113 1838571722194819405794835)
            ·
              refine ⟨2757857583292229108692253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838571722194819405794835 2757857583292229108692253)
              ·
                refine ⟨1034196593734585915759595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2757857583292229108692253 1034196593734585915759595)
                ·
                  refine ⟨1551294890601878873639393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034196593734585915759595 1551294890601878873639393)
                  ·
                    refine ⟨1163471167951409155229545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1551294890601878873639393 1163471167951409155229545)
                    ·
                      refine ⟨872603375963556866422159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163471167951409155229545 872603375963556866422159)
                      ·
                        rfl

theorem cell23_1699389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_1699389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699389 prefixEnd_1699389 := by exact prefixLift 1699389
  have htrace : WordTrace (prefixWord ++ tailWord_1699389) baseStart_1699389 baseEnd_1699389 := by
    simpa [prefixWord, tailWord_1699389, baseEnd_1699389] using wordTrace_append hprefix tailTrace_1699389
  have hstable : (prefixWord ++ tailWord_1699389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699389).length < 2 ^ (prefixWord ++ tailWord_1699389).sum := by decide
  have hdescent : baseEnd_1699389 < baseStart_1699389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699424 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_1699424 : Nat := 118140960795 + 1699424 * 2 ^ 59
def prefixEnd_1699424 : Nat := 4983230072969 + 3 ^ 40 * 1699424 * 2
def baseEnd_1699424 : Nat := 872621347786464229484497

theorem tailTrace_1699424 : CollatzResearch.WordTrace tailWord_1699424 prefixEnd_1699424 872621347786464229484497 := by
  unfold tailWord_1699424
  simp only [CollatzResearch.WordTrace]
  refine ⟨30991542697642280678620663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41322056930189707571494217 30991542697642280678620663)
  ·
    refine ⟨46487314046463421017930995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30991542697642280678620663 46487314046463421017930995)
    ·
      refine ⟨69730971069695131526896493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46487314046463421017930995 69730971069695131526896493)
      ·
        refine ⟨26149114151135674322586185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69730971069695131526896493 26149114151135674322586185)
        ·
          refine ⟨19611835613351755741939639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26149114151135674322586185 19611835613351755741939639)
          ·
            refine ⟨29417753420027633612909459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19611835613351755741939639 29417753420027633612909459)
            ·
              refine ⟨44126630130041450419364189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29417753420027633612909459 44126630130041450419364189)
              ·
                refine ⟨16547486298765543907261571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44126630130041450419364189 16547486298765543907261571)
                ·
                  refine ⟨24821229448148315860892357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16547486298765543907261571 24821229448148315860892357)
                  ·
                    refine ⟨4653980521527809223917317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24821229448148315860892357 4653980521527809223917317)
                    ·
                      refine ⟨872621347786464229484497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4653980521527809223917317 872621347786464229484497)
                      ·
                        rfl

theorem cell23_1699424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1699424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699424 prefixEnd_1699424 := by exact prefixLift 1699424
  have htrace : WordTrace (prefixWord ++ tailWord_1699424) baseStart_1699424 baseEnd_1699424 := by
    simpa [prefixWord, tailWord_1699424, baseEnd_1699424] using wordTrace_append hprefix tailTrace_1699424
  have hstable : (prefixWord ++ tailWord_1699424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699424).length < 2 ^ (prefixWord ++ tailWord_1699424).sum := by decide
  have hdescent : baseEnd_1699424 < baseStart_1699424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699432 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1699432 : Nat := 118140960795 + 1699432 * 2 ^ 59
def prefixEnd_1699432 : Nat := 4983230072969 + 3 ^ 40 * 1699432 * 2
def baseEnd_1699432 : Nat := 872625455631700198184461

theorem tailTrace_1699432 : CollatzResearch.WordTrace tailWord_1699432 prefixEnd_1699432 872625455631700198184461 := by
  unfold tailWord_1699432
  simp only [CollatzResearch.WordTrace]
  refine ⟨30991688589627789361766275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41322251452837052482355033 30991688589627789361766275)
  ·
    refine ⟨46487532884441684042649413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30991688589627789361766275 46487532884441684042649413)
    ·
      refine ⟨8716412415832815757996765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46487532884441684042649413 8716412415832815757996765)
      ·
        refine ⟨3268654655937305909248787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8716412415832815757996765 3268654655937305909248787)
        ·
          refine ⟨4902981983905958863873181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268654655937305909248787 4902981983905958863873181)
          ·
            refine ⟨1838618243964734573952443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4902981983905958863873181 1838618243964734573952443)
            ·
              refine ⟨2757927365947101860928665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838618243964734573952443 2757927365947101860928665)
              ·
                refine ⟨2068445524460326395696499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2757927365947101860928665 2068445524460326395696499)
                ·
                  refine ⟨3102668286690489593544749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068445524460326395696499 3102668286690489593544749)
                  ·
                    refine ⟨1163500607508933597579281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3102668286690489593544749 1163500607508933597579281)
                    ·
                      refine ⟨872625455631700198184461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163500607508933597579281 872625455631700198184461)
                      ·
                        rfl

theorem cell23_1699432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1699432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699432 prefixEnd_1699432 := by exact prefixLift 1699432
  have htrace : WordTrace (prefixWord ++ tailWord_1699432) baseStart_1699432 baseEnd_1699432 := by
    simpa [prefixWord, tailWord_1699432, baseEnd_1699432] using wordTrace_append hprefix tailTrace_1699432
  have hstable : (prefixWord ++ tailWord_1699432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699432).length < 2 ^ (prefixWord ++ tailWord_1699432).sum := by decide
  have hdescent : baseEnd_1699432 < baseStart_1699432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699445 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1699445 : Nat := 118140960795 + 1699445 * 2 ^ 59
def prefixEnd_1699445 : Nat := 4983230072969 + 3 ^ 40 * 1699445 * 2
def baseEnd_1699445 : Nat := 872632130880208647321901

theorem tailTrace_1699445 : CollatzResearch.WordTrace tailWord_1699445 prefixEnd_1699445 872632130880208647321901 := by
  unfold tailWord_1699445
  simp only [CollatzResearch.WordTrace]
  refine ⟨61983851328208481943755789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41322567552138987962503859 61983851328208481943755789)
  ·
    refine ⟨23243944248078180728908421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61983851328208481943755789 23243944248078180728908421)
    ·
      refine ⟨4358239546514658886670329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23243944248078180728908421 4358239546514658886670329)
      ·
        refine ⟨3268679659885994165002747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4358239546514658886670329 3268679659885994165002747)
        ·
          refine ⟨4903019489828991247504121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268679659885994165002747 4903019489828991247504121)
          ·
            refine ⟨3677264617371743435628091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4903019489828991247504121 3677264617371743435628091)
            ·
              refine ⟨5515896926057615153442137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677264617371743435628091 5515896926057615153442137)
              ·
                refine ⟨4136922694543211365081603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5515896926057615153442137 4136922694543211365081603)
                ·
                  refine ⟨6205384041814817047622405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4136922694543211365081603 6205384041814817047622405)
                  ·
                    refine ⟨1163509507840278196429201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6205384041814817047622405 1163509507840278196429201)
                    ·
                      refine ⟨872632130880208647321901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163509507840278196429201 872632130880208647321901)
                      ·
                        rfl

theorem cell23_1699445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1699445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699445 prefixEnd_1699445 := by exact prefixLift 1699445
  have htrace : WordTrace (prefixWord ++ tailWord_1699445) baseStart_1699445 baseEnd_1699445 := by
    simpa [prefixWord, tailWord_1699445, baseEnd_1699445] using wordTrace_append hprefix tailTrace_1699445
  have hstable : (prefixWord ++ tailWord_1699445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699445).length < 2 ^ (prefixWord ++ tailWord_1699445).sum := by decide
  have hdescent : baseEnd_1699445 < baseStart_1699445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699451 : List Nat := [1, 1, 1, 1, 1, 4, 4, 5, 5]
def baseStart_1699451 : Nat := 118140960795 + 1699451 * 2 ^ 59
def prefixEnd_1699451 : Nat := 4983230072969 + 3 ^ 40 * 1699451 * 2
def baseEnd_1699451 : Nat := 96959467973792847094097

theorem tailTrace_1699451 : CollatzResearch.WordTrace tailWord_1699451 prefixEnd_1699451 96959467973792847094097 := by
  unfold tailWord_1699451
  simp only [CollatzResearch.WordTrace]
  refine ⟨61984070166186744968474207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41322713444124496645649471 61984070166186744968474207)
  ·
    refine ⟨92976105249280117452711311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61984070166186744968474207 92976105249280117452711311)
    ·
      refine ⟨139464157873920176179066967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92976105249280117452711311 139464157873920176179066967)
      ·
        refine ⟨209196236810880264268600451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139464157873920176179066967 209196236810880264268600451)
        ·
          refine ⟨313794355216320396402900677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209196236810880264268600451 313794355216320396402900677)
          ·
            refine ⟨58836441603060074325543877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313794355216320396402900677 58836441603060074325543877)
            ·
              refine ⟨11031832800573763936039477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58836441603060074325543877 11031832800573763936039477)
              ·
                refine ⟨1034234325053790369003701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11031832800573763936039477 1034234325053790369003701)
                ·
                  refine ⟨96959467973792847094097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1034234325053790369003701 96959467973792847094097)
                  ·
                    rfl

theorem cell23_1699451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 5].length) (baseStart_1699451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699451 prefixEnd_1699451 := by exact prefixLift 1699451
  have htrace : WordTrace (prefixWord ++ tailWord_1699451) baseStart_1699451 baseEnd_1699451 := by
    simpa [prefixWord, tailWord_1699451, baseEnd_1699451] using wordTrace_append hprefix tailTrace_1699451
  have hstable : (prefixWord ++ tailWord_1699451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699451).length < 2 ^ (prefixWord ++ tailWord_1699451).sum := by decide
  have hdescent : baseEnd_1699451 < baseStart_1699451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699461 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 2, 3, 3]
def baseStart_1699461 : Nat := 118140960795 + 1699461 * 2 ^ 59
def prefixEnd_1699461 : Nat := 4983230072969 + 3 ^ 40 * 1699461 * 2
def baseEnd_1699461 : Nat := 872640346570680584721827

theorem tailTrace_1699461 : CollatzResearch.WordTrace tailWord_1699461 prefixEnd_1699461 872640346570680584721827 := by
  unfold tailWord_1699461
  simp only [CollatzResearch.WordTrace]
  refine ⟨61984434896150516676338237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41322956597433677784225491 61984434896150516676338237)
  ·
    refine ⟨23244163086056443753626839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61984434896150516676338237 23244163086056443753626839)
    ·
      refine ⟨34866244629084665630440259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23244163086056443753626839 34866244629084665630440259)
      ·
        refine ⟨52299366943626998445660389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34866244629084665630440259 52299366943626998445660389)
        ·
          refine ⟨9806131301930062208561323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52299366943626998445660389 9806131301930062208561323)
          ·
            refine ⟨14709196952895093312841985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806131301930062208561323 14709196952895093312841985)
            ·
              refine ⟨11031897714671319984631489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14709196952895093312841985 11031897714671319984631489)
              ·
                refine ⟨8273923286003489988473617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11031897714671319984631489 8273923286003489988473617)
                ·
                  refine ⟨6205442464502617491355213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8273923286003489988473617 6205442464502617491355213)
                  ·
                    refine ⟨2327040924188481559258205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6205442464502617491355213 2327040924188481559258205)
                    ·
                      refine ⟨872640346570680584721827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2327040924188481559258205 872640346570680584721827)
                      ·
                        rfl

theorem cell23_1699461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_1699461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699461 prefixEnd_1699461 := by exact prefixLift 1699461
  have htrace : WordTrace (prefixWord ++ tailWord_1699461) baseStart_1699461 baseEnd_1699461 := by
    simpa [prefixWord, tailWord_1699461, baseEnd_1699461] using wordTrace_append hprefix tailTrace_1699461
  have hstable : (prefixWord ++ tailWord_1699461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699461).length < 2 ^ (prefixWord ++ tailWord_1699461).sum := by decide
  have hdescent : baseEnd_1699461 < baseStart_1699461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699502 : List Nat := [4, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_1699502 : Nat := 118140960795 + 1699502 * 2 ^ 59
def prefixEnd_1699502 : Nat := 4983230072969 + 3 ^ 40 * 1699502 * 2
def baseEnd_1699502 : Nat := 96962377697501658256571

theorem tailTrace_1699502 : CollatzResearch.WordTrace tailWord_1699502 prefixEnd_1699502 96962377697501658256571 := by
  unfold tailWord_1699502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748241286125247584822595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41323953526001320452387173 7748241286125247584822595)
  ·
    refine ⟨11622361929187871377233893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7748241286125247584822595 11622361929187871377233893)
    ·
      refine ⟨2179192861722725883231355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11622361929187871377233893 2179192861722725883231355)
      ·
        refine ⟨3268789292584088824847033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2179192861722725883231355 3268789292584088824847033)
        ·
          refine ⟨2451591969438066618635275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3268789292584088824847033 2451591969438066618635275)
          ·
            refine ⟨3677387954157099927952913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451591969438066618635275 3677387954157099927952913)
            ·
              refine ⟨2758040965617824945964685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3677387954157099927952913 2758040965617824945964685)
              ·
                refine ⟨1034265362106684354736757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2758040965617824945964685 1034265362106684354736757)
                ·
                  refine ⟨96962377697501658256571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1034265362106684354736757 96962377697501658256571)
                  ·
                    rfl

theorem cell23_1699502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_1699502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699502 prefixEnd_1699502 := by exact prefixLift 1699502
  have htrace : WordTrace (prefixWord ++ tailWord_1699502) baseStart_1699502 baseEnd_1699502 := by
    simpa [prefixWord, tailWord_1699502, baseEnd_1699502] using wordTrace_append hprefix tailTrace_1699502
  have hstable : (prefixWord ++ tailWord_1699502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699502).length < 2 ^ (prefixWord ++ tailWord_1699502).sum := by decide
  have hdescent : baseEnd_1699502 < baseStart_1699502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699528 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 3, 4]
def baseStart_1699528 : Nat := 118140960795 + 1699528 * 2 ^ 59
def prefixEnd_1699528 : Nat := 4983230072969 + 3 ^ 40 * 1699528 * 2
def baseEnd_1699528 : Nat := 290891583258177274194673

theorem tailTrace_1699528 : CollatzResearch.WordTrace tailWord_1699528 prefixEnd_1699528 290891583258177274194673 := by
  unfold tailWord_1699528
  simp only [CollatzResearch.WordTrace]
  refine ⟨30993439293453893559513619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41324585724605191412684825 30993439293453893559513619)
  ·
    refine ⟨46490158940180840339270429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30993439293453893559513619 46490158940180840339270429)
    ·
      refine ⟨17433809602567815127226411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46490158940180840339270429 17433809602567815127226411)
      ·
        refine ⟨26150714403851722690839617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17433809602567815127226411 26150714403851722690839617)
        ·
          refine ⟨19613035802888792018129713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26150714403851722690839617 19613035802888792018129713)
          ·
            refine ⟨14709776852166594013597285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19613035802888792018129713 14709776852166594013597285)
            ·
              refine ⟨2758083159781236377549491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14709776852166594013597285 2758083159781236377549491)
              ·
                refine ⟨4137124739671854566324237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758083159781236377549491 4137124739671854566324237)
                ·
                  refine ⟨1551421777376945462371589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4137124739671854566324237 1551421777376945462371589)
                  ·
                    refine ⟨290891583258177274194673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1551421777376945462371589 290891583258177274194673)
                    ·
                      rfl

theorem cell23_1699528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_1699528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699528 prefixEnd_1699528 := by exact prefixLift 1699528
  have htrace : WordTrace (prefixWord ++ tailWord_1699528) baseStart_1699528 baseEnd_1699528 := by
    simpa [prefixWord, tailWord_1699528, baseEnd_1699528] using wordTrace_append hprefix tailTrace_1699528
  have hstable : (prefixWord ++ tailWord_1699528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699528).length < 2 ^ (prefixWord ++ tailWord_1699528).sum := by decide
  have hdescent : baseEnd_1699528 < baseStart_1699528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699538 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_1699538 : Nat := 118140960795 + 1699538 * 2 ^ 59
def prefixEnd_1699538 : Nat := 4983230072969 + 3 ^ 40 * 1699538 * 2
def baseEnd_1699538 : Nat := 872679884581076783458973

theorem tailTrace_1699538 : CollatzResearch.WordTrace tailWord_1699538 prefixEnd_1699538 872679884581076783458973 := by
  unfold tailWord_1699538
  simp only [CollatzResearch.WordTrace]
  refine ⟨15496810829217889706722817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41324828877914372551260845 15496810829217889706722817)
  ·
    refine ⟨11622608121913417280042113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15496810829217889706722817 11622608121913417280042113)
    ·
      refine ⟨8716956091435062960031585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11622608121913417280042113 8716956091435062960031585)
      ·
        refine ⟨6537717068576297220023689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8716956091435062960031585 6537717068576297220023689)
        ·
          refine ⟨4903287801432222915017767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6537717068576297220023689 4903287801432222915017767)
          ·
            refine ⟨7354931702148334372526651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903287801432222915017767 7354931702148334372526651)
            ·
              refine ⟨11032397553222501558789977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354931702148334372526651 11032397553222501558789977)
              ·
                refine ⟨8274298164916876169092483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11032397553222501558789977 8274298164916876169092483)
                ·
                  refine ⟨12411447247375314253638725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8274298164916876169092483 12411447247375314253638725)
                  ·
                    refine ⟨2327146358882871422557261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12411447247375314253638725 2327146358882871422557261)
                    ·
                      refine ⟨872679884581076783458973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2327146358882871422557261 872679884581076783458973)
                      ·
                        rfl

theorem cell23_1699538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_1699538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699538 prefixEnd_1699538 := by exact prefixLift 1699538
  have htrace : WordTrace (prefixWord ++ tailWord_1699538) baseStart_1699538 baseEnd_1699538 := by
    simpa [prefixWord, tailWord_1699538, baseEnd_1699538] using wordTrace_append hprefix tailTrace_1699538
  have hstable : (prefixWord ++ tailWord_1699538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699538).length < 2 ^ (prefixWord ++ tailWord_1699538).sum := by decide
  have hdescent : baseEnd_1699538 < baseStart_1699538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699551 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 3]
def baseStart_1699551 : Nat := 118140960795 + 1699551 * 2 ^ 59
def prefixEnd_1699551 : Nat := 4983230072969 + 3 ^ 40 * 1699551 * 2
def baseEnd_1699551 : Nat := 872686559829585232596413

theorem tailTrace_1699551 : CollatzResearch.WordTrace tailWord_1699551 prefixEnd_1699551 872686559829585232596413 := by
  unfold tailWord_1699551
  simp only [CollatzResearch.WordTrace]
  refine ⟨61987717465824462047114507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41325144977216308031409671 61987717465824462047114507)
  ·
    refine ⟨92981576198736693070671761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61987717465824462047114507 92981576198736693070671761)
    ·
      refine ⟨69736182149052519803003821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92981576198736693070671761 69736182149052519803003821)
      ·
        refine ⟨26151068305894694926126433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69736182149052519803003821 26151068305894694926126433)
        ·
          refine ⟨19613301229421021194594825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26151068305894694926126433 19613301229421021194594825)
          ·
            refine ⟨14709975922065765895946119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19613301229421021194594825 14709975922065765895946119)
            ·
              refine ⟨22064963883098648843919179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14709975922065765895946119 22064963883098648843919179)
              ·
                refine ⟨33097445824647973265878769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22064963883098648843919179 33097445824647973265878769)
                ·
                  refine ⟨24823084368485979949409077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33097445824647973265878769 24823084368485979949409077)
                  ·
                    refine ⟨2327164159545560620257101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24823084368485979949409077 2327164159545560620257101)
                    ·
                      refine ⟨872686559829585232596413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2327164159545560620257101 872686559829585232596413)
                      ·
                        rfl

theorem cell23_1699551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_1699551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699551 prefixEnd_1699551 := by exact prefixLift 1699551
  have htrace : WordTrace (prefixWord ++ tailWord_1699551) baseStart_1699551 baseEnd_1699551 := by
    simpa [prefixWord, tailWord_1699551, baseEnd_1699551] using wordTrace_append hprefix tailTrace_1699551
  have hstable : (prefixWord ++ tailWord_1699551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699551).length < 2 ^ (prefixWord ++ tailWord_1699551).sum := by decide
  have hdescent : baseEnd_1699551 < baseStart_1699551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699572 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1699572 : Nat := 118140960795 + 1699572 * 2 ^ 59
def prefixEnd_1699572 : Nat := 4983230072969 + 3 ^ 40 * 1699572 * 2
def baseEnd_1699572 : Nat := 872697342923329650433817

theorem tailTrace_1699572 : CollatzResearch.WordTrace tailWord_1699572 prefixEnd_1699572 872697342923329650433817 := by
  unfold tailWord_1699572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30994241699374191316814485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41325655599165588422419313 30994241699374191316814485)
  ·
    refine ⟨1452855079658165217975679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30994241699374191316814485 1452855079658165217975679)
    ·
      refine ⟨2179282619487247826963519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452855079658165217975679 2179282619487247826963519)
      ·
        refine ⟨3268923929230871740445279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2179282619487247826963519 3268923929230871740445279)
        ·
          refine ⟨4903385893846307610667919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268923929230871740445279 4903385893846307610667919)
          ·
            refine ⟨7355078840769461416001879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903385893846307610667919 7355078840769461416001879)
            ·
              refine ⟨11032618261154192124002819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7355078840769461416001879 11032618261154192124002819)
              ·
                refine ⟨16548927391731288186004229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11032618261154192124002819 16548927391731288186004229)
                ·
                  refine ⟨3102923885949616534875793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16548927391731288186004229 3102923885949616534875793)
                  ·
                    refine ⟨2327192914462212401156845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3102923885949616534875793 2327192914462212401156845)
                    ·
                      refine ⟨872697342923329650433817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2327192914462212401156845 872697342923329650433817)
                      ·
                        rfl

theorem cell23_1699572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1699572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699572 prefixEnd_1699572 := by exact prefixLift 1699572
  have htrace : WordTrace (prefixWord ++ tailWord_1699572) baseStart_1699572 baseEnd_1699572 := by
    simpa [prefixWord, tailWord_1699572, baseEnd_1699572] using wordTrace_append hprefix tailTrace_1699572
  have hstable : (prefixWord ++ tailWord_1699572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699572).length < 2 ^ (prefixWord ++ tailWord_1699572).sum := by decide
  have hdescent : baseEnd_1699572 < baseStart_1699572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699585 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_1699585 : Nat := 118140960795 + 1699585 * 2 ^ 59
def prefixEnd_1699585 : Nat := 4983230072969 + 3 ^ 40 * 1699585 * 2
def baseEnd_1699585 : Nat := 872704018171838099571257

theorem tailTrace_1699585 : CollatzResearch.WordTrace tailWord_1699585 prefixEnd_1699585 872704018171838099571257 := by
  unfold tailWord_1699585
  simp only [CollatzResearch.WordTrace]
  refine ⟨61988957547701285853852209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41325971698467523902568139 61988957547701285853852209)
  ·
    refine ⟨46491718160775964390389157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61988957547701285853852209 46491718160775964390389157)
    ·
      refine ⟨8717197155145493323197967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46491718160775964390389157 8717197155145493323197967)
      ·
        refine ⟨13075795732718239984796951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8717197155145493323197967 13075795732718239984796951)
        ·
          refine ⟨19613693599077359977195427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13075795732718239984796951 19613693599077359977195427)
          ·
            refine ⟨29420540398616039965793141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19613693599077359977195427 29420540398616039965793141)
            ·
              refine ⟨2758175662370253746793107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29420540398616039965793141 2758175662370253746793107)
              ·
                refine ⟨4137263493555380620189661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758175662370253746793107 4137263493555380620189661)
                ·
                  refine ⟨1551473810083267732571123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4137263493555380620189661 1551473810083267732571123)
                  ·
                    refine ⟨2327210715124901598856685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1551473810083267732571123 2327210715124901598856685)
                    ·
                      refine ⟨872704018171838099571257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2327210715124901598856685 872704018171838099571257)
                      ·
                        rfl

theorem cell23_1699585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_1699585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699585 prefixEnd_1699585 := by exact prefixLift 1699585
  have htrace : WordTrace (prefixWord ++ tailWord_1699585) baseStart_1699585 baseEnd_1699585 := by
    simpa [prefixWord, tailWord_1699585, baseEnd_1699585] using wordTrace_append hprefix tailTrace_1699585
  have hstable : (prefixWord ++ tailWord_1699585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699585).length < 2 ^ (prefixWord ++ tailWord_1699585).sum := by decide
  have hdescent : baseEnd_1699585 < baseStart_1699585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699601 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 1, 6]
def baseStart_1699601 : Nat := 118140960795 + 1699601 * 2 ^ 59
def prefixEnd_1699601 : Nat := 4983230072969 + 3 ^ 40 * 1699601 * 2
def baseEnd_1699601 : Nat := 290904077954103345657061

theorem tailTrace_1699601 : CollatzResearch.WordTrace tailWord_1699601 prefixEnd_1699601 290904077954103345657061 := by
  unfold tailWord_1699601
  simp only [CollatzResearch.WordTrace]
  refine ⟨61989541115643320586434657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41326360743762213724289771 61989541115643320586434657)
  ·
    refine ⟨46492155836732490439825993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61989541115643320586434657 46492155836732490439825993)
    ·
      refine ⟨34869116877549367829869495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46492155836732490439825993 34869116877549367829869495)
      ·
        refine ⟨52303675316324051744804243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34869116877549367829869495 52303675316324051744804243)
        ·
          refine ⟨78455512974486077617206365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52303675316324051744804243 78455512974486077617206365)
          ·
            refine ⟨29420817365432279106452387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78455512974486077617206365 29420817365432279106452387)
            ·
              refine ⟨44131226048148418659678581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29420817365432279106452387 44131226048148418659678581)
              ·
                refine ⟨4137302442013914249344867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44131226048148418659678581 4137302442013914249344867)
                ·
                  refine ⟨6205953663020871374017301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137302442013914249344867 6205953663020871374017301)
                  ·
                    refine ⟨290904077954103345657061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6205953663020871374017301 290904077954103345657061)
                    ·
                      rfl

theorem cell23_1699601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_1699601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699601 prefixEnd_1699601 := by exact prefixLift 1699601
  have htrace : WordTrace (prefixWord ++ tailWord_1699601) baseStart_1699601 baseEnd_1699601 := by
    simpa [prefixWord, tailWord_1699601, baseEnd_1699601] using wordTrace_append hprefix tailTrace_1699601
  have hstable : (prefixWord ++ tailWord_1699601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699601).length < 2 ^ (prefixWord ++ tailWord_1699601).sum := by decide
  have hdescent : baseEnd_1699601 < baseStart_1699601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699605 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_1699605 : Nat := 118140960795 + 1699605 * 2 ^ 59
def prefixEnd_1699605 : Nat := 4983230072969 + 3 ^ 40 * 1699605 * 2
def baseEnd_1699605 : Nat := 290904762594976007107055

theorem tailTrace_1699605 : CollatzResearch.WordTrace tailWord_1699605 prefixEnd_1699605 290904762594976007107055 := by
  unfold tailWord_1699605
  simp only [CollatzResearch.WordTrace]
  refine ⟨61989687007628829269580269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41326458005085886179720179 61989687007628829269580269)
  ·
    refine ⟨23246132627860810976092601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61989687007628829269580269 23246132627860810976092601)
    ·
      refine ⟨17434599470895608232069451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23246132627860810976092601 17434599470895608232069451)
      ·
        refine ⟨26151899206343412348104177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17434599470895608232069451 26151899206343412348104177)
        ·
          refine ⟨19613924404757559261078133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26151899206343412348104177 19613924404757559261078133)
          ·
            refine ⟨1838805412946021180726075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19613924404757559261078133 1838805412946021180726075)
            ·
              refine ⟨2758208119419031771089113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838805412946021180726075 2758208119419031771089113)
              ·
                refine ⟨2068656089564273828316835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758208119419031771089113 2068656089564273828316835)
                ·
                  refine ⟨3102984134346410742475253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068656089564273828316835 3102984134346410742475253)
                  ·
                    refine ⟨290904762594976007107055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3102984134346410742475253 290904762594976007107055)
                    ·
                      rfl

theorem cell23_1699605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_1699605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699605 prefixEnd_1699605 := by exact prefixLift 1699605
  have htrace : WordTrace (prefixWord ++ tailWord_1699605) baseStart_1699605 baseEnd_1699605 := by
    simpa [prefixWord, tailWord_1699605, baseEnd_1699605] using wordTrace_append hprefix tailTrace_1699605
  have hstable : (prefixWord ++ tailWord_1699605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699605).length < 2 ^ (prefixWord ++ tailWord_1699605).sum := by decide
  have hdescent : baseEnd_1699605 < baseStart_1699605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699608 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 2, 6, 2]
def baseStart_1699608 : Nat := 118140960795 + 1699608 * 2 ^ 59
def prefixEnd_1699608 : Nat := 4983230072969 + 3 ^ 40 * 1699608 * 2
def baseEnd_1699608 : Nat := 872715828226891509583651

theorem tailTrace_1699608 : CollatzResearch.WordTrace tailWord_1699608 prefixEnd_1699608 872715828226891509583651 := by
  unfold tailWord_1699608
  simp only [CollatzResearch.WordTrace]
  refine ⟨30994898213308980390969739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41326530951078640521292985 30994898213308980390969739)
  ·
    refine ⟨46492347319963470586454609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30994898213308980390969739 46492347319963470586454609)
    ·
      refine ⟨34869260489972602939840957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46492347319963470586454609 34869260489972602939840957)
      ·
        refine ⟨13075972683739726102440359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34869260489972602939840957 13075972683739726102440359)
        ·
          refine ⟨19613959025609589153660539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13075972683739726102440359 19613959025609589153660539)
          ·
            refine ⟨29420938538414383730490809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19613959025609589153660539 29420938538414383730490809)
            ·
              refine ⟨22065703903810787797868107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29420938538414383730490809 22065703903810787797868107)
              ·
                refine ⟨33098555855716181696802161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22065703903810787797868107 33098555855716181696802161)
                ·
                  refine ⟨24823916891787136272601621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33098555855716181696802161 24823916891787136272601621)
                  ·
                    refine ⟨1163621104302522012778201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24823916891787136272601621 1163621104302522012778201)
                    ·
                      refine ⟨872715828226891509583651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163621104302522012778201 872715828226891509583651)
                      ·
                        rfl

theorem cell23_1699608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_1699608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699608 prefixEnd_1699608 := by exact prefixLift 1699608
  have htrace : WordTrace (prefixWord ++ tailWord_1699608) baseStart_1699608 baseEnd_1699608 := by
    simpa [prefixWord, tailWord_1699608, baseEnd_1699608] using wordTrace_append hprefix tailTrace_1699608
  have hstable : (prefixWord ++ tailWord_1699608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699608).length < 2 ^ (prefixWord ++ tailWord_1699608).sum := by decide
  have hdescent : baseEnd_1699608 < baseStart_1699608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699611 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 3]
def baseStart_1699611 : Nat := 118140960795 + 1699611 * 2 ^ 59
def prefixEnd_1699611 : Nat := 4983230072969 + 3 ^ 40 * 1699611 * 2
def baseEnd_1699611 : Nat := 872717368668854997846137

theorem tailTrace_1699611 : CollatzResearch.WordTrace tailWord_1699611 prefixEnd_1699611 872717368668854997846137 := by
  unfold tailWord_1699611
  simp only [CollatzResearch.WordTrace]
  refine ⟨61989905845607092294298687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41326603897071394862865791 61989905845607092294298687)
  ·
    refine ⟨92984858768410638441448031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61989905845607092294298687 92984858768410638441448031)
    ·
      refine ⟨139477288152615957662172047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92984858768410638441448031 139477288152615957662172047)
      ·
        refine ⟨209215932228923936493258071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139477288152615957662172047 209215932228923936493258071)
        ·
          refine ⟨313823898343385904739887107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209215932228923936493258071 313823898343385904739887107)
          ·
            refine ⟨470735847515078857109830661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313823898343385904739887107 470735847515078857109830661)
            ·
              refine ⟨88262971409077285708093249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 470735847515078857109830661 88262971409077285708093249)
              ·
                refine ⟨66197228556807964281069937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88262971409077285708093249 66197228556807964281069937)
                ·
                  refine ⟨49647921417605973210802453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66197228556807964281069937 49647921417605973210802453)
                  ·
                    refine ⟨2327246316450279994256365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49647921417605973210802453 2327246316450279994256365)
                    ·
                      refine ⟨872717368668854997846137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2327246316450279994256365 872717368668854997846137)
                      ·
                        rfl

theorem cell23_1699611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 3].length) (baseStart_1699611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699611 prefixEnd_1699611 := by exact prefixLift 1699611
  have htrace : WordTrace (prefixWord ++ tailWord_1699611) baseStart_1699611 baseEnd_1699611 := by
    simpa [prefixWord, tailWord_1699611, baseEnd_1699611] using wordTrace_append hprefix tailTrace_1699611
  have hstable : (prefixWord ++ tailWord_1699611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699611).length < 2 ^ (prefixWord ++ tailWord_1699611).sum := by decide
  have hdescent : baseEnd_1699611 < baseStart_1699611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699618 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_1699618 : Nat := 118140960795 + 1699618 * 2 ^ 59
def prefixEnd_1699618 : Nat := 4983230072969 + 3 ^ 40 * 1699618 * 2
def baseEnd_1699618 : Nat := 290906987677812156819535

theorem tailTrace_1699618 : CollatzResearch.WordTrace tailWord_1699618 prefixEnd_1699618 290906987677812156819535 := by
  unfold tailWord_1699618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15497540289145433122450877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41326774104387821659869005 15497540289145433122450877)
  ·
    refine ⟨5811577608429537420919079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15497540289145433122450877 5811577608429537420919079)
    ·
      refine ⟨8717366412644306131378619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5811577608429537420919079 8717366412644306131378619)
      ·
        refine ⟨13076049618966459197067929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8717366412644306131378619 13076049618966459197067929)
        ·
          refine ⟨9807037214224844397800947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13076049618966459197067929 9807037214224844397800947)
          ·
            refine ⟨14710555821337266596701421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9807037214224844397800947 14710555821337266596701421)
            ·
              refine ⟨5516458433001474973763033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14710555821337266596701421 5516458433001474973763033)
              ·
                refine ⟨4137343824751106230322275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5516458433001474973763033 4137343824751106230322275)
                ·
                  refine ⟨6206015737126659345483413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137343824751106230322275 6206015737126659345483413)
                  ·
                    refine ⟨290906987677812156819535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6206015737126659345483413 290906987677812156819535)
                    ·
                      rfl

theorem cell23_1699618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_1699618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699618 prefixEnd_1699618 := by exact prefixLift 1699618
  have htrace : WordTrace (prefixWord ++ tailWord_1699618) baseStart_1699618 baseEnd_1699618 := by
    simpa [prefixWord, tailWord_1699618, baseEnd_1699618] using wordTrace_append hprefix tailTrace_1699618
  have hstable : (prefixWord ++ tailWord_1699618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699618).length < 2 ^ (prefixWord ++ tailWord_1699618).sum := by decide
  have hdescent : baseEnd_1699618 < baseStart_1699618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699628 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 5]
def baseStart_1699628 : Nat := 118140960795 + 1699628 * 2 ^ 59
def prefixEnd_1699628 : Nat := 4983230072969 + 3 ^ 40 * 1699628 * 2
def baseEnd_1699628 : Nat := 872726097839981431333559

theorem tailTrace_1699628 : CollatzResearch.WordTrace tailWord_1699628 prefixEnd_1699628 872726097839981431333559 := by
  unfold tailWord_1699628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30995262943272752098833769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41327017257697002798445025 30995262943272752098833769)
  ·
    refine ⟨23246447207454564074125327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30995262943272752098833769 23246447207454564074125327)
    ·
      refine ⟨34869670811181846111187991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23246447207454564074125327 34869670811181846111187991)
      ·
        refine ⟨52304506216772769166781987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34869670811181846111187991 52304506216772769166781987)
        ·
          refine ⟨78456759325159153750172981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52304506216772769166781987 78456759325159153750172981)
          ·
            refine ⟨7355321186733670664078717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78456759325159153750172981 7355321186733670664078717)
            ·
              refine ⟨2758245445025126499029519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7355321186733670664078717 2758245445025126499029519)
              ·
                refine ⟨4137368167537689748544279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758245445025126499029519 4137368167537689748544279)
                ·
                  refine ⟨6206052251306534622816419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137368167537689748544279 6206052251306534622816419)
                  ·
                    refine ⟨9309078376959801934224629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6206052251306534622816419 9309078376959801934224629)
                    ·
                      refine ⟨872726097839981431333559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9309078376959801934224629 872726097839981431333559)
                      ·
                        rfl

theorem cell23_1699628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_1699628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699628 prefixEnd_1699628 := by exact prefixLift 1699628
  have htrace : WordTrace (prefixWord ++ tailWord_1699628) baseStart_1699628 baseEnd_1699628 := by
    simpa [prefixWord, tailWord_1699628, baseEnd_1699628] using wordTrace_append hprefix tailTrace_1699628
  have hstable : (prefixWord ++ tailWord_1699628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699628).length < 2 ^ (prefixWord ++ tailWord_1699628).sum := by decide
  have hdescent : baseEnd_1699628 < baseStart_1699628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699636 : List Nat := [2, 5, 1, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_1699636 : Nat := 118140960795 + 1699636 * 2 ^ 59
def prefixEnd_1699636 : Nat := 4983230072969 + 3 ^ 40 * 1699636 * 2
def baseEnd_1699636 : Nat := 872730205685217400033523

theorem tailTrace_1699636 : CollatzResearch.WordTrace tailWord_1699636 prefixEnd_1699636 872730205685217400033523 := by
  unfold tailWord_1699636
  simp only [CollatzResearch.WordTrace]
  refine ⟨30995408835258260781979381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41327211780344347709305841 30995408835258260781979381)
  ·
    refine ⟨2905819578305461948310567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30995408835258260781979381 2905819578305461948310567)
    ·
      refine ⟨4358729367458192922465851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2905819578305461948310567 4358729367458192922465851)
      ·
        refine ⟨6538094051187289383698777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4358729367458192922465851 6538094051187289383698777)
        ·
          refine ⟨4903570538390467037774083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6538094051187289383698777 4903570538390467037774083)
          ·
            refine ⟨7355355807585700556661125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903570538390467037774083 7355355807585700556661125)
            ·
              refine ⟨1379129213922318854373961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7355355807585700556661125 1379129213922318854373961)
              ·
                refine ⟨1034346910441739140780471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379129213922318854373961 1034346910441739140780471)
                ·
                  refine ⟨1551520365662608711170707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034346910441739140780471 1551520365662608711170707)
                  ·
                    refine ⟨2327280548493913066756061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1551520365662608711170707 2327280548493913066756061)
                    ·
                      refine ⟨872730205685217400033523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2327280548493913066756061 872730205685217400033523)
                      ·
                        rfl

theorem cell23_1699636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_1699636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699636 prefixEnd_1699636 := by exact prefixLift 1699636
  have htrace : WordTrace (prefixWord ++ tailWord_1699636) baseStart_1699636 baseEnd_1699636 := by
    simpa [prefixWord, tailWord_1699636, baseEnd_1699636] using wordTrace_append hprefix tailTrace_1699636
  have hstable : (prefixWord ++ tailWord_1699636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699636).length < 2 ^ (prefixWord ++ tailWord_1699636).sum := by decide
  have hdescent : baseEnd_1699636 < baseStart_1699636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699645 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1699645 : Nat := 118140960795 + 1699645 * 2 ^ 59
def prefixEnd_1699645 : Nat := 4983230072969 + 3 ^ 40 * 1699645 * 2
def baseEnd_1699645 : Nat := 872734827011107864820981

theorem tailTrace_1699645 : CollatzResearch.WordTrace tailWord_1699645 prefixEnd_1699645 872734827011107864820981 := by
  unfold tailWord_1699645
  simp only [CollatzResearch.WordTrace]
  refine ⟨61991145927483916101036389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41327430618322610734024259 61991145927483916101036389)
  ·
    refine ⟨11623339861403234268944323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61991145927483916101036389 11623339861403234268944323)
    ·
      refine ⟨17435009792104851403416485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11623339861403234268944323 17435009792104851403416485)
      ·
        refine ⟨3269064336019659638140591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17435009792104851403416485 3269064336019659638140591)
        ·
          refine ⟨4903596504029489457210887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3269064336019659638140591 4903596504029489457210887)
          ·
            refine ⟨7355394756044234185816331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903596504029489457210887 7355394756044234185816331)
            ·
              refine ⟨11033092134066351278724497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7355394756044234185816331 11033092134066351278724497)
              ·
                refine ⟨8274819100549763459043373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11033092134066351278724497 8274819100549763459043373)
                ·
                  refine ⟨3103057162706161297141265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8274819100549763459043373 3103057162706161297141265)
                  ·
                    refine ⟨2327292872029620972855949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3103057162706161297141265 2327292872029620972855949)
                    ·
                      refine ⟨872734827011107864820981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2327292872029620972855949 872734827011107864820981)
                      ·
                        rfl

theorem cell23_1699645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1699645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699645 prefixEnd_1699645 := by exact prefixLift 1699645
  have htrace : WordTrace (prefixWord ++ tailWord_1699645) baseStart_1699645 baseEnd_1699645 := by
    simpa [prefixWord, tailWord_1699645, baseEnd_1699645] using wordTrace_append hprefix tailTrace_1699645
  have hstable : (prefixWord ++ tailWord_1699645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699645).length < 2 ^ (prefixWord ++ tailWord_1699645).sum := by decide
  have hdescent : baseEnd_1699645 < baseStart_1699645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699676 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_1699676 : Nat := 118140960795 + 1699676 * 2 ^ 59
def prefixEnd_1699676 : Nat := 4983230072969 + 3 ^ 40 * 1699676 * 2
def baseEnd_1699676 : Nat := 872750744911397243533339

theorem tailTrace_1699676 : CollatzResearch.WordTrace tailWord_1699676 prefixEnd_1699676 872750744911397243533339 := by
  unfold tailWord_1699676
  simp only [CollatzResearch.WordTrace]
  refine ⟨30996138295185804197707441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41328184393581072263609921 30996138295185804197707441)
  ·
    refine ⟨23247103721389353148280581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30996138295185804197707441 23247103721389353148280581)
    ·
      refine ⟨4358831947760503715302609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23247103721389353148280581 4358831947760503715302609)
      ·
        refine ⟨3269123960820377786476957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4358831947760503715302609 3269123960820377786476957)
        ·
          refine ⟨1225921485307641669928859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3269123960820377786476957 1225921485307641669928859)
          ·
            refine ⟨1838882227961462504893289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225921485307641669928859 1838882227961462504893289)
            ·
              refine ⟨1379161670971096878669967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838882227961462504893289 1379161670971096878669967)
              ·
                refine ⟨2068742506456645318004951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379161670971096878669967 2068742506456645318004951)
                ·
                  refine ⟨3103113759684967977007427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068742506456645318004951 3103113759684967977007427)
                  ·
                    refine ⟨4654670639527451965511141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3103113759684967977007427 4654670639527451965511141)
                    ·
                      refine ⟨872750744911397243533339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4654670639527451965511141 872750744911397243533339)
                      ·
                        rfl

theorem cell23_1699676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_1699676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699676 prefixEnd_1699676 := by exact prefixLift 1699676
  have htrace : WordTrace (prefixWord ++ tailWord_1699676) baseStart_1699676 baseEnd_1699676 := by
    simpa [prefixWord, tailWord_1699676, baseEnd_1699676] using wordTrace_append hprefix tailTrace_1699676
  have hstable : (prefixWord ++ tailWord_1699676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699676).length < 2 ^ (prefixWord ++ tailWord_1699676).sum := by decide
  have hdescent : baseEnd_1699676 < baseStart_1699676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699692 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 3]
def baseStart_1699692 : Nat := 118140960795 + 1699692 * 2 ^ 59
def prefixEnd_1699692 : Nat := 4983230072969 + 3 ^ 40 * 1699692 * 2
def baseEnd_1699692 : Nat := 872758960601869180933265

theorem tailTrace_1699692 : CollatzResearch.WordTrace tailWord_1699692 prefixEnd_1699692 872758960601869180933265 := by
  unfold tailWord_1699692
  simp only [CollatzResearch.WordTrace]
  refine ⟨30996430079156821563998665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41328573438875762085331553 30996430079156821563998665)
  ·
    refine ⟨23247322559367616172998999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30996430079156821563998665 23247322559367616172998999)
    ·
      refine ⟨34870983839051424259498499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23247322559367616172998999 34870983839051424259498499)
      ·
        refine ⟨52306475758577136389247749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34870983839051424259498499 52306475758577136389247749)
        ·
          refine ⟨9807464204733213072983953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52306475758577136389247749 9807464204733213072983953)
          ·
            refine ⟨7355598153549909804737965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9807464204733213072983953 7355598153549909804737965)
            ·
              refine ⟨2758349307581216176776737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7355598153549909804737965 2758349307581216176776737)
              ·
                refine ⟨2068761980685912132582553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758349307581216176776737 2068761980685912132582553)
                ·
                  refine ⟨1551571485514434099436915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2068761980685912132582553 1551571485514434099436915)
                  ·
                    refine ⟨2327357228271651149155373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1551571485514434099436915 2327357228271651149155373)
                    ·
                      refine ⟨872758960601869180933265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2327357228271651149155373 872758960601869180933265)
                      ·
                        rfl

theorem cell23_1699692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_1699692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699692 prefixEnd_1699692 := by exact prefixLift 1699692
  have htrace : WordTrace (prefixWord ++ tailWord_1699692) baseStart_1699692 baseEnd_1699692 := by
    simpa [prefixWord, tailWord_1699692, baseEnd_1699692] using wordTrace_append hprefix tailTrace_1699692
  have hstable : (prefixWord ++ tailWord_1699692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699692).length < 2 ^ (prefixWord ++ tailWord_1699692).sum := by decide
  have hdescent : baseEnd_1699692 < baseStart_1699692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699719 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 1, 3, 2]
def baseStart_1699719 : Nat := 118140960795 + 1699719 * 2 ^ 59
def prefixEnd_1699719 : Nat := 4983230072969 + 3 ^ 40 * 1699719 * 2
def baseEnd_1699719 : Nat := 872772824579540575295641

theorem tailTrace_1699719 : CollatzResearch.WordTrace tailWord_1699719 prefixEnd_1699719 872772824579540575295641 := by
  unfold tailWord_1699719
  simp only [CollatzResearch.WordTrace]
  refine ⟨61993844929215826739230211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41329229952810551159486807 61993844929215826739230211)
  ·
    refine ⟨92990767393823740108845317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61993844929215826739230211 92990767393823740108845317)
    ·
      refine ⟨17435768886341951270408497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92990767393823740108845317 17435768886341951270408497)
      ·
        refine ⟨13076826664756463452806373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17435768886341951270408497 13076826664756463452806373)
        ·
          refine ⟨2451904999641836897401195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13076826664756463452806373 2451904999641836897401195)
          ·
            refine ⟨3677857499462755346101793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451904999641836897401195 3677857499462755346101793)
            ·
              refine ⟨2758393124597066509576345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3677857499462755346101793 2758393124597066509576345)
              ·
                refine ⟨2068794843447799882182259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758393124597066509576345 2068794843447799882182259)
                ·
                  refine ⟨3103192265171699823273389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068794843447799882182259 3103192265171699823273389)
                  ·
                    refine ⟨1163697099439387433727521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3103192265171699823273389 1163697099439387433727521)
                    ·
                      refine ⟨872772824579540575295641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163697099439387433727521 872772824579540575295641)
                      ·
                        rfl

theorem cell23_1699719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_1699719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699719 prefixEnd_1699719 := by exact prefixLift 1699719
  have htrace : WordTrace (prefixWord ++ tailWord_1699719) baseStart_1699719 baseEnd_1699719 := by
    simpa [prefixWord, tailWord_1699719, baseEnd_1699719] using wordTrace_append hprefix tailTrace_1699719
  have hstable : (prefixWord ++ tailWord_1699719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699719).length < 2 ^ (prefixWord ++ tailWord_1699719).sum := by decide
  have hdescent : baseEnd_1699719 < baseStart_1699719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699768 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 4, 5]
def baseStart_1699768 : Nat := 118140960795 + 1699768 * 2 ^ 59
def prefixEnd_1699768 : Nat := 4983230072969 + 3 ^ 40 * 1699768 * 2
def baseEnd_1699768 : Nat := 290932661710536961194305

theorem tailTrace_1699768 : CollatzResearch.WordTrace tailWord_1699768 prefixEnd_1699768 290932661710536961194305 := by
  unfold tailWord_1699768
  simp only [CollatzResearch.WordTrace]
  refine ⟨30997816053019154053881979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41330421404025538738509305 30997816053019154053881979)
  ·
    refine ⟨46496724079528731080822969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30997816053019154053881979 46496724079528731080822969)
    ·
      refine ⟨34872543059646548310617227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46496724079528731080822969 34872543059646548310617227)
      ·
        refine ⟨52308814589469822465925841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34872543059646548310617227 52308814589469822465925841)
        ·
          refine ⟨39231610942102366849444381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52308814589469822465925841 39231610942102366849444381)
          ·
            refine ⟨14711854103288387568541643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39231610942102366849444381 14711854103288387568541643)
            ·
              refine ⟨22067781154932581352812465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14711854103288387568541643 22067781154932581352812465)
              ·
                refine ⟨16550835866199436014609349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22067781154932581352812465 16550835866199436014609349)
                ·
                  refine ⟨3103281724912394252739253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16550835866199436014609349 3103281724912394252739253)
                  ·
                    refine ⟨290932661710536961194305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3103281724912394252739253 290932661710536961194305)
                    ·
                      rfl

theorem cell23_1699768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_1699768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699768 prefixEnd_1699768 := by exact prefixLift 1699768
  have htrace : WordTrace (prefixWord ++ tailWord_1699768) baseStart_1699768 baseEnd_1699768 := by
    simpa [prefixWord, tailWord_1699768, baseEnd_1699768] using wordTrace_append hprefix tailTrace_1699768
  have hstable : (prefixWord ++ tailWord_1699768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699768).length < 2 ^ (prefixWord ++ tailWord_1699768).sum := by decide
  have hdescent : baseEnd_1699768 < baseStart_1699768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699822 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_1699822 : Nat := 118140960795 + 1699822 * 2 ^ 59
def prefixEnd_1699822 : Nat := 4983230072969 + 3 ^ 40 * 1699822 * 2
def baseEnd_1699822 : Nat := 872825713086953672307667

theorem tailTrace_1699822 : CollatzResearch.WordTrace tailWord_1699822 prefixEnd_1699822 872825713086953672307667 := by
  unfold tailWord_1699822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7749700205980334416278715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41331734431895116886819813 7749700205980334416278715)
  ·
    refine ⟨11624550308970501624418073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7749700205980334416278715 11624550308970501624418073)
    ·
      refine ⟨8718412731727876218313555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11624550308970501624418073 8718412731727876218313555)
      ·
        refine ⟨13077619097591814327470333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8718412731727876218313555 13077619097591814327470333)
        ·
          refine ⟨4904107161596930372801375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13077619097591814327470333 4904107161596930372801375)
          ·
            refine ⟨7356160742395395559202063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904107161596930372801375 7356160742395395559202063)
            ·
              refine ⟨11034241113593093338803095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7356160742395395559202063 11034241113593093338803095)
              ·
                refine ⟨16551361670389640008204643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11034241113593093338803095 16551361670389640008204643)
                ·
                  refine ⟨24827042505584460012306965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16551361670389640008204643 24827042505584460012306965)
                  ·
                    refine ⟨1163767617449271563076889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24827042505584460012306965 1163767617449271563076889)
                    ·
                      refine ⟨872825713086953672307667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163767617449271563076889 872825713086953672307667)
                      ·
                        rfl

theorem cell23_1699822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_1699822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699822 prefixEnd_1699822 := by exact prefixLift 1699822
  have htrace : WordTrace (prefixWord ++ tailWord_1699822) baseStart_1699822 baseEnd_1699822 := by
    simpa [prefixWord, tailWord_1699822, baseEnd_1699822] using wordTrace_append hprefix tailTrace_1699822
  have hstable : (prefixWord ++ tailWord_1699822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699822).length < 2 ^ (prefixWord ++ tailWord_1699822).sum := by decide
  have hdescent : baseEnd_1699822 < baseStart_1699822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699895 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_1699895 : Nat := 118140960795 + 1699895 * 2 ^ 59
def prefixEnd_1699895 : Nat := 4983230072969 + 3 ^ 40 * 1699895 * 2
def baseEnd_1699895 : Nat := 872863197174731886694831

theorem tailTrace_1699895 : CollatzResearch.WordTrace tailWord_1699895 prefixEnd_1699895 872863197174731886694831 := by
  unfold tailWord_1699895
  simp only [CollatzResearch.WordTrace]
  refine ⟨62000264176578208797637139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41333509451052139198424759 62000264176578208797637139)
  ·
    refine ⟨93000396264867313196455709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62000264176578208797637139 93000396264867313196455709)
    ·
      refine ⟨34875148599325242448670891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93000396264867313196455709 34875148599325242448670891)
      ·
        refine ⟨52312722898987863673006337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34875148599325242448670891 52312722898987863673006337)
        ·
          refine ⟨39234542174240897754754753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52312722898987863673006337 39234542174240897754754753)
          ·
            refine ⟨29425906630680673316066065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39234542174240897754754753 29425906630680673316066065)
            ·
              refine ⟨22069429973010504987049549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29425906630680673316066065 22069429973010504987049549)
              ·
                refine ⟨8276036239878939370143581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22069429973010504987049549 8276036239878939370143581)
                ·
                  refine ⟨3103513589954602263803843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8276036239878939370143581 3103513589954602263803843)
                  ·
                    refine ⟨4655270384931903395705765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3103513589954602263803843 4655270384931903395705765)
                    ·
                      refine ⟨872863197174731886694831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4655270384931903395705765 872863197174731886694831)
                      ·
                        rfl

theorem cell23_1699895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_1699895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699895 prefixEnd_1699895 := by exact prefixLift 1699895
  have htrace : WordTrace (prefixWord ++ tailWord_1699895) baseStart_1699895 baseEnd_1699895 := by
    simpa [prefixWord, tailWord_1699895, baseEnd_1699895] using wordTrace_append hprefix tailTrace_1699895
  have hstable : (prefixWord ++ tailWord_1699895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699895).length < 2 ^ (prefixWord ++ tailWord_1699895).sum := by decide
  have hdescent : baseEnd_1699895 < baseStart_1699895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699925 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1699925 : Nat := 118140960795 + 1699925 * 2 ^ 59
def prefixEnd_1699925 : Nat := 4983230072969 + 3 ^ 40 * 1699925 * 2
def baseEnd_1699925 : Nat := 872878601594366769319693

theorem tailTrace_1699925 : CollatzResearch.WordTrace tailWord_1699925 prefixEnd_1699925 872878601594366769319693 := by
  unfold tailWord_1699925
  simp only [CollatzResearch.WordTrace]
  refine ⟨62001358366469523921229229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41334238910979682614152819 62001358366469523921229229)
  ·
    refine ⟨23250509387426071470460961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62001358366469523921229229 23250509387426071470460961)
    ·
      refine ⟨17437882040569553602845721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23250509387426071470460961 17437882040569553602845721)
      ·
        refine ⟨13078411530427165202134291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17437882040569553602845721 13078411530427165202134291)
        ·
          refine ⟨19617617295640747803201437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13078411530427165202134291 19617617295640747803201437)
          ·
            refine ⟨7356606485865280426200539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19617617295640747803201437 7356606485865280426200539)
            ·
              refine ⟨11034909728797920639300809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7356606485865280426200539 11034909728797920639300809)
              ·
                refine ⟨8276182296598440479475607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11034909728797920639300809 8276182296598440479475607)
                ·
                  refine ⟨12414273444897660719213411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276182296598440479475607 12414273444897660719213411)
                  ·
                    refine ⟨18621410167346491078820117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12414273444897660719213411 18621410167346491078820117)
                    ·
                      refine ⟨872878601594366769319693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18621410167346491078820117 872878601594366769319693)
                      ·
                        rfl

theorem cell23_1699925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1699925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699925 prefixEnd_1699925 := by exact prefixLift 1699925
  have htrace : WordTrace (prefixWord ++ tailWord_1699925) baseStart_1699925 baseEnd_1699925 := by
    simpa [prefixWord, tailWord_1699925, baseEnd_1699925] using wordTrace_append hprefix tailTrace_1699925
  have hstable : (prefixWord ++ tailWord_1699925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699925).length < 2 ^ (prefixWord ++ tailWord_1699925).sum := by decide
  have hdescent : baseEnd_1699925 < baseStart_1699925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699932 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1699932 : Nat := 118140960795 + 1699932 * 2 ^ 59
def prefixEnd_1699932 : Nat := 4983230072969 + 3 ^ 40 * 1699932 * 2
def baseEnd_1699932 : Nat := 872882195958948241932161

theorem tailTrace_1699932 : CollatzResearch.WordTrace tailWord_1699932 prefixEnd_1699932 872882195958948241932161 := by
  unfold tailWord_1699932
  simp only [CollatzResearch.WordTrace]
  refine ⟨31000806838722082058367025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41334409118296109411156033 31000806838722082058367025)
  ·
    refine ⟨23250605129041561543775269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31000806838722082058367025 23250605129041561543775269)
    ·
      refine ⟨4359488461695292789457863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23250605129041561543775269 4359488461695292789457863)
      ·
        refine ⟨6539232692542939184186795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359488461695292789457863 6539232692542939184186795)
        ·
          refine ⟨9808849038814408776280193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6539232692542939184186795 9808849038814408776280193)
          ·
            refine ⟨7356636779110806582210145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9808849038814408776280193 7356636779110806582210145)
            ·
              refine ⟨5517477584333104936657609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7356636779110806582210145 5517477584333104936657609)
              ·
                refine ⟨4138108188249828702493207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5517477584333104936657609 4138108188249828702493207)
                ·
                  refine ⟨6207162282374743053739811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138108188249828702493207 6207162282374743053739811)
                  ·
                    refine ⟨9310743423562114580609717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6207162282374743053739811 9310743423562114580609717)
                    ·
                      refine ⟨872882195958948241932161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9310743423562114580609717 872882195958948241932161)
                      ·
                        rfl

theorem cell23_1699932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1699932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699932 prefixEnd_1699932 := by exact prefixLift 1699932
  have htrace : WordTrace (prefixWord ++ tailWord_1699932) baseStart_1699932 baseEnd_1699932 := by
    simpa [prefixWord, tailWord_1699932, baseEnd_1699932] using wordTrace_append hprefix tailTrace_1699932
  have hstable : (prefixWord ++ tailWord_1699932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699932).length < 2 ^ (prefixWord ++ tailWord_1699932).sum := by decide
  have hdescent : baseEnd_1699932 < baseStart_1699932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699939 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 2, 4]
def baseStart_1699939 : Nat := 118140960795 + 1699939 * 2 ^ 59
def prefixEnd_1699939 : Nat := 4983230072969 + 3 ^ 40 * 1699939 * 2
def baseEnd_1699939 : Nat := 290961930107843238181543

theorem tailTrace_1699939 : CollatzResearch.WordTrace tailWord_1699939 prefixEnd_1699939 290961930107843238181543 := by
  unfold tailWord_1699939
  simp only [CollatzResearch.WordTrace]
  refine ⟨62001868988418804312238871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41334579325612536208159247 62001868988418804312238871)
  ·
    refine ⟨93002803482628206468358307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62001868988418804312238871 93002803482628206468358307)
    ·
      refine ⟨139504205223942309702537461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93002803482628206468358307 139504205223942309702537461)
      ·
        refine ⟨13078519239744591534612887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139504205223942309702537461 13078519239744591534612887)
        ·
          refine ⟨19617778859616887301919331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13078519239744591534612887 19617778859616887301919331)
          ·
            refine ⟨29426668289425330952878997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19617778859616887301919331 29426668289425330952878997)
            ·
              refine ⟨1379375076066812388416203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29426668289425330952878997 1379375076066812388416203)
              ·
                refine ⟨2069062614100218582624305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379375076066812388416203 2069062614100218582624305)
                ·
                  refine ⟨1551796960575163936968229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2069062614100218582624305 1551796960575163936968229)
                  ·
                    refine ⟨290961930107843238181543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1551796960575163936968229 290961930107843238181543)
                    ·
                      rfl

theorem cell23_1699939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 2, 4].length) (baseStart_1699939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699939 prefixEnd_1699939 := by exact prefixLift 1699939
  have htrace : WordTrace (prefixWord ++ tailWord_1699939) baseStart_1699939 baseEnd_1699939 := by
    simpa [prefixWord, tailWord_1699939, baseEnd_1699939] using wordTrace_append hprefix tailTrace_1699939
  have hstable : (prefixWord ++ tailWord_1699939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699939).length < 2 ^ (prefixWord ++ tailWord_1699939).sum := by decide
  have hdescent : baseEnd_1699939 < baseStart_1699939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699946 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1699946 : Nat := 118140960795 + 1699946 * 2 ^ 59
def prefixEnd_1699946 : Nat := 4983230072969 + 3 ^ 40 * 1699946 * 2
def baseEnd_1699946 : Nat := 872889384688111187157097

theorem tailTrace_1699946 : CollatzResearch.WordTrace tailWord_1699946 prefixEnd_1699946 872889384688111187157097 := by
  unfold tailWord_1699946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15500531074848361126935923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41334749532928963005162461 15500531074848361126935923)
  ·
    refine ⟨23250796612272541690403885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15500531074848361126935923 23250796612272541690403885)
    ·
      refine ⟨8719048729602203133901457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23250796612272541690403885 8719048729602203133901457)
      ·
        refine ⟨6539286547201652350426093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8719048729602203133901457 6539286547201652350426093)
        ·
          refine ⟨2452232455200619631409785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6539286547201652350426093 2452232455200619631409785)
          ·
            refine ⟨1839174341400464723557339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2452232455200619631409785 1839174341400464723557339)
            ·
              refine ⟨2758761512100697085336009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839174341400464723557339 2758761512100697085336009)
              ·
                refine ⟨2069071134075522814002007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758761512100697085336009 2069071134075522814002007)
                ·
                  refine ⟨3103606701113284221003011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069071134075522814002007 3103606701113284221003011)
                  ·
                    refine ⟨4655410051669926331504517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3103606701113284221003011 4655410051669926331504517)
                    ·
                      refine ⟨872889384688111187157097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4655410051669926331504517 872889384688111187157097)
                      ·
                        rfl

theorem cell23_1699946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1699946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699946 prefixEnd_1699946 := by exact prefixLift 1699946
  have htrace : WordTrace (prefixWord ++ tailWord_1699946) baseStart_1699946 baseEnd_1699946 := by
    simpa [prefixWord, tailWord_1699946, baseEnd_1699946] using wordTrace_append hprefix tailTrace_1699946
  have hstable : (prefixWord ++ tailWord_1699946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699946).length < 2 ^ (prefixWord ++ tailWord_1699946).sum := by decide
  have hdescent : baseEnd_1699946 < baseStart_1699946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699975 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1699975 : Nat := 118140960795 + 1699975 * 2 ^ 59
def prefixEnd_1699975 : Nat := 4983230072969 + 3 ^ 40 * 1699975 * 2
def baseEnd_1699975 : Nat := 872904275627091573694463

theorem tailTrace_1699975 : CollatzResearch.WordTrace tailWord_1699975 prefixEnd_1699975 872904275627091573694463 := by
  unfold tailWord_1699975
  simp only [CollatzResearch.WordTrace]
  refine ⟨62003182016288382460549379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41335454677525588307032919 62003182016288382460549379)
  ·
    refine ⟨93004773024432573690824069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62003182016288382460549379 93004773024432573690824069)
    ·
      refine ⟨17438394942081107567029513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93004773024432573690824069 17438394942081107567029513)
      ·
        refine ⟨13078796206560830675272135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17438394942081107567029513 13078796206560830675272135)
        ·
          refine ⟨19618194309841246012908203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13078796206560830675272135 19618194309841246012908203)
          ·
            refine ⟨29427291464761869019362305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19618194309841246012908203 29427291464761869019362305)
            ·
              refine ⟨22070468598571401764521729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29427291464761869019362305 22070468598571401764521729)
              ·
                refine ⟨16552851448928551323391297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22070468598571401764521729 16552851448928551323391297)
                ·
                  refine ⟨12414638586696413492543473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16552851448928551323391297 12414638586696413492543473)
                  ·
                    refine ⟨9310978940022310119407605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12414638586696413492543473 9310978940022310119407605)
                    ·
                      refine ⟨872904275627091573694463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9310978940022310119407605 872904275627091573694463)
                      ·
                        rfl

theorem cell23_1699975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1699975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699975 prefixEnd_1699975 := by exact prefixLift 1699975
  have htrace : WordTrace (prefixWord ++ tailWord_1699975) baseStart_1699975 baseEnd_1699975 := by
    simpa [prefixWord, tailWord_1699975, baseEnd_1699975] using wordTrace_append hprefix tailTrace_1699975
  have hstable : (prefixWord ++ tailWord_1699975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699975).length < 2 ^ (prefixWord ++ tailWord_1699975).sum := by decide
  have hdescent : baseEnd_1699975 < baseStart_1699975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699990 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1699990 : Nat := 118140960795 + 1699990 * 2 ^ 59
def prefixEnd_1699990 : Nat := 4983230072969 + 3 ^ 40 * 1699990 * 2
def baseEnd_1699990 : Nat := 290970659278969671668965

theorem tailTrace_1699990 : CollatzResearch.WordTrace tailWord_1699990 prefixEnd_1699990 290970659278969671668965 := by
  unfold tailWord_1699990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3875233069452127501396589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41335819407489360014896949 3875233069452127501396589)
  ·
    refine ⟨1453212401044547813023721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3875233069452127501396589 1453212401044547813023721)
    ·
      refine ⟨1089909300783410859767791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1453212401044547813023721 1089909300783410859767791)
      ·
        refine ⟨1634863951175116289651687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089909300783410859767791 1634863951175116289651687)
        ·
          refine ⟨2452295926762674434477531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634863951175116289651687 2452295926762674434477531)
          ·
            refine ⟨3678443890144011651716297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452295926762674434477531 3678443890144011651716297)
            ·
              refine ⟨2758832917608008738787223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678443890144011651716297 2758832917608008738787223)
              ·
                refine ⟨4138249376412013108180835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758832917608008738787223 4138249376412013108180835)
                ·
                  refine ⟨6207374064618019662271253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138249376412013108180835 6207374064618019662271253)
                  ·
                    refine ⟨290970659278969671668965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6207374064618019662271253 290970659278969671668965)
                    ·
                      rfl

theorem cell23_1699990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1699990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1699990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1699990 prefixEnd_1699990 := by exact prefixLift 1699990
  have htrace : WordTrace (prefixWord ++ tailWord_1699990) baseStart_1699990 baseEnd_1699990 := by
    simpa [prefixWord, tailWord_1699990, baseEnd_1699990] using wordTrace_append hprefix tailTrace_1699990
  have hstable : (prefixWord ++ tailWord_1699990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699990).length < 2 ^ (prefixWord ++ tailWord_1699990).sum := by decide
  have hdescent : baseEnd_1699990 < baseStart_1699990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700015 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_1700015 : Nat := 118140960795 + 1700015 * 2 ^ 59
def prefixEnd_1700015 : Nat := 4983230072969 + 3 ^ 40 * 1700015 * 2
def baseEnd_1700015 : Nat := 872924814853271417194279

theorem tailTrace_1700015 : CollatzResearch.WordTrace tailWord_1700015 prefixEnd_1700015 872924814853271417194279 := by
  unfold tailWord_1700015
  simp only [CollatzResearch.WordTrace]
  refine ⟨62004640936143469292005499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41336427290762312861336999 62004640936143469292005499)
  ·
    refine ⟨93006961404215203938008249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62004640936143469292005499 93006961404215203938008249)
    ·
      refine ⟨69755221053161402953506187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93006961404215203938008249 69755221053161402953506187)
      ·
        refine ⟨104632831579742104430259281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69755221053161402953506187 104632831579742104430259281)
        ·
          refine ⟨78474623684806578322694461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104632831579742104430259281 78474623684806578322694461)
          ·
            refine ⟨29427983881802466871010423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78474623684806578322694461 29427983881802466871010423)
            ·
              refine ⟨44141975822703700306515635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29427983881802466871010423 44141975822703700306515635)
              ·
                refine ⟨66212963734055550459773453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44141975822703700306515635 66212963734055550459773453)
                ·
                  refine ⟨24829861400270831422415045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66212963734055550459773453 24829861400270831422415045)
                  ·
                    refine ⟨4655599012550780891702821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24829861400270831422415045 4655599012550780891702821)
                    ·
                      refine ⟨872924814853271417194279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4655599012550780891702821 872924814853271417194279)
                      ·
                        rfl

theorem cell23_1700015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_1700015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700015 prefixEnd_1700015 := by exact prefixLift 1700015
  have htrace : WordTrace (prefixWord ++ tailWord_1700015) baseStart_1700015 baseEnd_1700015 := by
    simpa [prefixWord, tailWord_1700015, baseEnd_1700015] using wordTrace_append hprefix tailTrace_1700015
  have hstable : (prefixWord ++ tailWord_1700015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700015).length < 2 ^ (prefixWord ++ tailWord_1700015).sum := by decide
  have hdescent : baseEnd_1700015 < baseStart_1700015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700019 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 4, 2, 2]
def baseStart_1700019 : Nat := 118140960795 + 1700019 * 2 ^ 59
def prefixEnd_1700019 : Nat := 4983230072969 + 3 ^ 40 * 1700019 * 2
def baseEnd_1700019 : Nat := 872926868775889401544261

theorem tailTrace_1700019 : CollatzResearch.WordTrace tailWord_1700019 prefixEnd_1700019 872926868775889401544261 := by
  unfold tailWord_1700019
  simp only [CollatzResearch.WordTrace]
  refine ⟨62004786828128977975151111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41336524552085985316767407 62004786828128977975151111)
  ·
    refine ⟨93007180242193466962726667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62004786828128977975151111 93007180242193466962726667)
    ·
      refine ⟨139510770363290200444090001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93007180242193466962726667 139510770363290200444090001)
      ·
        refine ⟨104633077772467650333067501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139510770363290200444090001 104633077772467650333067501)
        ·
          refine ⟨39237404164675368874900313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104633077772467650333067501 39237404164675368874900313)
          ·
            refine ⟨29428053123506526656175235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39237404164675368874900313 29428053123506526656175235)
            ·
              refine ⟨44142079685259789984262853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29428053123506526656175235 44142079685259789984262853)
              ·
                refine ⟨8276639940986210622049285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44142079685259789984262853 8276639940986210622049285)
                ·
                  refine ⟨1551869988934914491634241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8276639940986210622049285 1551869988934914491634241)
                  ·
                    refine ⟨1163902491701185868725681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1551869988934914491634241 1163902491701185868725681)
                    ·
                      refine ⟨872926868775889401544261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163902491701185868725681 872926868775889401544261)
                      ·
                        rfl

theorem cell23_1700019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 2, 2].length) (baseStart_1700019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700019 prefixEnd_1700019 := by exact prefixLift 1700019
  have htrace : WordTrace (prefixWord ++ tailWord_1700019) baseStart_1700019 baseEnd_1700019 := by
    simpa [prefixWord, tailWord_1700019, baseEnd_1700019] using wordTrace_append hprefix tailTrace_1700019
  have hstable : (prefixWord ++ tailWord_1700019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700019).length < 2 ^ (prefixWord ++ tailWord_1700019).sum := by decide
  have hdescent : baseEnd_1700019 < baseStart_1700019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700023 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 1, 3, 2]
def baseStart_1700023 : Nat := 118140960795 + 1700023 * 2 ^ 59
def prefixEnd_1700023 : Nat := 4983230072969 + 3 ^ 40 * 1700023 * 2
def baseEnd_1700023 : Nat := 872928922698507385894243

theorem tailTrace_1700023 : CollatzResearch.WordTrace tailWord_1700023 prefixEnd_1700023 872928922698507385894243 := by
  unfold tailWord_1700023
  simp only [CollatzResearch.WordTrace]
  refine ⟨62004932720114486658296723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41336621813409657772197815 62004932720114486658296723)
  ·
    refine ⟨93007399080171729987445085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62004932720114486658296723 93007399080171729987445085)
    ·
      refine ⟨34877774655064398745291907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93007399080171729987445085 34877774655064398745291907)
      ·
        refine ⟨52316661982596598117937861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34877774655064398745291907 52316661982596598117937861)
        ·
          refine ⟨9809374121736862147113349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52316661982596598117937861 9809374121736862147113349)
          ·
            refine ⟨1839257647825661652583753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9809374121736862147113349 1839257647825661652583753)
            ·
              refine ⟨1379443235869246239437815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1839257647825661652583753 1379443235869246239437815)
              ·
                refine ⟨2069164853803869359156723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379443235869246239437815 2069164853803869359156723)
                ·
                  refine ⟨3103747280705804038735085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069164853803869359156723 3103747280705804038735085)
                  ·
                    refine ⟨1163905230264676514525657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3103747280705804038735085 1163905230264676514525657)
                    ·
                      refine ⟨872928922698507385894243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163905230264676514525657 872928922698507385894243)
                      ·
                        rfl

theorem cell23_1700023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_1700023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700023 prefixEnd_1700023 := by exact prefixLift 1700023
  have htrace : WordTrace (prefixWord ++ tailWord_1700023) baseStart_1700023 baseEnd_1700023 := by
    simpa [prefixWord, tailWord_1700023, baseEnd_1700023] using wordTrace_append hprefix tailTrace_1700023
  have hstable : (prefixWord ++ tailWord_1700023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700023).length < 2 ^ (prefixWord ++ tailWord_1700023).sum := by decide
  have hdescent : baseEnd_1700023 < baseStart_1700023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700025 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 9]
def baseStart_1700025 : Nat := 118140960795 + 1700025 * 2 ^ 59
def prefixEnd_1700025 : Nat := 4983230072969 + 3 ^ 40 * 1700025 * 2
def baseEnd_1700025 : Nat := 96992216628868486452137

theorem tailTrace_1700025 : CollatzResearch.WordTrace tailWord_1700025 prefixEnd_1700025 96992216628868486452137 := by
  unfold tailWord_1700025
  simp only [CollatzResearch.WordTrace]
  refine ⟨62005005666107240999869529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41336670444071493999913019 62005005666107240999869529)
  ·
    refine ⟨46503754249580430749902147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62005005666107240999869529 46503754249580430749902147)
    ·
      refine ⟨69755631374370646124853221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46503754249580430749902147 69755631374370646124853221)
      ·
        refine ⟨13079180882694496148409979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69755631374370646124853221 13079180882694496148409979)
        ·
          refine ⟨19618771324041744222614969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13079180882694496148409979 19618771324041744222614969)
          ·
            refine ⟨14714078493031308166961227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19618771324041744222614969 14714078493031308166961227)
            ·
              refine ⟨22071117739546962250441841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14714078493031308166961227 22071117739546962250441841)
              ·
                refine ⟨16553338304660221687831381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22071117739546962250441841 16553338304660221687831381)
                ·
                  refine ⟨96992216628868486452137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16553338304660221687831381 96992216628868486452137)
                  ·
                    rfl

theorem cell23_1700025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 9].length) (baseStart_1700025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700025 prefixEnd_1700025 := by exact prefixLift 1700025
  have htrace : WordTrace (prefixWord ++ tailWord_1700025) baseStart_1700025 baseEnd_1700025 := by
    simpa [prefixWord, tailWord_1700025, baseEnd_1700025] using wordTrace_append hprefix tailTrace_1700025
  have hstable : (prefixWord ++ tailWord_1700025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700025).length < 2 ^ (prefixWord ++ tailWord_1700025).sum := by decide
  have hdescent : baseEnd_1700025 < baseStart_1700025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700030 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_1700030 : Nat := 118140960795 + 1700030 * 2 ^ 59
def prefixEnd_1700030 : Nat := 4983230072969 + 3 ^ 40 * 1700030 * 2
def baseEnd_1700030 : Nat := 872932517063088858506711

theorem tailTrace_1700030 : CollatzResearch.WordTrace tailWord_1700030 prefixEnd_1700030 872932517063088858506711 := by
  unfold tailWord_1700030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7750648503886140856725193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41336792020726084569201029 7750648503886140856725193)
  ·
    refine ⟨5812986377914605642543895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7750648503886140856725193 5812986377914605642543895)
    ·
      refine ⟨8719479566871908463815843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5812986377914605642543895 8719479566871908463815843)
      ·
        refine ⟨13079219350307862695723765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8719479566871908463815843 13079219350307862695723765)
        ·
          refine ⟨1226176814091362127724103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13079219350307862695723765 1226176814091362127724103)
          ·
            refine ⟨1839265221137043191586155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226176814091362127724103 1839265221137043191586155)
            ·
              refine ⟨2758897831705564787379233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839265221137043191586155 2758897831705564787379233)
              ·
                refine ⟨2069173373779173590534425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758897831705564787379233 2069173373779173590534425)
                ·
                  refine ⟨1551880030334380192900819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2069173373779173590534425 1551880030334380192900819)
                  ·
                    refine ⟨2327820045501570289351229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1551880030334380192900819 2327820045501570289351229)
                    ·
                      refine ⟨872932517063088858506711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2327820045501570289351229 872932517063088858506711)
                      ·
                        rfl

theorem cell23_1700030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_1700030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700030 prefixEnd_1700030 := by exact prefixLift 1700030
  have htrace : WordTrace (prefixWord ++ tailWord_1700030) baseStart_1700030 baseEnd_1700030 := by
    simpa [prefixWord, tailWord_1700030, baseEnd_1700030] using wordTrace_append hprefix tailTrace_1700030
  have hstable : (prefixWord ++ tailWord_1700030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700030).length < 2 ^ (prefixWord ++ tailWord_1700030).sum := by decide
  have hdescent : baseEnd_1700030 < baseStart_1700030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700032 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_1700032 : Nat := 118140960795 + 1700032 * 2 ^ 59
def prefixEnd_1700032 : Nat := 4983230072969 + 3 ^ 40 * 1700032 * 2
def baseEnd_1700032 : Nat := 872933544024397850681701

theorem tailTrace_1700032 : CollatzResearch.WordTrace tailWord_1700032 prefixEnd_1700032 872933544024397850681701 := by
  unfold tailWord_1700032
  simp only [CollatzResearch.WordTrace]
  refine ⟨31002630488540940597687175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41336840651387920796916233 31002630488540940597687175)
  ·
    refine ⟨46503945732811410896530763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31002630488540940597687175 46503945732811410896530763)
    ·
      refine ⟨69755918599217116344796145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46503945732811410896530763 69755918599217116344796145)
      ·
        refine ⟨52316938949412837258597109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69755918599217116344796145 52316938949412837258597109)
        ·
          refine ⟨4904713026507453492993479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52316938949412837258597109 4904713026507453492993479)
          ·
            refine ⟨7357069539761180239490219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904713026507453492993479 7357069539761180239490219)
            ·
              refine ⟨11035604309641770359235329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7357069539761180239490219 11035604309641770359235329)
              ·
                refine ⟨8276703232231327769426497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11035604309641770359235329 8276703232231327769426497)
                ·
                  refine ⟨6207527424173495827069873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8276703232231327769426497 6207527424173495827069873)
                  ·
                    refine ⟨4655645568130121870302405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6207527424173495827069873 4655645568130121870302405)
                    ·
                      refine ⟨872933544024397850681701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4655645568130121870302405 872933544024397850681701)
                      ·
                        rfl

theorem cell23_1700032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_1700032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700032 prefixEnd_1700032 := by exact prefixLift 1700032
  have htrace : WordTrace (prefixWord ++ tailWord_1700032) baseStart_1700032 baseEnd_1700032 := by
    simpa [prefixWord, tailWord_1700032, baseEnd_1700032] using wordTrace_append hprefix tailTrace_1700032
  have hstable : (prefixWord ++ tailWord_1700032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700032).length < 2 ^ (prefixWord ++ tailWord_1700032).sum := by decide
  have hdescent : baseEnd_1700032 < baseStart_1700032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700042 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 7]
def baseStart_1700042 : Nat := 118140960795 + 1700042 * 2 ^ 59
def prefixEnd_1700042 : Nat := 4983230072969 + 3 ^ 40 * 1700042 * 2
def baseEnd_1700042 : Nat := 96993186536771423506295

theorem tailTrace_1700042 : CollatzResearch.WordTrace tailWord_1700042 prefixEnd_1700042 96993186536771423506295 := by
  unfold tailWord_1700042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15501406426761413225809595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41337083804697101935492253 15501406426761413225809595)
  ·
    refine ⟨23252109640142119838714393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15501406426761413225809595 23252109640142119838714393)
    ·
      refine ⟨17439082230106589879035795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23252109640142119838714393 17439082230106589879035795)
      ·
        refine ⟨26158623345159884818553693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17439082230106589879035795 26158623345159884818553693)
        ·
          refine ⟨9809483754434956806957635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26158623345159884818553693 9809483754434956806957635)
          ·
            refine ⟨14714225631652435210436453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9809483754434956806957635 14714225631652435210436453)
            ·
              refine ⟨2758917305934831601956835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14714225631652435210436453 2758917305934831601956835)
              ·
                refine ⟨4138375958902247402935253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758917305934831601956835 4138375958902247402935253)
                ·
                  refine ⟨96993186536771423506295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4138375958902247402935253 96993186536771423506295)
                  ·
                    rfl

theorem cell23_1700042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_1700042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700042 prefixEnd_1700042 := by exact prefixLift 1700042
  have htrace : WordTrace (prefixWord ++ tailWord_1700042) baseStart_1700042 baseEnd_1700042 := by
    simpa [prefixWord, tailWord_1700042, baseEnd_1700042] using wordTrace_append hprefix tailTrace_1700042
  have hstable : (prefixWord ++ tailWord_1700042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700042).length < 2 ^ (prefixWord ++ tailWord_1700042).sum := by decide
  have hdescent : baseEnd_1700042 < baseStart_1700042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700053 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1700053 : Nat := 118140960795 + 1700053 * 2 ^ 59
def prefixEnd_1700053 : Nat := 4983230072969 + 3 ^ 40 * 1700053 * 2
def baseEnd_1700053 : Nat := 872944327118142268519105

theorem tailTrace_1700053 : CollatzResearch.WordTrace tailWord_1700053 prefixEnd_1700053 872944327118142268519105 := by
  unfold tailWord_1700053
  simp only [CollatzResearch.WordTrace]
  refine ⟨62006026910005801781888813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41337351273337201187925875 62006026910005801781888813)
  ·
    refine ⟨23252260091252175668208305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62006026910005801781888813 23252260091252175668208305)
    ·
      refine ⟨17439195068439131751156229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23252260091252175668208305 17439195068439131751156229)
      ·
        refine ⟨3269849075332337203341793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17439195068439131751156229 3269849075332337203341793)
        ·
          refine ⟨2452386806499252902506345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3269849075332337203341793 2452386806499252902506345)
          ·
            refine ⟨1839290104874439676879759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2452386806499252902506345 1839290104874439676879759)
            ·
              refine ⟨2758935157311659515319639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839290104874439676879759 2758935157311659515319639)
              ·
                refine ⟨4138402735967489272979459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758935157311659515319639 4138402735967489272979459)
                ·
                  refine ⟨6207604103951233909469189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138402735967489272979459 6207604103951233909469189)
                  ·
                    refine ⟨1163925769490856358025473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6207604103951233909469189 1163925769490856358025473)
                    ·
                      refine ⟨872944327118142268519105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1163925769490856358025473 872944327118142268519105)
                      ·
                        rfl

theorem cell23_1700053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1700053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700053 prefixEnd_1700053 := by exact prefixLift 1700053
  have htrace : WordTrace (prefixWord ++ tailWord_1700053) baseStart_1700053 baseEnd_1700053 := by
    simpa [prefixWord, tailWord_1700053, baseEnd_1700053] using wordTrace_append hprefix tailTrace_1700053
  have hstable : (prefixWord ++ tailWord_1700053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700053).length < 2 ^ (prefixWord ++ tailWord_1700053).sum := by decide
  have hdescent : baseEnd_1700053 < baseStart_1700053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700072 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1700072 : Nat := 118140960795 + 1700072 * 2 ^ 59
def prefixEnd_1700072 : Nat := 4983230072969 + 3 ^ 40 * 1700072 * 2
def baseEnd_1700072 : Nat := 290984694416859231393839

theorem tailTrace_1700072 : CollatzResearch.WordTrace tailWord_1700072 prefixEnd_1700072 290984694416859231393839 := by
  unfold tailWord_1700072
  simp only [CollatzResearch.WordTrace]
  refine ⟨31003359948468484013415235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41337813264624645351220313 31003359948468484013415235)
  ·
    refine ⟨46505039922702726020122853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31003359948468484013415235 46505039922702726020122853)
    ·
      refine ⟨8719694985506761128773035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46505039922702726020122853 8719694985506761128773035)
      ·
        refine ⟨13079542478260141693159553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8719694985506761128773035 13079542478260141693159553)
        ·
          refine ⟨9809656858695106269869665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13079542478260141693159553 9809656858695106269869665)
          ·
            refine ⟨7357242644021329702402249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9809656858695106269869665 7357242644021329702402249)
            ·
              refine ⟨5517931983015997276801687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7357242644021329702402249 5517931983015997276801687)
              ·
                refine ⟨8276897974523995915202531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517931983015997276801687 8276897974523995915202531)
                ·
                  refine ⟨12415346961785993872803797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276897974523995915202531 12415346961785993872803797)
                  ·
                    refine ⟨290984694416859231393839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12415346961785993872803797 290984694416859231393839)
                    ·
                      rfl

theorem cell23_1700072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1700072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700072 prefixEnd_1700072 := by exact prefixLift 1700072
  have htrace : WordTrace (prefixWord ++ tailWord_1700072) baseStart_1700072 baseEnd_1700072 := by
    simpa [prefixWord, tailWord_1700072, baseEnd_1700072] using wordTrace_append hprefix tailTrace_1700072
  have hstable : (prefixWord ++ tailWord_1700072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700072).length < 2 ^ (prefixWord ++ tailWord_1700072).sum := by decide
  have hdescent : baseEnd_1700072 < baseStart_1700072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700129 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1700129 : Nat := 118140960795 + 1700129 * 2 ^ 59
def prefixEnd_1700129 : Nat := 4983230072969 + 3 ^ 40 * 1700129 * 2
def baseEnd_1700129 : Nat := 872983351647883971168755

theorem tailTrace_1700129 : CollatzResearch.WordTrace tailWord_1700129 prefixEnd_1700129 872983351647883971168755 := by
  unfold tailWord_1700129
  simp only [CollatzResearch.WordTrace]
  refine ⟨62008798857730466761655441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41339199238486977841103627 62008798857730466761655441)
  ·
    refine ⟨46506599143297850071241581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62008798857730466761655441 46506599143297850071241581)
    ·
      refine ⟨17439974678736693776715593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46506599143297850071241581 17439974678736693776715593)
      ·
        refine ⟨13079981009052520332536695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17439974678736693776715593 13079981009052520332536695)
        ·
          refine ⟨19619971513578780498805043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13079981009052520332536695 19619971513578780498805043)
          ·
            refine ⟨29429957270368170748207565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19619971513578780498805043 29429957270368170748207565)
            ·
              refine ⟨11036233976388064030577837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29429957270368170748207565 11036233976388064030577837)
              ·
                refine ⟨4138587741145524011466689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11036233976388064030577837 4138587741145524011466689)
                ·
                  refine ⟨3103940805859143008600017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4138587741145524011466689 3103940805859143008600017)
                  ·
                    refine ⟨2327955604394357256450013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3103940805859143008600017 2327955604394357256450013)
                    ·
                      refine ⟨872983351647883971168755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2327955604394357256450013 872983351647883971168755)
                      ·
                        rfl

theorem cell23_1700129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1700129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700129 prefixEnd_1700129 := by exact prefixLift 1700129
  have htrace : WordTrace (prefixWord ++ tailWord_1700129) baseStart_1700129 baseEnd_1700129 := by
    simpa [prefixWord, tailWord_1700129, baseEnd_1700129] using wordTrace_append hprefix tailTrace_1700129
  have hstable : (prefixWord ++ tailWord_1700129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700129).length < 2 ^ (prefixWord ++ tailWord_1700129).sum := by decide
  have hdescent : baseEnd_1700129 < baseStart_1700129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700149 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 6]
def baseStart_1700149 : Nat := 118140960795 + 1700149 * 2 ^ 59
def prefixEnd_1700149 : Nat := 4983230072969 + 3 ^ 40 * 1700149 * 2
def baseEnd_1700149 : Nat := 96999291251219321435407

theorem tailTrace_1700149 : CollatzResearch.WordTrace tailWord_1700149 prefixEnd_1700149 96999291251219321435407 := by
  unfold tailWord_1700149
  simp only [CollatzResearch.WordTrace]
  refine ⟨62009528317658010177383501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41339685545105340118255667 62009528317658010177383501)
  ·
    refine ⟨23253573119121753816518813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62009528317658010177383501 23253573119121753816518813)
    ·
      refine ⟨8720089919670657681194555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23253573119121753816518813 8720089919670657681194555)
      ·
        refine ⟨13080134879505986521791833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8720089919670657681194555 13080134879505986521791833)
        ·
          refine ⟨9810101159629489891343875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13080134879505986521791833 9810101159629489891343875)
          ·
            refine ⟨14715151739444234837015813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9810101159629489891343875 14715151739444234837015813)
            ·
              refine ⟨2759090951145794031940465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14715151739444234837015813 2759090951145794031940465)
              ·
                refine ⟨2069318213359345523955349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759090951145794031940465 2069318213359345523955349)
                ·
                  refine ⟨96999291251219321435407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2069318213359345523955349 96999291251219321435407)
                  ·
                    rfl

theorem cell23_1700149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_1700149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700149 prefixEnd_1700149 := by exact prefixLift 1700149
  have htrace : WordTrace (prefixWord ++ tailWord_1700149) baseStart_1700149 baseEnd_1700149 := by
    simpa [prefixWord, tailWord_1700149, baseEnd_1700149] using wordTrace_append hprefix tailTrace_1700149
  have hstable : (prefixWord ++ tailWord_1700149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700149).length < 2 ^ (prefixWord ++ tailWord_1700149).sum := by decide
  have hdescent : baseEnd_1700149 < baseStart_1700149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700153 : List Nat := [1, 2, 1, 6, 1, 2, 1, 4, 1, 4]
def baseStart_1700153 : Nat := 118140960795 + 1700153 * 2 ^ 59
def prefixEnd_1700153 : Nat := 4983230072969 + 3 ^ 40 * 1700153 * 2
def baseEnd_1700153 : Nat := 290998558394530625756215

theorem tailTrace_1700153 : CollatzResearch.WordTrace tailWord_1700153 prefixEnd_1700153 290998558394530625756215 := by
  unfold tailWord_1700153
  simp only [CollatzResearch.WordTrace]
  refine ⟨62009674209643518860529113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41339782806429012573686075 62009674209643518860529113)
  ·
    refine ⟨46507255657232639145396835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62009674209643518860529113 46507255657232639145396835)
    ·
      refine ⟨69760883485848958718095253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46507255657232639145396835 69760883485848958718095253)
      ·
        refine ⟨3270041413399169939910715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69760883485848958718095253 3270041413399169939910715)
        ·
          refine ⟨4905062120098754909866073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3270041413399169939910715 4905062120098754909866073)
          ·
            refine ⟨3678796590074066182399555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4905062120098754909866073 3678796590074066182399555)
            ·
              refine ⟨5518194885111099273599333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678796590074066182399555 5518194885111099273599333)
              ·
                refine ⟨1034661540958331113799875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5518194885111099273599333 1034661540958331113799875)
                ·
                  refine ⟨1551992311437496670699813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034661540958331113799875 1551992311437496670699813)
                  ·
                    refine ⟨290998558394530625756215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1551992311437496670699813 290998558394530625756215)
                    ·
                      rfl

theorem cell23_1700153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 1, 4].length) (baseStart_1700153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700153 prefixEnd_1700153 := by exact prefixLift 1700153
  have htrace : WordTrace (prefixWord ++ tailWord_1700153) baseStart_1700153 baseEnd_1700153 := by
    simpa [prefixWord, tailWord_1700153, baseEnd_1700153] using wordTrace_append hprefix tailTrace_1700153
  have hstable : (prefixWord ++ tailWord_1700153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700153).length < 2 ^ (prefixWord ++ tailWord_1700153).sum := by decide
  have hdescent : baseEnd_1700153 < baseStart_1700153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700169 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 1, 5, 2]
def baseStart_1700169 : Nat := 118140960795 + 1700169 * 2 ^ 59
def prefixEnd_1700169 : Nat := 4983230072969 + 3 ^ 40 * 1700169 * 2
def baseEnd_1700169 : Nat := 873003890874063814668571

theorem tailTrace_1700169 : CollatzResearch.WordTrace tailWord_1700169 prefixEnd_1700169 873003890874063814668571 := by
  unfold tailWord_1700169
  simp only [CollatzResearch.WordTrace]
  refine ⟨62010257777585553593111561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41340171851723702395407707 62010257777585553593111561)
  ·
    refine ⟨46507693333189165194833671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62010257777585553593111561 46507693333189165194833671)
    ·
      refine ⟨69761539999783747792250507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46507693333189165194833671 69761539999783747792250507)
      ·
        refine ⟨104642309999675621688375761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69761539999783747792250507 104642309999675621688375761)
        ·
          refine ⟨78481732499756716266281821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104642309999675621688375761 78481732499756716266281821)
          ·
            refine ⟨29430649687408768599855683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78481732499756716266281821 29430649687408768599855683)
            ·
              refine ⟨44145974531113152899783525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29430649687408768599855683 44145974531113152899783525)
              ·
                refine ⟨8277370224583716168709411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44145974531113152899783525 8277370224583716168709411)
                ·
                  refine ⟨12416055336875574253064117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8277370224583716168709411 12416055336875574253064117)
                  ·
                    refine ⟨1164005187832085086224761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12416055336875574253064117 1164005187832085086224761)
                    ·
                      refine ⟨873003890874063814668571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164005187832085086224761 873003890874063814668571)
                      ·
                        rfl

theorem cell23_1700169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 5, 2].length) (baseStart_1700169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700169 prefixEnd_1700169 := by exact prefixLift 1700169
  have htrace : WordTrace (prefixWord ++ tailWord_1700169) baseStart_1700169 baseEnd_1700169 := by
    simpa [prefixWord, tailWord_1700169, baseEnd_1700169] using wordTrace_append hprefix tailTrace_1700169
  have hstable : (prefixWord ++ tailWord_1700169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700169).length < 2 ^ (prefixWord ++ tailWord_1700169).sum := by decide
  have hdescent : baseEnd_1700169 < baseStart_1700169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700172 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1700172 : Nat := 118140960795 + 1700172 * 2 ^ 59
def prefixEnd_1700172 : Nat := 4983230072969 + 3 ^ 40 * 1700172 * 2
def baseEnd_1700172 : Nat := 873005431316027302931057

theorem tailTrace_1700172 : CollatzResearch.WordTrace tailWord_1700172 prefixEnd_1700172 873005431316027302931057 := by
  unfold tailWord_1700172
  simp only [CollatzResearch.WordTrace]
  refine ⟨31005183598287342552735385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41340244797716456736980513 31005183598287342552735385)
  ·
    refine ⟨23253887698715506914551539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31005183598287342552735385 23253887698715506914551539)
    ·
      refine ⟨34880831548073260371827309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23253887698715506914551539 34880831548073260371827309)
      ·
        refine ⟨13080311830527472639435241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34880831548073260371827309 13080311830527472639435241)
        ·
          refine ⟨9810233872895604479576431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13080311830527472639435241 9810233872895604479576431)
          ·
            refine ⟨14715350809343406719364647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9810233872895604479576431 14715350809343406719364647)
            ·
              refine ⟨22073026214015110079046971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14715350809343406719364647 22073026214015110079046971)
              ·
                refine ⟨33109539321022665118570457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22073026214015110079046971 33109539321022665118570457)
                ·
                  refine ⟨24832154490766998838927843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33109539321022665118570457 24832154490766998838927843)
                  ·
                    refine ⟨37248231736150498258391765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24832154490766998838927843 37248231736150498258391765)
                    ·
                      refine ⟨873005431316027302931057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37248231736150498258391765 873005431316027302931057)
                      ·
                        rfl

theorem cell23_1700172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1700172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700172 prefixEnd_1700172 := by exact prefixLift 1700172
  have htrace : WordTrace (prefixWord ++ tailWord_1700172) baseStart_1700172 baseEnd_1700172 := by
    simpa [prefixWord, tailWord_1700172, baseEnd_1700172] using wordTrace_append hprefix tailTrace_1700172
  have hstable : (prefixWord ++ tailWord_1700172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700172).length < 2 ^ (prefixWord ++ tailWord_1700172).sum := by decide
  have hdescent : baseEnd_1700172 < baseStart_1700172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700176 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 3, 1, 3]
def baseStart_1700176 : Nat := 118140960795 + 1700176 * 2 ^ 59
def prefixEnd_1700176 : Nat := 4983230072969 + 3 ^ 40 * 1700176 * 2
def baseEnd_1700176 : Nat := 873007485238645287281039

theorem tailTrace_1700176 : CollatzResearch.WordTrace tailWord_1700176 prefixEnd_1700176 873007485238645287281039 := by
  unfold tailWord_1700176
  simp only [CollatzResearch.WordTrace]
  refine ⟨31005256544280096894308191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41340342059040129192410921 31005256544280096894308191)
  ·
    refine ⟨46507884816420145341462287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31005256544280096894308191 46507884816420145341462287)
    ·
      refine ⟨69761827224630218012193431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46507884816420145341462287 69761827224630218012193431)
      ·
        refine ⟨104642740836945327018290147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69761827224630218012193431 104642740836945327018290147)
        ·
          refine ⟨156964111255417990527435221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104642740836945327018290147 156964111255417990527435221)
          ·
            refine ⟨3678846357548859152986763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 156964111255417990527435221 3678846357548859152986763)
            ·
              refine ⟨5518269536323288729480145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678846357548859152986763 5518269536323288729480145)
              ·
                refine ⟨4138702152242466547110109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5518269536323288729480145 4138702152242466547110109)
                ·
                  refine ⟨1552013307090924955166291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4138702152242466547110109 1552013307090924955166291)
                  ·
                    refine ⟨2328019960636387432749437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1552013307090924955166291 2328019960636387432749437)
                    ·
                      refine ⟨873007485238645287281039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2328019960636387432749437 873007485238645287281039)
                      ·
                        rfl

theorem cell23_1700176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3, 1, 3].length) (baseStart_1700176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700176 prefixEnd_1700176 := by exact prefixLift 1700176
  have htrace : WordTrace (prefixWord ++ tailWord_1700176) baseStart_1700176 baseEnd_1700176 := by
    simpa [prefixWord, tailWord_1700176, baseEnd_1700176] using wordTrace_append hprefix tailTrace_1700176
  have hstable : (prefixWord ++ tailWord_1700176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700176).length < 2 ^ (prefixWord ++ tailWord_1700176).sum := by decide
  have hdescent : baseEnd_1700176 < baseStart_1700176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700219 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 5]
def baseStart_1700219 : Nat := 118140960795 + 1700219 * 2 ^ 59
def prefixEnd_1700219 : Nat := 4983230072969 + 3 ^ 40 * 1700219 * 2
def baseEnd_1700219 : Nat := 873029564906788619043341

theorem tailTrace_1700219 : CollatzResearch.WordTrace tailWord_1700219 prefixEnd_1700219 873029564906788619043341 := by
  unfold tailWord_1700219
  simp only [CollatzResearch.WordTrace]
  refine ⟨62012081427404412132431711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41341387618269608088287807 62012081427404412132431711)
  ·
    refine ⟨93018122141106618198647567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62012081427404412132431711 93018122141106618198647567)
    ·
      refine ⟨139527183211659927297971351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93018122141106618198647567 139527183211659927297971351)
      ·
        refine ⟨209290774817489890946957027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139527183211659927297971351 209290774817489890946957027)
        ·
          refine ⟨313936162226234836420435541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209290774817489890946957027 313936162226234836420435541)
          ·
            refine ⟨3678939401088689489301979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 313936162226234836420435541 3678939401088689489301979)
            ·
              refine ⟨5518409101633034233952969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678939401088689489301979 5518409101633034233952969)
              ·
                refine ⟨4138806826224775675464727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5518409101633034233952969 4138806826224775675464727)
                ·
                  refine ⟨6208210239337163513197091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138806826224775675464727 6208210239337163513197091)
                  ·
                    refine ⟨9312315359005745269795637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6208210239337163513197091 9312315359005745269795637)
                    ·
                      refine ⟨873029564906788619043341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9312315359005745269795637 873029564906788619043341)
                      ·
                        rfl

theorem cell23_1700219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 5].length) (baseStart_1700219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700219 prefixEnd_1700219 := by exact prefixLift 1700219
  have htrace : WordTrace (prefixWord ++ tailWord_1700219) baseStart_1700219 baseEnd_1700219 := by
    simpa [prefixWord, tailWord_1700219, baseEnd_1700219] using wordTrace_append hprefix tailTrace_1700219
  have hstable : (prefixWord ++ tailWord_1700219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700219).length < 2 ^ (prefixWord ++ tailWord_1700219).sum := by decide
  have hdescent : baseEnd_1700219 < baseStart_1700219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700233 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 3, 2, 2]
def baseStart_1700233 : Nat := 118140960795 + 1700233 * 2 ^ 59
def prefixEnd_1700233 : Nat := 4983230072969 + 3 ^ 40 * 1700233 * 2
def baseEnd_1700233 : Nat := 873036753635951564268277

theorem tailTrace_1700233 : CollatzResearch.WordTrace tailWord_1700233 prefixEnd_1700233 873036753635951564268277 := by
  unfold tailWord_1700233
  simp only [CollatzResearch.WordTrace]
  refine ⟨62012592049353692523441353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41341728032902461682294235 62012592049353692523441353)
  ·
    refine ⟨46509444037015269392581015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62012592049353692523441353 46509444037015269392581015)
    ·
      refine ⟨69764166055522904088871523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46509444037015269392581015 69764166055522904088871523)
      ·
        refine ⟨104646249083284356133307285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69764166055522904088871523 104646249083284356133307285)
        ·
          refine ⟨4905292925778954193748779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104646249083284356133307285 4905292925778954193748779)
          ·
            refine ⟨7357939388668431290623169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905292925778954193748779 7357939388668431290623169)
            ·
              refine ⟨5518454541501323467967377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7357939388668431290623169 5518454541501323467967377)
              ·
                refine ⟨4138840906125992600975533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5518454541501323467967377 4138840906125992600975533)
                ·
                  refine ⟨1552065339797247225365825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4138840906125992600975533 1552065339797247225365825)
                  ·
                    refine ⟨1164049004847935419024369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1552065339797247225365825 1164049004847935419024369)
                    ·
                      refine ⟨873036753635951564268277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164049004847935419024369 873036753635951564268277)
                      ·
                        rfl

theorem cell23_1700233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 2, 2].length) (baseStart_1700233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700233 prefixEnd_1700233 := by exact prefixLift 1700233
  have htrace : WordTrace (prefixWord ++ tailWord_1700233) baseStart_1700233 baseEnd_1700233 := by
    simpa [prefixWord, tailWord_1700233, baseEnd_1700233] using wordTrace_append hprefix tailTrace_1700233
  have hstable : (prefixWord ++ tailWord_1700233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700233).length < 2 ^ (prefixWord ++ tailWord_1700233).sum := by decide
  have hdescent : baseEnd_1700233 < baseStart_1700233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700236 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 1, 2, 3]
def baseStart_1700236 : Nat := 118140960795 + 1700236 * 2 ^ 59
def prefixEnd_1700236 : Nat := 4983230072969 + 3 ^ 40 * 1700236 * 2
def baseEnd_1700236 : Nat := 873038294077915052530763

theorem tailTrace_1700236 : CollatzResearch.WordTrace tailWord_1700236 prefixEnd_1700236 873038294077915052530763 := by
  unfold tailWord_1700236
  simp only [CollatzResearch.WordTrace]
  refine ⟨31006350734171412017900281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41341800978895216023867041 31006350734171412017900281)
  ·
    refine ⟨23254763050628559013425211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31006350734171412017900281 23254763050628559013425211)
    ·
      refine ⟨34882144575942838520137817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23254763050628559013425211 34882144575942838520137817)
      ·
        refine ⟨26161608431957128890103363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34882144575942838520137817 26161608431957128890103363)
        ·
          refine ⟨39242412647935693335155045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26161608431957128890103363 39242412647935693335155045)
          ·
            refine ⟨7357952371487942500341571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39242412647935693335155045 7357952371487942500341571)
            ·
              refine ⟨11036928557231913750512357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7357952371487942500341571 11036928557231913750512357)
              ·
                refine ⟨2069424104480983828221067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11036928557231913750512357 2069424104480983828221067)
                ·
                  refine ⟨3104136156721475742331601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069424104480983828221067 3104136156721475742331601)
                  ·
                    refine ⟨2328102117541106806748701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3104136156721475742331601 2328102117541106806748701)
                    ·
                      refine ⟨873038294077915052530763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2328102117541106806748701 873038294077915052530763)
                      ·
                        rfl

theorem cell23_1700236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_1700236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700236 prefixEnd_1700236 := by exact prefixLift 1700236
  have htrace : WordTrace (prefixWord ++ tailWord_1700236) baseStart_1700236 baseEnd_1700236 := by
    simpa [prefixWord, tailWord_1700236, baseEnd_1700236] using wordTrace_append hprefix tailTrace_1700236
  have hstable : (prefixWord ++ tailWord_1700236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700236).length < 2 ^ (prefixWord ++ tailWord_1700236).sum := by decide
  have hdescent : baseEnd_1700236 < baseStart_1700236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700244 : List Nat := [2, 4, 2, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_1700244 : Nat := 118140960795 + 1700244 * 2 ^ 59
def prefixEnd_1700244 : Nat := 4983230072969 + 3 ^ 40 * 1700244 * 2
def baseEnd_1700244 : Nat := 873042401923151021230727

theorem tailTrace_1700244 : CollatzResearch.WordTrace tailWord_1700244 prefixEnd_1700244 873042401923151021230727 := by
  unfold tailWord_1700244
  simp only [CollatzResearch.WordTrace]
  refine ⟨31006496626156920701045893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41341995501542560934727857 31006496626156920701045893)
  ·
    refine ⟨5813718117404422631446105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31006496626156920701045893 5813718117404422631446105)
    ·
      refine ⟨4360288588053316973584579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5813718117404422631446105 4360288588053316973584579)
      ·
        refine ⟨6540432882079975460376869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4360288588053316973584579 6540432882079975460376869)
        ·
          refine ⟨1226331165389995398820663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6540432882079975460376869 1226331165389995398820663)
          ·
            refine ⟨1839496748084993098230995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226331165389995398820663 1839496748084993098230995)
            ·
              refine ⟨2759245122127489647346493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839496748084993098230995 2759245122127489647346493)
              ·
                refine ⟨1034716920797808617754935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2759245122127489647346493 1034716920797808617754935)
                ·
                  refine ⟨1552075381196712926632403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034716920797808617754935 1552075381196712926632403)
                  ·
                    refine ⟨2328113071795069389948605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1552075381196712926632403 2328113071795069389948605)
                    ·
                      refine ⟨873042401923151021230727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2328113071795069389948605 873042401923151021230727)
                      ·
                        rfl

theorem cell23_1700244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_1700244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700244 prefixEnd_1700244 := by exact prefixLift 1700244
  have htrace : WordTrace (prefixWord ++ tailWord_1700244) baseStart_1700244 baseEnd_1700244 := by
    simpa [prefixWord, tailWord_1700244, baseEnd_1700244] using wordTrace_append hprefix tailTrace_1700244
  have hstable : (prefixWord ++ tailWord_1700244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700244).length < 2 ^ (prefixWord ++ tailWord_1700244).sum := by decide
  have hdescent : baseEnd_1700244 < baseStart_1700244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700249 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 3, 3, 3]
def baseStart_1700249 : Nat := 118140960795 + 1700249 * 2 ^ 59
def prefixEnd_1700249 : Nat := 4983230072969 + 3 ^ 40 * 1700249 * 2
def baseEnd_1700249 : Nat := 873044969326423501668203

theorem tailTrace_1700249 : CollatzResearch.WordTrace tailWord_1700249 prefixEnd_1700249 873044969326423501668203 := by
  unfold tailWord_1700249
  simp only [CollatzResearch.WordTrace]
  refine ⟨62013175617295727256023801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41342117078197151504015867 62013175617295727256023801)
  ·
    refine ⟨46509881712971795442017851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62013175617295727256023801 46509881712971795442017851)
    ·
      refine ⟨69764822569457693163026777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46509881712971795442017851 69764822569457693163026777)
      ·
        refine ⟨52323616927093269872270083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69764822569457693163026777 52323616927093269872270083)
        ·
          refine ⟨78485425390639904808405125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52323616927093269872270083 78485425390639904808405125)
          ·
            refine ⟨14716017260744982151575961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78485425390639904808405125 14716017260744982151575961)
            ·
              refine ⟨11037012945558736613681971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14716017260744982151575961 11037012945558736613681971)
              ·
                refine ⟨16555519418338104920522957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11037012945558736613681971 16555519418338104920522957)
                ·
                  refine ⟨6208319781876789345196109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16555519418338104920522957 6208319781876789345196109)
                  ·
                    refine ⟨2328119918203796004448541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6208319781876789345196109 2328119918203796004448541)
                    ·
                      refine ⟨873044969326423501668203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2328119918203796004448541 873044969326423501668203)
                      ·
                        rfl

theorem cell23_1700249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_1700249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700249 prefixEnd_1700249 := by exact prefixLift 1700249
  have htrace : WordTrace (prefixWord ++ tailWord_1700249) baseStart_1700249 baseEnd_1700249 := by
    simpa [prefixWord, tailWord_1700249, baseEnd_1700249] using wordTrace_append hprefix tailTrace_1700249
  have hstable : (prefixWord ++ tailWord_1700249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700249).length < 2 ^ (prefixWord ++ tailWord_1700249).sum := by decide
  have hdescent : baseEnd_1700249 < baseStart_1700249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700272 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_1700272 : Nat := 118140960795 + 1700272 * 2 ^ 59
def prefixEnd_1700272 : Nat := 4983230072969 + 3 ^ 40 * 1700272 * 2
def baseEnd_1700272 : Nat := 873056779381476911680597

theorem tailTrace_1700272 : CollatzResearch.WordTrace tailWord_1700272 prefixEnd_1700272 873056779381476911680597 := by
  unfold tailWord_1700272
  simp only [CollatzResearch.WordTrace]
  refine ⟨31007007248106201092055535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41342676330808268122740713 31007007248106201092055535)
  ·
    refine ⟨46510510872159301638083303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31007007248106201092055535 46510510872159301638083303)
    ·
      refine ⟨69765766308238952457124955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46510510872159301638083303 69765766308238952457124955)
      ·
        refine ⟨104648649462358428685687433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69765766308238952457124955 104648649462358428685687433)
        ·
          refine ⟨78486487096768821514265575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104648649462358428685687433 78486487096768821514265575)
          ·
            refine ⟨117729730645153232271398363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78486487096768821514265575 117729730645153232271398363)
            ·
              refine ⟨176594595967729848407097545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117729730645153232271398363 176594595967729848407097545)
              ·
                refine ⟨132445946975797386305323159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176594595967729848407097545 132445946975797386305323159)
                ·
                  refine ⟨198668920463696079457984739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132445946975797386305323159 198668920463696079457984739)
                  ·
                    refine ⟨298003380695544119186977109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198668920463696079457984739 298003380695544119186977109)
                    ·
                      refine ⟨873056779381476911680597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 298003380695544119186977109 873056779381476911680597)
                      ·
                        rfl

theorem cell23_1700272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_1700272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700272 prefixEnd_1700272 := by exact prefixLift 1700272
  have htrace : WordTrace (prefixWord ++ tailWord_1700272) baseStart_1700272 baseEnd_1700272 := by
    simpa [prefixWord, tailWord_1700272, baseEnd_1700272] using wordTrace_append hprefix tailTrace_1700272
  have hstable : (prefixWord ++ tailWord_1700272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700272).length < 2 ^ (prefixWord ++ tailWord_1700272).sum := by decide
  have hdescent : baseEnd_1700272 < baseStart_1700272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700277 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 2, 4]
def baseStart_1700277 : Nat := 118140960795 + 1700277 * 2 ^ 59
def prefixEnd_1700277 : Nat := 4983230072969 + 3 ^ 40 * 1700277 * 2
def baseEnd_1700277 : Nat := 291019782261583130706025

theorem tailTrace_1700277 : CollatzResearch.WordTrace tailWord_1700277 prefixEnd_1700277 291019782261583130706025 := by
  unfold tailWord_1700277
  simp only [CollatzResearch.WordTrace]
  refine ⟨62014196861194288038043085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41342797907462858692028723 62014196861194288038043085)
  ·
    refine ⟨23255323822947858014266157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62014196861194288038043085 23255323822947858014266157)
    ·
      refine ⟨8720746433605446755349809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23255323822947858014266157 8720746433605446755349809)
      ·
        refine ⟨6540559825204085066512357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8720746433605446755349809 6540559825204085066512357)
        ·
          refine ⟨1226354967225765949971067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6540559825204085066512357 1226354967225765949971067)
          ·
            refine ⟨1839532450838648924956601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226354967225765949971067 1839532450838648924956601)
            ·
              refine ⟨1379649338128986693717451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1839532450838648924956601 1379649338128986693717451)
              ·
                refine ⟨2069474007193480040576177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379649338128986693717451 2069474007193480040576177)
                ·
                  refine ⟨1552105505395110030432133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2069474007193480040576177 1552105505395110030432133)
                  ·
                    refine ⟨291019782261583130706025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1552105505395110030432133 291019782261583130706025)
                    ·
                      rfl

theorem cell23_1700277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_1700277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700277 prefixEnd_1700277 := by exact prefixLift 1700277
  have htrace : WordTrace (prefixWord ++ tailWord_1700277) baseStart_1700277 baseEnd_1700277 := by
    simpa [prefixWord, tailWord_1700277, baseEnd_1700277] using wordTrace_append hprefix tailTrace_1700277
  have hstable : (prefixWord ++ tailWord_1700277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700277).length < 2 ^ (prefixWord ++ tailWord_1700277).sum := by decide
  have hdescent : baseEnd_1700277 < baseStart_1700277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700363 : List Nat := [1, 1, 1, 1, 7, 2, 2, 3, 5]
def baseStart_1700363 : Nat := 118140960795 + 1700363 * 2 ^ 59
def prefixEnd_1700363 : Nat := 4983230072969 + 3 ^ 40 * 1700363 * 2
def baseEnd_1700363 : Nat := 97011500680115117293631

theorem tailTrace_1700363 : CollatzResearch.WordTrace tailWord_1700363 prefixEnd_1700363 97011500680115117293631 := by
  unfold tailWord_1700363
  simp only [CollatzResearch.WordTrace]
  refine ⟨62017333538882724725673743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41344889025921816483782495 62017333538882724725673743)
  ·
    refine ⟨93026000308324087088510615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62017333538882724725673743 93026000308324087088510615)
    ·
      refine ⟨139539000462486130632765923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93026000308324087088510615 139539000462486130632765923)
      ·
        refine ⟨209308500693729195949148885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139539000462486130632765923 209308500693729195949148885)
        ·
          refine ⟨4905667985009278030058177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 209308500693729195949148885 4905667985009278030058177)
          ·
            refine ⟨3679250988756958522543633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4905667985009278030058177 3679250988756958522543633)
            ·
              refine ⟨2759438241567718891907725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3679250988756958522543633 2759438241567718891907725)
              ·
                refine ⟨1034789340587894584465397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2759438241567718891907725 1034789340587894584465397)
                ·
                  refine ⟨97011500680115117293631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1034789340587894584465397 97011500680115117293631)
                  ·
                    rfl

theorem cell23_1700363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 5].length) (baseStart_1700363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700363 prefixEnd_1700363 := by exact prefixLift 1700363
  have htrace : WordTrace (prefixWord ++ tailWord_1700363) baseStart_1700363 baseEnd_1700363 := by
    simpa [prefixWord, tailWord_1700363, baseEnd_1700363] using wordTrace_append hprefix tailTrace_1700363
  have hstable : (prefixWord ++ tailWord_1700363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700363).length < 2 ^ (prefixWord ++ tailWord_1700363).sum := by decide
  have hdescent : baseEnd_1700363 < baseStart_1700363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700369 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_1700369 : Nat := 118140960795 + 1700369 * 2 ^ 59
def prefixEnd_1700369 : Nat := 4983230072969 + 3 ^ 40 * 1700369 * 2
def baseEnd_1700369 : Nat := 873106587004963032167651

theorem tailTrace_1700369 : CollatzResearch.WordTrace tailWord_1700369 prefixEnd_1700369 873106587004963032167651 := by
  unfold tailWord_1700369
  simp only [CollatzResearch.WordTrace]
  refine ⟨62017552376860987750392161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41345034917907325166928107 62017552376860987750392161)
  ·
    refine ⟨46513164282645740812794121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62017552376860987750392161 46513164282645740812794121)
    ·
      refine ⟨34884873211984305609595591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46513164282645740812794121 34884873211984305609595591)
      ·
        refine ⟨52327309817976458414393387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34884873211984305609595591 52327309817976458414393387)
        ·
          refine ⟨78490964726964687621590081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52327309817976458414393387 78490964726964687621590081)
          ·
            refine ⟨58868223545223515716192561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78490964726964687621590081 58868223545223515716192561)
            ·
              refine ⟨44151167658917636787144421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58868223545223515716192561 44151167658917636787144421)
              ·
                refine ⟨8278343936047056897589579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44151167658917636787144421 8278343936047056897589579)
                ·
                  refine ⟨12417515904070585346384369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8278343936047056897589579 12417515904070585346384369)
                  ·
                    refine ⟨9313136928052939009788277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12417515904070585346384369 9313136928052939009788277)
                    ·
                      refine ⟨873106587004963032167651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9313136928052939009788277 873106587004963032167651)
                      ·
                        rfl

theorem cell23_1700369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_1700369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700369 prefixEnd_1700369 := by exact prefixLift 1700369
  have htrace : WordTrace (prefixWord ++ tailWord_1700369) baseStart_1700369 baseEnd_1700369 := by
    simpa [prefixWord, tailWord_1700369, baseEnd_1700369] using wordTrace_append hprefix tailTrace_1700369
  have hstable : (prefixWord ++ tailWord_1700369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700369).length < 2 ^ (prefixWord ++ tailWord_1700369).sum := by decide
  have hdescent : baseEnd_1700369 < baseStart_1700369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700391 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1700391 : Nat := 118140960795 + 1700391 * 2 ^ 59
def prefixEnd_1700391 : Nat := 4983230072969 + 3 ^ 40 * 1700391 * 2
def baseEnd_1700391 : Nat := 873117883579361946092551

theorem tailTrace_1700391 : CollatzResearch.WordTrace tailWord_1700391 prefixEnd_1700391 873117883579361946092551 := by
  unfold tailWord_1700391
  simp only [CollatzResearch.WordTrace]
  refine ⟨62018354782781285507693027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41345569855187523671795351 62018354782781285507693027)
  ·
    refine ⟨93027532174171928261539541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62018354782781285507693027 93027532174171928261539541)
    ·
      refine ⟨2180332785332154568629833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 93027532174171928261539541 2180332785332154568629833)
      ·
        refine ⟨1635249588999115926472375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2180332785332154568629833 1635249588999115926472375)
        ·
          refine ⟨2452874383498673889708563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635249588999115926472375 2452874383498673889708563)
          ·
            refine ⟨3679311575248010834562845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452874383498673889708563 3679311575248010834562845)
            ·
              refine ⟨1379741840718004062961067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3679311575248010834562845 1379741840718004062961067)
              ·
                refine ⟨2069612761077006094441601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379741840718004062961067 2069612761077006094441601)
                ·
                  refine ⟨1552209570807754570831201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2069612761077006094441601 1552209570807754570831201)
                  ·
                    refine ⟨1164157178105815928123401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1552209570807754570831201 1164157178105815928123401)
                    ·
                      refine ⟨873117883579361946092551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164157178105815928123401 873117883579361946092551)
                      ·
                        rfl

theorem cell23_1700391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1700391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700391 prefixEnd_1700391 := by exact prefixLift 1700391
  have htrace : WordTrace (prefixWord ++ tailWord_1700391) baseStart_1700391 baseEnd_1700391 := by
    simpa [prefixWord, tailWord_1700391, baseEnd_1700391] using wordTrace_append hprefix tailTrace_1700391
  have hstable : (prefixWord ++ tailWord_1700391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700391).length < 2 ^ (prefixWord ++ tailWord_1700391).sum := by decide
  have hdescent : baseEnd_1700391 < baseStart_1700391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700414 : List Nat := [4, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_1700414 : Nat := 118140960795 + 1700414 * 2 ^ 59
def prefixEnd_1700414 : Nat := 4983230072969 + 3 ^ 40 * 1700414 * 2
def baseEnd_1700414 : Nat := 97014410403823928456105

theorem tailTrace_1700414 : CollatzResearch.WordTrace tailWord_1700414 prefixEnd_1700414 97014410403823928456105 := by
  unfold tailWord_1700414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7752399207712245054472537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41346129107798640290520197 7752399207712245054472537)
  ·
    refine ⟨5814299405784183790854403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7752399207712245054472537 5814299405784183790854403)
    ·
      refine ⟨8721449108676275686281605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5814299405784183790854403 8721449108676275686281605)
      ·
        refine ⟨1635271707876801691177801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8721449108676275686281605 1635271707876801691177801)
        ·
          refine ⟨1226453780907601268383351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1635271707876801691177801 1226453780907601268383351)
          ·
            refine ⟨1839680671361401902575027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226453780907601268383351 1839680671361401902575027)
            ·
              refine ⟨2759521007042102853862541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839680671361401902575027 2759521007042102853862541)
              ·
                refine ⟨1034820377640788570198453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2759521007042102853862541 1034820377640788570198453)
                ·
                  refine ⟨97014410403823928456105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1034820377640788570198453 97014410403823928456105)
                  ·
                    rfl

theorem cell23_1700414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_1700414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700414 prefixEnd_1700414 := by exact prefixLift 1700414
  have htrace : WordTrace (prefixWord ++ tailWord_1700414) baseStart_1700414 baseEnd_1700414 := by
    simpa [prefixWord, tailWord_1700414, baseEnd_1700414] using wordTrace_append hprefix tailTrace_1700414
  have hstable : (prefixWord ++ tailWord_1700414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700414).length < 2 ^ (prefixWord ++ tailWord_1700414).sum := by decide
  have hdescent : baseEnd_1700414 < baseStart_1700414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700416 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 3]
def baseStart_1700416 : Nat := 118140960795 + 1700416 * 2 ^ 59
def prefixEnd_1700416 : Nat := 4983230072969 + 3 ^ 40 * 1700416 * 2
def baseEnd_1700416 : Nat := 873130720595724348279935

theorem tailTrace_1700416 : CollatzResearch.WordTrace tailWord_1700416 prefixEnd_1700416 873130720595724348279935 := by
  unfold tailWord_1700416
  simp only [CollatzResearch.WordTrace]
  refine ⟨31009633303845357388676551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41346177738460476518235401 31009633303845357388676551)
  ·
    refine ⟨46514449955768036083014827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31009633303845357388676551 46514449955768036083014827)
    ·
      refine ⟨69771674933652054124522241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46514449955768036083014827 69771674933652054124522241)
      ·
        refine ⟨52328756200239040593391681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69771674933652054124522241 52328756200239040593391681)
        ·
          refine ⟨39246567150179280445043761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52328756200239040593391681 39246567150179280445043761)
          ·
            refine ⟨29434925362634460333782821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39246567150179280445043761 29434925362634460333782821)
            ·
              refine ⟨5519048505493961312584279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29434925362634460333782821 5519048505493961312584279)
              ·
                refine ⟨8278572758240941968876419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519048505493961312584279 8278572758240941968876419)
                ·
                  refine ⟨12417859137361412953314629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8278572758240941968876419 12417859137361412953314629)
                  ·
                    refine ⟨2328348588255264928746493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12417859137361412953314629 2328348588255264928746493)
                    ·
                      refine ⟨873130720595724348279935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2328348588255264928746493 873130720595724348279935)
                      ·
                        rfl

theorem cell23_1700416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_1700416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700416 prefixEnd_1700416 := by exact prefixLift 1700416
  have htrace : WordTrace (prefixWord ++ tailWord_1700416) baseStart_1700416 baseEnd_1700416 := by
    simpa [prefixWord, tailWord_1700416, baseEnd_1700416] using wordTrace_append hprefix tailTrace_1700416
  have hstable : (prefixWord ++ tailWord_1700416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700416).length < 2 ^ (prefixWord ++ tailWord_1700416).sum := by decide
  have hdescent : baseEnd_1700416 < baseStart_1700416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700433 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 2, 2, 3]
def baseStart_1700433 : Nat := 118140960795 + 1700433 * 2 ^ 59
def prefixEnd_1700433 : Nat := 4983230072969 + 3 ^ 40 * 1700433 * 2
def baseEnd_1700433 : Nat := 873139449766850781767357

theorem tailTrace_1700433 : CollatzResearch.WordTrace tailWord_1700433 prefixEnd_1700433 873139449766850781767357 := by
  unfold tailWord_1700433
  simp only [CollatzResearch.WordTrace]
  refine ⟨62019886648629126680721953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41346591099086084453814635 62019886648629126680721953)
  ·
    refine ⟨46514914986471845010541465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62019886648629126680721953 46514914986471845010541465)
    ·
      refine ⟨34886186239853883757906099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46514914986471845010541465 34886186239853883757906099)
      ·
        refine ⟨52329279359780825636859149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34886186239853883757906099 52329279359780825636859149)
        ·
          refine ⟨19623479759917809613822181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52329279359780825636859149 19623479759917809613822181)
          ·
            refine ⟨3679402454984589302591659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19623479759917809613822181 3679402454984589302591659)
            ·
              refine ⟨5519103682476883953887489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679402454984589302591659 5519103682476883953887489)
              ·
                refine ⟨4139327761857662965415617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5519103682476883953887489 4139327761857662965415617)
                ·
                  refine ⟨3104495821393247224061713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4139327761857662965415617 3104495821393247224061713)
                  ·
                    refine ⟨2328371866044935418046285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3104495821393247224061713 2328371866044935418046285)
                    ·
                      refine ⟨873139449766850781767357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2328371866044935418046285 873139449766850781767357)
                      ·
                        rfl

theorem cell23_1700433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_1700433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700433 prefixEnd_1700433 := by exact prefixLift 1700433
  have htrace : WordTrace (prefixWord ++ tailWord_1700433) baseStart_1700433 baseEnd_1700433 := by
    simpa [prefixWord, tailWord_1700433, baseEnd_1700433] using wordTrace_append hprefix tailTrace_1700433
  have hstable : (prefixWord ++ tailWord_1700433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700433).length < 2 ^ (prefixWord ++ tailWord_1700433).sum := by decide
  have hdescent : baseEnd_1700433 < baseStart_1700433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700436 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 8]
def baseStart_1700436 : Nat := 118140960795 + 1700436 * 2 ^ 59
def prefixEnd_1700436 : Nat := 4983230072969 + 3 ^ 40 * 1700436 * 2
def baseEnd_1700436 : Nat := 97015665578757141114427

theorem tailTrace_1700436 : CollatzResearch.WordTrace tailWord_1700436 prefixEnd_1700436 97015665578757141114427 := by
  unfold tailWord_1700436
  simp only [CollatzResearch.WordTrace]
  refine ⟨31009998033809129096540581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41346664045078838795387441 31009998033809129096540581)
  ·
    refine ⟨5814374631339211705601359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31009998033809129096540581 5814374631339211705601359)
    ·
      refine ⟨8721561947008817558402039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5814374631339211705601359 8721561947008817558402039)
      ·
        refine ⟨13082342920513226337603059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8721561947008817558402039 13082342920513226337603059)
        ·
          refine ⟨19623514380769839506404589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13082342920513226337603059 19623514380769839506404589)
          ·
            refine ⟨7358817892788689814901721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19623514380769839506404589 7358817892788689814901721)
            ·
              refine ⟨5519113419591517361176291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7358817892788689814901721 5519113419591517361176291)
              ·
                refine ⟨8278670129387276041764437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519113419591517361176291 8278670129387276041764437)
                ·
                  refine ⟨97015665578757141114427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8278670129387276041764437 97015665578757141114427)
                  ·
                    rfl

theorem cell23_1700436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_1700436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700436 prefixEnd_1700436 := by exact prefixLift 1700436
  have htrace : WordTrace (prefixWord ++ tailWord_1700436) baseStart_1700436 baseEnd_1700436 := by
    simpa [prefixWord, tailWord_1700436, baseEnd_1700436] using wordTrace_append hprefix tailTrace_1700436
  have hstable : (prefixWord ++ tailWord_1700436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700436).length < 2 ^ (prefixWord ++ tailWord_1700436).sum := by decide
  have hdescent : baseEnd_1700436 < baseStart_1700436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700453 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 6]
def baseStart_1700453 : Nat := 118140960795 + 1700453 * 2 ^ 59
def prefixEnd_1700453 : Nat := 4983230072969 + 3 ^ 40 * 1700453 * 2
def baseEnd_1700453 : Nat := 97016635486660078168585

theorem tailTrace_1700453 : CollatzResearch.WordTrace tailWord_1700453 prefixEnd_1700453 97016635486660078168585 := by
  unfold tailWord_1700453
  simp only [CollatzResearch.WordTrace]
  refine ⟨62020616108556670096450013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41347077405704446730966675 62020616108556670096450013)
  ·
    refine ⟨23257731040708751286168755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62020616108556670096450013 23257731040708751286168755)
    ·
      refine ⟨34886596561063126929253133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23257731040708751286168755 34886596561063126929253133)
      ·
        refine ⟨13082473710398672598469925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34886596561063126929253133 13082473710398672598469925)
        ·
          refine ⟨2452963820699751112213111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13082473710398672598469925 2452963820699751112213111)
          ·
            refine ⟨3679445731049626668319667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452963820699751112213111 3679445731049626668319667)
            ·
              refine ⟨5519168596574440002479501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679445731049626668319667 5519168596574440002479501)
              ·
                refine ⟨2069688223715415000929813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5519168596574440002479501 2069688223715415000929813)
                ·
                  refine ⟨97016635486660078168585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2069688223715415000929813 97016635486660078168585)
                  ·
                    rfl

theorem cell23_1700453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_1700453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700453 prefixEnd_1700453 := by exact prefixLift 1700453
  have htrace : WordTrace (prefixWord ++ tailWord_1700453) baseStart_1700453 baseEnd_1700453 := by
    simpa [prefixWord, tailWord_1700453, baseEnd_1700453] using wordTrace_append hprefix tailTrace_1700453
  have hstable : (prefixWord ++ tailWord_1700453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700453).length < 2 ^ (prefixWord ++ tailWord_1700453).sum := by decide
  have hdescent : baseEnd_1700453 < baseStart_1700453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700459 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 7]
def baseStart_1700459 : Nat := 118140960795 + 1700459 * 2 ^ 59
def prefixEnd_1700459 : Nat := 4983230072969 + 3 ^ 40 * 1700459 * 2
def baseEnd_1700459 : Nat := 873152800263867680042237

theorem tailTrace_1700459 : CollatzResearch.WordTrace tailWord_1700459 prefixEnd_1700459 873152800263867680042237 := by
  unfold tailWord_1700459
  simp only [CollatzResearch.WordTrace]
  refine ⟨62020834946534933121168431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41347223297689955414112287 62020834946534933121168431)
  ·
    refine ⟨93031252419802399681752647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62020834946534933121168431 93031252419802399681752647)
    ·
      refine ⟨139546878629703599522628971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93031252419802399681752647 139546878629703599522628971)
      ·
        refine ⟨209320317944555399283943457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139546878629703599522628971 209320317944555399283943457)
        ·
          refine ⟨156990238458416549462957593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209320317944555399283943457 156990238458416549462957593)
          ·
            refine ⟨117742678843812412097218195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156990238458416549462957593 117742678843812412097218195)
            ·
              refine ⟨176614018265718618145827293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117742678843812412097218195 176614018265718618145827293)
              ·
                refine ⟨66230256849644481804685235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176614018265718618145827293 66230256849644481804685235)
                ·
                  refine ⟨99345385274466722707027853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66230256849644481804685235 99345385274466722707027853)
                  ·
                    refine ⟨37254519477925021015135445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99345385274466722707027853 37254519477925021015135445)
                    ·
                      refine ⟨873152800263867680042237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37254519477925021015135445 873152800263867680042237)
                      ·
                        rfl

theorem cell23_1700459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_1700459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700459 prefixEnd_1700459 := by exact prefixLift 1700459
  have htrace : WordTrace (prefixWord ++ tailWord_1700459) baseStart_1700459 baseEnd_1700459 := by
    simpa [prefixWord, tailWord_1700459, baseEnd_1700459] using wordTrace_append hprefix tailTrace_1700459
  have hstable : (prefixWord ++ tailWord_1700459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700459).length < 2 ^ (prefixWord ++ tailWord_1700459).sum := by decide
  have hdescent : baseEnd_1700459 < baseStart_1700459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700463 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 3, 1, 3]
def baseStart_1700463 : Nat := 118140960795 + 1700463 * 2 ^ 59
def prefixEnd_1700463 : Nat := 4983230072969 + 3 ^ 40 * 1700463 * 2
def baseEnd_1700463 : Nat := 873154854186485664392219

theorem tailTrace_1700463 : CollatzResearch.WordTrace tailWord_1700463 prefixEnd_1700463 873154854186485664392219 := by
  unfold tailWord_1700463
  simp only [CollatzResearch.WordTrace]
  refine ⟨62020980838520441804314043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41347320559013627869542695 62020980838520441804314043)
  ·
    refine ⟨93031471257780662706471065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62020980838520441804314043 93031471257780662706471065)
    ·
      refine ⟨69773603443335497029853299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93031471257780662706471065 69773603443335497029853299)
      ·
        refine ⟨104660405165003245544779949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69773603443335497029853299 104660405165003245544779949)
        ·
          refine ⟨39247651936876217079292481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104660405165003245544779949 39247651936876217079292481)
          ·
            refine ⟨29435738952657162809469361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39247651936876217079292481 29435738952657162809469361)
            ·
              refine ⟨22076804214492872107102021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29435738952657162809469361 22076804214492872107102021)
              ·
                refine ⟨4139400790217413520081629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22076804214492872107102021 4139400790217413520081629)
                ·
                  refine ⟨1552275296331530070030611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4139400790217413520081629 1552275296331530070030611)
                  ·
                    refine ⟨2328412944497295105045917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1552275296331530070030611 2328412944497295105045917)
                    ·
                      refine ⟨873154854186485664392219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2328412944497295105045917 873154854186485664392219)
                      ·
                        rfl

theorem cell23_1700463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 1, 3].length) (baseStart_1700463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700463 prefixEnd_1700463 := by exact prefixLift 1700463
  have htrace : WordTrace (prefixWord ++ tailWord_1700463) baseStart_1700463 baseEnd_1700463 := by
    simpa [prefixWord, tailWord_1700463, baseEnd_1700463] using wordTrace_append hprefix tailTrace_1700463
  have hstable : (prefixWord ++ tailWord_1700463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700463).length < 2 ^ (prefixWord ++ tailWord_1700463).sum := by decide
  have hdescent : baseEnd_1700463 < baseStart_1700463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700540 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_1700540 : Nat := 118140960795 + 1700540 * 2 ^ 59
def prefixEnd_1700540 : Nat := 4983230072969 + 3 ^ 40 * 1700540 * 2
def baseEnd_1700540 : Nat := 873194392196881863129365

theorem tailTrace_1700540 : CollatzResearch.WordTrace tailWord_1700540 prefixEnd_1700540 873194392196881863129365 := by
  unfold tailWord_1700540
  simp only [CollatzResearch.WordTrace]
  refine ⟨31011894629620741977433537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41349192839494322636578049 31011894629620741977433537)
  ·
    refine ⟨23258920972215556483075153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31011894629620741977433537 23258920972215556483075153)
    ·
      refine ⟨17444190729161667362306365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23258920972215556483075153 17444190729161667362306365)
      ·
        refine ⟨6541571523435625260864887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17444190729161667362306365 6541571523435625260864887)
        ·
          refine ⟨9812357285153437891297331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541571523435625260864887 9812357285153437891297331)
          ·
            refine ⟨14718535927730156836945997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9812357285153437891297331 14718535927730156836945997)
            ·
              refine ⟨5519450972898808813854749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14718535927730156836945997 5519450972898808813854749)
              ·
                refine ⟨2069794114837053305195531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5519450972898808813854749 2069794114837053305195531)
                ·
                  refine ⟨3104691172255579957793297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069794114837053305195531 3104691172255579957793297)
                  ·
                    refine ⟨2328518379191684968344973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3104691172255579957793297 2328518379191684968344973)
                    ·
                      refine ⟨873194392196881863129365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2328518379191684968344973 873194392196881863129365)
                      ·
                        rfl

theorem cell23_1700540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_1700540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700540 prefixEnd_1700540 := by exact prefixLift 1700540
  have htrace : WordTrace (prefixWord ++ tailWord_1700540) baseStart_1700540 baseEnd_1700540 := by
    simpa [prefixWord, tailWord_1700540, baseEnd_1700540] using wordTrace_append hprefix tailTrace_1700540
  have hstable : (prefixWord ++ tailWord_1700540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700540).length < 2 ^ (prefixWord ++ tailWord_1700540).sum := by decide
  have hdescent : baseEnd_1700540 < baseStart_1700540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700554 : List Nat := [3, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2]
def baseStart_1700554 : Nat := 118140960795 + 1700554 * 2 ^ 59
def prefixEnd_1700554 : Nat := 4983230072969 + 3 ^ 40 * 1700554 * 2
def baseEnd_1700554 : Nat := 873201580926044808354301

theorem tailTrace_1700554 : CollatzResearch.WordTrace tailWord_1700554 prefixEnd_1700554 873201580926044808354301 := by
  unfold tailWord_1700554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15506074970297691086469179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41349533254127176230584477 15506074970297691086469179)
  ·
    refine ⟨23259112455446536629703769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15506074970297691086469179 23259112455446536629703769)
    ·
      refine ⟨17444334341584902472277827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23259112455446536629703769 17444334341584902472277827)
      ·
        refine ⟨26166501512377353708416741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17444334341584902472277827 26166501512377353708416741)
        ·
          refine ⟨4906219033570753820328139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26166501512377353708416741 4906219033570753820328139)
          ·
            refine ⟨7359328550356130730492209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4906219033570753820328139 7359328550356130730492209)
            ·
              refine ⟨5519496412767098047869157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7359328550356130730492209 5519496412767098047869157)
              ·
                refine ⟨1034905577393830883975467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5519496412767098047869157 1034905577393830883975467)
                ·
                  refine ⟨1552358366090746325963201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034905577393830883975467 1552358366090746325963201)
                  ·
                    refine ⟨1164268774568059744472401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1552358366090746325963201 1164268774568059744472401)
                    ·
                      refine ⟨873201580926044808354301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164268774568059744472401 873201580926044808354301)
                      ·
                        rfl

theorem cell23_1700554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_1700554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700554 prefixEnd_1700554 := by exact prefixLift 1700554
  have htrace : WordTrace (prefixWord ++ tailWord_1700554) baseStart_1700554 baseEnd_1700554 := by
    simpa [prefixWord, tailWord_1700554, baseEnd_1700554] using wordTrace_append hprefix tailTrace_1700554
  have hstable : (prefixWord ++ tailWord_1700554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700554).length < 2 ^ (prefixWord ++ tailWord_1700554).sum := by decide
  have hdescent : baseEnd_1700554 < baseStart_1700554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700557 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1700557 : Nat := 118140960795 + 1700557 * 2 ^ 59
def prefixEnd_1700557 : Nat := 4983230072969 + 3 ^ 40 * 1700557 * 2
def baseEnd_1700557 : Nat := 873203121368008296616787

theorem tailTrace_1700557 : CollatzResearch.WordTrace tailWord_1700557 prefixEnd_1700557 873203121368008296616787 := by
  unfold tailWord_1700557
  simp only [CollatzResearch.WordTrace]
  refine ⟨62024409300179895858235925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41349606200119930572157283 62024409300179895858235925)
  ·
    refine ⟨2907394185945932618354809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62024409300179895858235925 2907394185945932618354809)
    ·
      refine ⟨2180545639459449463766107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2907394185945932618354809 2180545639459449463766107)
      ·
        refine ⟨3270818459189174195649161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2180545639459449463766107 3270818459189174195649161)
        ·
          refine ⟨2453113844391880646736871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3270818459189174195649161 2453113844391880646736871)
          ·
            refine ⟨3679670766587820970105307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453113844391880646736871 3679670766587820970105307)
            ·
              refine ⟨5519506149881731455157961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679670766587820970105307 5519506149881731455157961)
              ·
                refine ⟨4139629612411298591368471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5519506149881731455157961 4139629612411298591368471)
                ·
                  refine ⟨6209444418616947887052707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139629612411298591368471 6209444418616947887052707)
                  ·
                    refine ⟨9314166627925421830579061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6209444418616947887052707 9314166627925421830579061)
                    ·
                      refine ⟨873203121368008296616787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9314166627925421830579061 873203121368008296616787)
                      ·
                        rfl

theorem cell23_1700557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1700557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700557 prefixEnd_1700557 := by exact prefixLift 1700557
  have htrace : WordTrace (prefixWord ++ tailWord_1700557) baseStart_1700557 baseEnd_1700557 := by
    simpa [prefixWord, tailWord_1700557, baseEnd_1700557] using wordTrace_append hprefix tailTrace_1700557
  have hstable : (prefixWord ++ tailWord_1700557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700557).length < 2 ^ (prefixWord ++ tailWord_1700557).sum := by decide
  have hdescent : baseEnd_1700557 < baseStart_1700557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700564 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_1700564 : Nat := 118140960795 + 1700564 * 2 ^ 59
def prefixEnd_1700564 : Nat := 4983230072969 + 3 ^ 40 * 1700564 * 2
def baseEnd_1700564 : Nat := 291068905244196589743085

theorem tailTrace_1700564 : CollatzResearch.WordTrace tailWord_1700564 prefixEnd_1700564 291068905244196589743085 := by
  unfold tailWord_1700564
  simp only [CollatzResearch.WordTrace]
  refine ⟨31012332305577268026870373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41349776407436357369160497 31012332305577268026870373)
  ·
    refine ⟨5814812307295737755038195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31012332305577268026870373 5814812307295737755038195)
    ·
      refine ⟨8722218460943606632557293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5814812307295737755038195 8722218460943606632557293)
      ·
        refine ⟨3270831922853852487208985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8722218460943606632557293 3270831922853852487208985)
        ·
          refine ⟨2453123942140389365406739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3270831922853852487208985 2453123942140389365406739)
          ·
            refine ⟨3679685913210584048110109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453123942140389365406739 3679685913210584048110109)
            ·
              refine ⟨1379882217453969018041291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3679685913210584048110109 1379882217453969018041291)
              ·
                refine ⟨2069823326180953527061937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379882217453969018041291 2069823326180953527061937)
                ·
                  refine ⟨1552367494635715145296453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2069823326180953527061937 1552367494635715145296453)
                  ·
                    refine ⟨291068905244196589743085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1552367494635715145296453 291068905244196589743085)
                    ·
                      rfl

theorem cell23_1700564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_1700564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700564 prefixEnd_1700564 := by exact prefixLift 1700564
  have htrace : WordTrace (prefixWord ++ tailWord_1700564) baseStart_1700564 baseEnd_1700564 := by
    simpa [prefixWord, tailWord_1700564, baseEnd_1700564] using wordTrace_append hprefix tailTrace_1700564
  have hstable : (prefixWord ++ tailWord_1700564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700564).length < 2 ^ (prefixWord ++ tailWord_1700564).sum := by decide
  have hdescent : baseEnd_1700564 < baseStart_1700564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700627 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 2, 2, 2]
def baseStart_1700627 : Nat := 118140960795 + 1700627 * 2 ^ 59
def prefixEnd_1700627 : Nat := 4983230072969 + 3 ^ 40 * 1700627 * 2
def baseEnd_1700627 : Nat := 873239065013823022741465

theorem tailTrace_1700627 : CollatzResearch.WordTrace tailWord_1700627 prefixEnd_1700627 873239065013823022741465 := by
  unfold tailWord_1700627
  simp only [CollatzResearch.WordTrace]
  refine ⟨62026962409926297813284135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41351308273284198542189423 62026962409926297813284135)
  ·
    refine ⟨93040443614889446719926203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62026962409926297813284135 93040443614889446719926203)
    ·
      refine ⟨139560665422334170079889305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93040443614889446719926203 139560665422334170079889305)
      ·
        refine ⟨104670499066750627559916979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139560665422334170079889305 104670499066750627559916979)
        ·
          refine ⟨157005748600125941339875469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104670499066750627559916979 157005748600125941339875469)
          ·
            refine ⟨58877155725047228002453301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157005748600125941339875469 58877155725047228002453301)
            ·
              refine ⟨5519733349223177625229997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58877155725047228002453301 5519733349223177625229997)
              ·
                refine ⟨2069900005958691609461249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5519733349223177625229997 2069900005958691609461249)
                ·
                  refine ⟨1552425004469018707095937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2069900005958691609461249 1552425004469018707095937)
                  ·
                    refine ⟨1164318753351764030321953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1552425004469018707095937 1164318753351764030321953)
                    ·
                      refine ⟨873239065013823022741465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164318753351764030321953 873239065013823022741465)
                      ·
                        rfl

theorem cell23_1700627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 2, 2].length) (baseStart_1700627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700627 prefixEnd_1700627 := by exact prefixLift 1700627
  have htrace : WordTrace (prefixWord ++ tailWord_1700627) baseStart_1700627 baseEnd_1700627 := by
    simpa [prefixWord, tailWord_1700627, baseEnd_1700627] using wordTrace_append hprefix tailTrace_1700627
  have hstable : (prefixWord ++ tailWord_1700627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700627).length < 2 ^ (prefixWord ++ tailWord_1700627).sum := by decide
  have hdescent : baseEnd_1700627 < baseStart_1700627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700631 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 1, 3, 2]
def baseStart_1700631 : Nat := 118140960795 + 1700631 * 2 ^ 59
def prefixEnd_1700631 : Nat := 4983230072969 + 3 ^ 40 * 1700631 * 2
def baseEnd_1700631 : Nat := 873241118936441007091447

theorem tailTrace_1700631 : CollatzResearch.WordTrace tailWord_1700631 prefixEnd_1700631 873241118936441007091447 := by
  unfold tailWord_1700631
  simp only [CollatzResearch.WordTrace]
  refine ⟨62027108301911806496429747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41351405534607870997619831 62027108301911806496429747)
  ·
    refine ⟨93040662452867709744644621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62027108301911806496429747 93040662452867709744644621)
    ·
      refine ⟨34890248419825391154241733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93040662452867709744644621 34890248419825391154241733)
      ·
        refine ⟨6541921578717260841420325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34890248419825391154241733 6541921578717260841420325)
        ·
          refine ⟨1226610296009486407766311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6541921578717260841420325 1226610296009486407766311)
          ·
            refine ⟨1839915444014229611649467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226610296009486407766311 1839915444014229611649467)
            ·
              refine ⟨2759873166021344417474201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839915444014229611649467 2759873166021344417474201)
              ·
                refine ⟨2069904874516008313105651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759873166021344417474201 2069904874516008313105651)
                ·
                  refine ⟨3104857311774012469658477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069904874516008313105651 3104857311774012469658477)
                  ·
                    refine ⟨1164321491915254676121929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3104857311774012469658477 1164321491915254676121929)
                    ·
                      refine ⟨873241118936441007091447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164321491915254676121929 873241118936441007091447)
                      ·
                        rfl

theorem cell23_1700631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_1700631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700631 prefixEnd_1700631 := by exact prefixLift 1700631
  have htrace : WordTrace (prefixWord ++ tailWord_1700631) baseStart_1700631 baseEnd_1700631 := by
    simpa [prefixWord, tailWord_1700631, baseEnd_1700631] using wordTrace_append hprefix tailTrace_1700631
  have hstable : (prefixWord ++ tailWord_1700631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700631).length < 2 ^ (prefixWord ++ tailWord_1700631).sum := by decide
  have hdescent : baseEnd_1700631 < baseStart_1700631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700643 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1700643 : Nat := 118140960795 + 1700643 * 2 ^ 59
def prefixEnd_1700643 : Nat := 4983230072969 + 3 ^ 40 * 1700643 * 2
def baseEnd_1700643 : Nat := 873247280704294960141391

theorem tailTrace_1700643 : CollatzResearch.WordTrace tailWord_1700643 prefixEnd_1700643 873247280704294960141391 := by
  unfold tailWord_1700643
  simp only [CollatzResearch.WordTrace]
  refine ⟨62027545977868332545866583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41351697318578888363911055 62027545977868332545866583)
  ·
    refine ⟨93041318966802498818799875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62027545977868332545866583 93041318966802498818799875)
    ·
      refine ⟨139561978450203748228199813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93041318966802498818799875 139561978450203748228199813)
      ·
        refine ⟨26167870959413202792787465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139561978450203748228199813 26167870959413202792787465)
        ·
          refine ⟨19625903219559902094590599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26167870959413202792787465 19625903219559902094590599)
          ·
            refine ⟨29438854829339853141885899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19625903219559902094590599 29438854829339853141885899)
            ·
              refine ⟨44158282244009779712828849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29438854829339853141885899 44158282244009779712828849)
              ·
                refine ⟨33118711683007334784621637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44158282244009779712828849 33118711683007334784621637)
                ·
                  refine ⟨6209758440563875272116557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33118711683007334784621637 6209758440563875272116557)
                  ·
                    refine ⟨2328659415211453227043709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6209758440563875272116557 2328659415211453227043709)
                    ·
                      refine ⟨873247280704294960141391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2328659415211453227043709 873247280704294960141391)
                      ·
                        rfl

theorem cell23_1700643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1700643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700643 prefixEnd_1700643 := by exact prefixLift 1700643
  have htrace : WordTrace (prefixWord ++ tailWord_1700643) baseStart_1700643 baseEnd_1700643 := by
    simpa [prefixWord, tailWord_1700643, baseEnd_1700643] using wordTrace_append hprefix tailTrace_1700643
  have hstable : (prefixWord ++ tailWord_1700643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700643).length < 2 ^ (prefixWord ++ tailWord_1700643).sum := by decide
  have hdescent : baseEnd_1700643 < baseStart_1700643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700663 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 2, 5]
def baseStart_1700663 : Nat := 118140960795 + 1700663 * 2 ^ 59
def prefixEnd_1700663 : Nat := 4983230072969 + 3 ^ 40 * 1700663 * 2
def baseEnd_1700663 : Nat := 291085850105794960630433

theorem tailTrace_1700663 : CollatzResearch.WordTrace tailWord_1700663 prefixEnd_1700663 291085850105794960630433 := by
  unfold tailWord_1700663
  simp only [CollatzResearch.WordTrace]
  refine ⟨62028275437795875961594643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41352183625197250641063095 62028275437795875961594643)
  ·
    refine ⟨93042413156693813942391965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62028275437795875961594643 93042413156693813942391965)
    ·
      refine ⟨34890904933760180228396987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93042413156693813942391965 34890904933760180228396987)
      ·
        refine ⟨52336357400640270342595481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34890904933760180228396987 52336357400640270342595481)
        ·
          refine ⟨39252268050480202756946611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52336357400640270342595481 39252268050480202756946611)
          ·
            refine ⟨58878402075720304135419917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39252268050480202756946611 58878402075720304135419917)
            ·
              refine ⟨22079400778395114050782469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58878402075720304135419917 22079400778395114050782469)
              ·
                refine ⟨4139887645949083884521713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22079400778395114050782469 4139887645949083884521713)
                ·
                  refine ⟨3104915734461812913391285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4139887645949083884521713 3104915734461812913391285)
                  ·
                    refine ⟨291085850105794960630433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3104915734461812913391285 291085850105794960630433)
                    ·
                      rfl

theorem cell23_1700663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_1700663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700663 prefixEnd_1700663 := by exact prefixLift 1700663
  have htrace : WordTrace (prefixWord ++ tailWord_1700663) baseStart_1700663 baseEnd_1700663 := by
    simpa [prefixWord, tailWord_1700663, baseEnd_1700663] using wordTrace_append hprefix tailTrace_1700663
  have hstable : (prefixWord ++ tailWord_1700663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700663).length < 2 ^ (prefixWord ++ tailWord_1700663).sum := by decide
  have hdescent : baseEnd_1700663 < baseStart_1700663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700720 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 3]
def baseStart_1700720 : Nat := 118140960795 + 1700720 * 2 ^ 59
def prefixEnd_1700720 : Nat := 4983230072969 + 3 ^ 40 * 1700720 * 2
def baseEnd_1700720 : Nat := 873286818714691158878537

theorem tailTrace_1700720 : CollatzResearch.WordTrace tailWord_1700720 prefixEnd_1700720 873286818714691158878537 := by
  unfold tailWord_1700720
  simp only [CollatzResearch.WordTrace]
  refine ⟨31015177199294687348209807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41353569599059583130946409 31015177199294687348209807)
  ·
    refine ⟨46522765798942031022314711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31015177199294687348209807 46522765798942031022314711)
    ·
      refine ⟨69784148698413046533472067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46522765798942031022314711 69784148698413046533472067)
      ·
        refine ⟨104676223047619569800208101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69784148698413046533472067 104676223047619569800208101)
        ·
          refine ⟨19626791821428669337539019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104676223047619569800208101 19626791821428669337539019)
          ·
            refine ⟨29440187732143004006308529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19626791821428669337539019 29440187732143004006308529)
            ·
              refine ⟨22080140799107253004731397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29440187732143004006308529 22080140799107253004731397)
              ·
                refine ⟨4140026399832609938387137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22080140799107253004731397 4140026399832609938387137)
                ·
                  refine ⟨3105019799874457453790353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4140026399832609938387137 3105019799874457453790353)
                  ·
                    refine ⟨2328764849905843090342765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3105019799874457453790353 2328764849905843090342765)
                    ·
                      refine ⟨873286818714691158878537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2328764849905843090342765 873286818714691158878537)
                      ·
                        rfl

theorem cell23_1700720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 3].length) (baseStart_1700720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700720 prefixEnd_1700720 := by exact prefixLift 1700720
  have htrace : WordTrace (prefixWord ++ tailWord_1700720) baseStart_1700720 baseEnd_1700720 := by
    simpa [prefixWord, tailWord_1700720, baseEnd_1700720] using wordTrace_append hprefix tailTrace_1700720
  have hstable : (prefixWord ++ tailWord_1700720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700720).length < 2 ^ (prefixWord ++ tailWord_1700720).sum := by decide
  have hdescent : baseEnd_1700720 < baseStart_1700720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700777 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 2, 3, 2]
def baseStart_1700777 : Nat := 118140960795 + 1700777 * 2 ^ 59
def prefixEnd_1700777 : Nat := 4983230072969 + 3 ^ 40 * 1700777 * 2
def baseEnd_1700777 : Nat := 873316087111997435865775

theorem tailTrace_1700777 : CollatzResearch.WordTrace tailWord_1700777 prefixEnd_1700777 873316087111997435865775 := by
  unfold tailWord_1700777
  simp only [CollatzResearch.WordTrace]
  refine ⟨62032433359382873431244585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41354955572921915620829723 62032433359382873431244585)
  ·
    refine ⟨46524325019537155073433439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62032433359382873431244585 46524325019537155073433439)
    ·
      refine ⟨69786487529305732610150159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46524325019537155073433439 69786487529305732610150159)
      ·
        refine ⟨104679731293958598915225239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69786487529305732610150159 104679731293958598915225239)
        ·
          refine ⟨157019596940937898372837859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104679731293958598915225239 157019596940937898372837859)
          ·
            refine ⟨235529395411406847559256789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157019596940937898372837859 235529395411406847559256789)
            ·
              refine ⟨5520220204954847989670081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 235529395411406847559256789 5520220204954847989670081)
              ·
                refine ⟨4140165153716135992252561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5520220204954847989670081 4140165153716135992252561)
                ·
                  refine ⟨3105123865287101994189421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4140165153716135992252561 3105123865287101994189421)
                  ·
                    refine ⟨1164421449482663247821033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3105123865287101994189421 1164421449482663247821033)
                    ·
                      refine ⟨873316087111997435865775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164421449482663247821033 873316087111997435865775)
                      ·
                        rfl

theorem cell23_1700777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 3, 2].length) (baseStart_1700777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700777 prefixEnd_1700777 := by exact prefixLift 1700777
  have htrace : WordTrace (prefixWord ++ tailWord_1700777) baseStart_1700777 baseEnd_1700777 := by
    simpa [prefixWord, tailWord_1700777, baseEnd_1700777] using wordTrace_append hprefix tailTrace_1700777
  have hstable : (prefixWord ++ tailWord_1700777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700777).length < 2 ^ (prefixWord ++ tailWord_1700777).sum := by decide
  have hdescent : baseEnd_1700777 < baseStart_1700777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700783 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 5, 6]
def baseStart_1700783 : Nat := 118140960795 + 1700783 * 2 ^ 59
def prefixEnd_1700783 : Nat := 4983230072969 + 3 ^ 40 * 1700783 * 2
def baseEnd_1700783 : Nat := 291106389331974804130249

theorem tailTrace_1700783 : CollatzResearch.WordTrace tailWord_1700783 prefixEnd_1700783 291106389331974804130249 := by
  unfold tailWord_1700783
  simp only [CollatzResearch.WordTrace]
  refine ⟨62032652197361136455963003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41355101464907424303975335 62032652197361136455963003)
  ·
    refine ⟨93048978296041704683944505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62032652197361136455963003 93048978296041704683944505)
    ·
      refine ⟨69786733722031278512958379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93048978296041704683944505 69786733722031278512958379)
      ·
        refine ⟨104680100583046917769437569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69786733722031278512958379 104680100583046917769437569)
        ·
          refine ⟨78510075437285188327078177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104680100583046917769437569 78510075437285188327078177)
          ·
            refine ⟨58882556577963891245308633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78510075437285188327078177 58882556577963891245308633)
            ·
              refine ⟨44161917433472918433981475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58882556577963891245308633 44161917433472918433981475)
              ·
                refine ⟨66242876150209377650972213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44161917433472918433981475 66242876150209377650972213)
                ·
                  refine ⟨6210269639082129154778645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66242876150209377650972213 6210269639082129154778645)
                  ·
                    refine ⟨291106389331974804130249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6210269639082129154778645 291106389331974804130249)
                    ·
                      rfl

theorem cell23_1700783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_1700783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700783 prefixEnd_1700783 := by exact prefixLift 1700783
  have htrace : WordTrace (prefixWord ++ tailWord_1700783) baseStart_1700783 baseEnd_1700783 := by
    simpa [prefixWord, tailWord_1700783, baseEnd_1700783] using wordTrace_append hprefix tailTrace_1700783
  have hstable : (prefixWord ++ tailWord_1700783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700783).length < 2 ^ (prefixWord ++ tailWord_1700783).sum := by decide
  have hdescent : baseEnd_1700783 < baseStart_1700783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700804 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1700804 : Nat := 118140960795 + 1700804 * 2 ^ 59
def prefixEnd_1700804 : Nat := 4983230072969 + 3 ^ 40 * 1700804 * 2
def baseEnd_1700804 : Nat := 291109983696556276742717

theorem tailTrace_1700804 : CollatzResearch.WordTrace tailWord_1700804 prefixEnd_1700804 291109983696556276742717 := by
  unfold tailWord_1700804
  simp only [CollatzResearch.WordTrace]
  refine ⟨31016709065142528521238733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41355612086856704694984977 31016709065142528521238733)
  ·
    refine ⟨11631265899428448195464525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31016709065142528521238733 11631265899428448195464525)
    ·
      refine ⟨4361724712285668073299197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11631265899428448195464525 4361724712285668073299197)
      ·
        refine ⟨1635646767107125527487199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4361724712285668073299197 1635646767107125527487199)
        ·
          refine ⟨2453470150660688291230799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635646767107125527487199 2453470150660688291230799)
          ·
            refine ⟨3680205225991032436846199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453470150660688291230799 3680205225991032436846199)
            ·
              refine ⟨5520307838986548655269299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3680205225991032436846199 5520307838986548655269299)
              ·
                refine ⟨8280461758479822982903949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5520307838986548655269299 8280461758479822982903949)
                ·
                  refine ⟨3105173159429933618588981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8280461758479822982903949 3105173159429933618588981)
                  ·
                    refine ⟨291109983696556276742717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3105173159429933618588981 291109983696556276742717)
                    ·
                      rfl

theorem cell23_1700804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1700804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700804 prefixEnd_1700804 := by exact prefixLift 1700804
  have htrace : WordTrace (prefixWord ++ tailWord_1700804) baseStart_1700804 baseEnd_1700804 := by
    simpa [prefixWord, tailWord_1700804, baseEnd_1700804] using wordTrace_append hprefix tailTrace_1700804
  have hstable : (prefixWord ++ tailWord_1700804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700804).length < 2 ^ (prefixWord ++ tailWord_1700804).sum := by decide
  have hdescent : baseEnd_1700804 < baseStart_1700804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700807 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_1700807 : Nat := 118140960795 + 1700807 * 2 ^ 59
def prefixEnd_1700807 : Nat := 4983230072969 + 3 ^ 40 * 1700807 * 2
def baseEnd_1700807 : Nat := 873331491531632318490637

theorem tailTrace_1700807 : CollatzResearch.WordTrace tailWord_1700807 prefixEnd_1700807 873331491531632318490637 := by
  unfold tailWord_1700807
  simp only [CollatzResearch.WordTrace]
  refine ⟨62033527549274188554836675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41355685032849459036557783 62033527549274188554836675)
  ·
    refine ⟨93050291323911282832255013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62033527549274188554836675 93050291323911282832255013)
    ·
      refine ⟨17446929623233365531047815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93050291323911282832255013 17446929623233365531047815)
      ·
        refine ⟨26170394434850048296571723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17446929623233365531047815 26170394434850048296571723)
        ·
          refine ⟨39255591652275072444857585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26170394434850048296571723 39255591652275072444857585)
          ·
            refine ⟨29441693739206304333643189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39255591652275072444857585 29441693739206304333643189)
            ·
              refine ⟨2760158788050591031279049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29441693739206304333643189 2760158788050591031279049)
              ·
                refine ⟨2070119091037943273459287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2760158788050591031279049 2070119091037943273459287)
                ·
                  refine ⟨3105178636556914910188931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070119091037943273459287 3105178636556914910188931)
                  ·
                    refine ⟨4657767954835372365283397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3105178636556914910188931 4657767954835372365283397)
                    ·
                      refine ⟨873331491531632318490637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4657767954835372365283397 873331491531632318490637)
                      ·
                        rfl

theorem cell23_1700807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_1700807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700807 prefixEnd_1700807 := by exact prefixLift 1700807
  have htrace : WordTrace (prefixWord ++ tailWord_1700807) baseStart_1700807 baseEnd_1700807 := by
    simpa [prefixWord, tailWord_1700807, baseEnd_1700807] using wordTrace_append hprefix tailTrace_1700807
  have hstable : (prefixWord ++ tailWord_1700807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700807).length < 2 ^ (prefixWord ++ tailWord_1700807).sum := by decide
  have hdescent : baseEnd_1700807 < baseStart_1700807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700824 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 1, 1, 4]
def baseStart_1700824 : Nat := 118140960795 + 1700824 * 2 ^ 59
def prefixEnd_1700824 : Nat := 4983230072969 + 3 ^ 40 * 1700824 * 2
def baseEnd_1700824 : Nat := 873340220702758751978059

theorem tailTrace_1700824 : CollatzResearch.WordTrace tailWord_1700824 prefixEnd_1700824 873340220702758751978059 := by
  unfold tailWord_1700824
  simp only [CollatzResearch.WordTrace]
  refine ⟨31017073795106300229102763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41356098393475066972137017 31017073795106300229102763)
  ·
    refine ⟨46525610692659450343654145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31017073795106300229102763 46525610692659450343654145)
    ·
      refine ⟨34894208019494587757740609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46525610692659450343654145 34894208019494587757740609)
      ·
        refine ⟨26170656014620940818305457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34894208019494587757740609 26170656014620940818305457)
        ·
          refine ⟨19627992010965705613729093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26170656014620940818305457 19627992010965705613729093)
          ·
            refine ⟨3680248502056069802574205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19627992010965705613729093 3680248502056069802574205)
            ·
              refine ⟨1380093188271026175965327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3680248502056069802574205 1380093188271026175965327)
              ·
                refine ⟨2070139782406539263947991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380093188271026175965327 2070139782406539263947991)
                ·
                  refine ⟨3105209673609808895921987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070139782406539263947991 3105209673609808895921987)
                  ·
                    refine ⟨4657814510414713343882981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3105209673609808895921987 4657814510414713343882981)
                    ·
                      refine ⟨873340220702758751978059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4657814510414713343882981 873340220702758751978059)
                      ·
                        rfl

theorem cell23_1700824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_1700824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700824 prefixEnd_1700824 := by exact prefixLift 1700824
  have htrace : WordTrace (prefixWord ++ tailWord_1700824) baseStart_1700824 baseEnd_1700824 := by
    simpa [prefixWord, tailWord_1700824, baseEnd_1700824] using wordTrace_append hprefix tailTrace_1700824
  have hstable : (prefixWord ++ tailWord_1700824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700824).length < 2 ^ (prefixWord ++ tailWord_1700824).sum := by decide
  have hdescent : baseEnd_1700824 < baseStart_1700824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700854 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1700854 : Nat := 118140960795 + 1700854 * 2 ^ 59
def prefixEnd_1700854 : Nat := 4983230072969 + 3 ^ 40 * 1700854 * 2
def baseEnd_1700854 : Nat := 873355625122393634602921

theorem tailTrace_1700854 : CollatzResearch.WordTrace tailWord_1700854 prefixEnd_1700854 873355625122393634602921 := by
  unfold tailWord_1700854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3877202611256494723862351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41356827853402610387865077 3877202611256494723862351)
  ·
    refine ⟨5815803916884742085793527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3877202611256494723862351 5815803916884742085793527)
    ·
      refine ⟨8723705875327113128690291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5815803916884742085793527 8723705875327113128690291)
      ·
        refine ⟨13085558812990669693035437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8723705875327113128690291 13085558812990669693035437)
        ·
          refine ⟨4907084554871501134888289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13085558812990669693035437 4907084554871501134888289)
          ·
            refine ⟨3680313416153625851166217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4907084554871501134888289 3680313416153625851166217)
            ·
              refine ⟨2760235062115219388374663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680313416153625851166217 2760235062115219388374663)
              ·
                refine ⟨4140352593172829082561995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760235062115219388374663 4140352593172829082561995)
                ·
                  refine ⟨6210528889759243623842993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140352593172829082561995 6210528889759243623842993)
                  ·
                    refine ⟨4657896667319432717882245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6210528889759243623842993 4657896667319432717882245)
                    ·
                      refine ⟨873355625122393634602921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4657896667319432717882245 873355625122393634602921)
                      ·
                        rfl

theorem cell23_1700854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1700854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700854 prefixEnd_1700854 := by exact prefixLift 1700854
  have htrace : WordTrace (prefixWord ++ tailWord_1700854) baseStart_1700854 baseEnd_1700854 := by
    simpa [prefixWord, tailWord_1700854, baseEnd_1700854] using wordTrace_append hprefix tailTrace_1700854
  have hstable : (prefixWord ++ tailWord_1700854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700854).length < 2 ^ (prefixWord ++ tailWord_1700854).sum := by decide
  have hdescent : baseEnd_1700854 < baseStart_1700854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700857 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 1, 3, 3]
def baseStart_1700857 : Nat := 118140960795 + 1700857 * 2 ^ 59
def prefixEnd_1700857 : Nat := 4983230072969 + 3 ^ 40 * 1700857 * 2
def baseEnd_1700857 : Nat := 873357165564357122865407

theorem tailTrace_1700857 : CollatzResearch.WordTrace tailWord_1700857 prefixEnd_1700857 873357165564357122865407 := by
  unfold tailWord_1700857
  simp only [CollatzResearch.WordTrace]
  refine ⟨62035351199093047094156825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41356900799395364729437883 62035351199093047094156825)
  ·
    refine ⟨46526513399319785320617619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62035351199093047094156825 46526513399319785320617619)
    ·
      refine ⟨69789770098979677980926429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46526513399319785320617619 69789770098979677980926429)
      ·
        refine ⟨26171163787117379242847411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69789770098979677980926429 26171163787117379242847411)
        ·
          refine ⟨39256745680676068864271117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26171163787117379242847411 39256745680676068864271117)
          ·
            refine ⟨14721279630253525824101669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39256745680676068864271117 14721279630253525824101669)
            ·
              refine ⟨2760239930672536092019063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14721279630253525824101669 2760239930672536092019063)
              ·
                refine ⟨4140359896008804138028595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760239930672536092019063 4140359896008804138028595)
                ·
                  refine ⟨6210539844013206207042893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140359896008804138028595 6210539844013206207042893)
                  ·
                    refine ⟨2328952441504952327641085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6210539844013206207042893 2328952441504952327641085)
                    ·
                      refine ⟨873357165564357122865407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2328952441504952327641085 873357165564357122865407)
                      ·
                        rfl

theorem cell23_1700857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_1700857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700857 prefixEnd_1700857 := by exact prefixLift 1700857
  have htrace : WordTrace (prefixWord ++ tailWord_1700857) baseStart_1700857 baseEnd_1700857 := by
    simpa [prefixWord, tailWord_1700857, baseEnd_1700857] using wordTrace_append hprefix tailTrace_1700857
  have hstable : (prefixWord ++ tailWord_1700857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700857).length < 2 ^ (prefixWord ++ tailWord_1700857).sum := by decide
  have hdescent : baseEnd_1700857 < baseStart_1700857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700890 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_1700890 : Nat := 118140960795 + 1700890 * 2 ^ 59
def prefixEnd_1700890 : Nat := 4983230072969 + 3 ^ 40 * 1700890 * 2
def baseEnd_1700890 : Nat := 291124703475318497917585

theorem tailTrace_1700890 : CollatzResearch.WordTrace tailWord_1700890 prefixEnd_1700890 291124703475318497917585 := by
  unfold tailWord_1700890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15509138701993373432527031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41357703205315662486738749 15509138701993373432527031)
  ·
    refine ⟨23263708052990060148790547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15509138701993373432527031 23263708052990060148790547)
    ·
      refine ⟨34895562079485090223185821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23263708052990060148790547 34895562079485090223185821)
      ·
        refine ⟨13085835779806908833694683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34895562079485090223185821 13085835779806908833694683)
        ·
          refine ⟨19628753669710363250542025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13085835779806908833694683 19628753669710363250542025)
          ·
            refine ⟨14721565252282772437906519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19628753669710363250542025 14721565252282772437906519)
            ·
              refine ⟨22082347878424158656859779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14721565252282772437906519 22082347878424158656859779)
              ·
                refine ⟨33123521817636237985289669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22082347878424158656859779 33123521817636237985289669)
                ·
                  refine ⟨6210660340806794622241813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33123521817636237985289669 6210660340806794622241813)
                  ·
                    refine ⟨291124703475318497917585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6210660340806794622241813 291124703475318497917585)
                    ·
                      rfl

theorem cell23_1700890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_1700890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700890 prefixEnd_1700890 := by exact prefixLift 1700890
  have htrace : WordTrace (prefixWord ++ tailWord_1700890) baseStart_1700890 baseEnd_1700890 := by
    simpa [prefixWord, tailWord_1700890, baseEnd_1700890] using wordTrace_append hprefix tailTrace_1700890
  have hstable : (prefixWord ++ tailWord_1700890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700890).length < 2 ^ (prefixWord ++ tailWord_1700890).sum := by decide
  have hdescent : baseEnd_1700890 < baseStart_1700890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700918 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_1700918 : Nat := 118140960795 + 1700918 * 2 ^ 59
def prefixEnd_1700918 : Nat := 4983230072969 + 3 ^ 40 * 1700918 * 2
def baseEnd_1700918 : Nat := 873388487884281384202627

theorem tailTrace_1700918 : CollatzResearch.WordTrace tailWord_1700918 prefixEnd_1700918 873388487884281384202627 := by
  unfold tailWord_1700918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3877348503242003407007963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41358384034581369674751605 3877348503242003407007963)
  ·
    refine ⟨5816022754863005110511945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3877348503242003407007963 5816022754863005110511945)
    ·
      refine ⟨4362017066147253832883959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5816022754863005110511945 4362017066147253832883959)
      ·
        refine ⟨6543025599220880749325939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4362017066147253832883959 6543025599220880749325939)
        ·
          refine ⟨9814538398831321123988909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543025599220880749325939 9814538398831321123988909)
          ·
            refine ⟨3680451899561745421495841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9814538398831321123988909 3680451899561745421495841)
            ·
              refine ⟨2760338924671309066121881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680451899561745421495841 2760338924671309066121881)
              ·
                refine ⟨2070254193503481799591411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2760338924671309066121881 2070254193503481799591411)
                ·
                  refine ⟨3105381290255222699387117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070254193503481799591411 3105381290255222699387117)
                  ·
                    refine ⟨1164517983845708512270169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3105381290255222699387117 1164517983845708512270169)
                    ·
                      refine ⟨873388487884281384202627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164517983845708512270169 873388487884281384202627)
                      ·
                        rfl

theorem cell23_1700918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_1700918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700918 prefixEnd_1700918 := by exact prefixLift 1700918
  have htrace : WordTrace (prefixWord ++ tailWord_1700918) baseStart_1700918 baseEnd_1700918 := by
    simpa [prefixWord, tailWord_1700918, baseEnd_1700918] using wordTrace_append hprefix tailTrace_1700918
  have hstable : (prefixWord ++ tailWord_1700918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700918).length < 2 ^ (prefixWord ++ tailWord_1700918).sum := by decide
  have hdescent : baseEnd_1700918 < baseStart_1700918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700934 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1700934 : Nat := 118140960795 + 1700934 * 2 ^ 59
def prefixEnd_1700934 : Nat := 4983230072969 + 3 ^ 40 * 1700934 * 2
def baseEnd_1700934 : Nat := 873396703574753321602553

theorem tailTrace_1700934 : CollatzResearch.WordTrace tailWord_1700934 prefixEnd_1700934 873396703574753321602553 := by
  unfold tailWord_1700934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1938692488119190288897183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41358773079876059496473237 1938692488119190288897183)
  ·
    refine ⟨2908038732178785433345775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1938692488119190288897183 2908038732178785433345775)
    ·
      refine ⟨4362058098268178150018663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2908038732178785433345775 4362058098268178150018663)
      ·
        refine ⟨6543087147402267225027995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4362058098268178150018663 6543087147402267225027995)
        ·
          refine ⟨9814630721103400837541993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543087147402267225027995 9814630721103400837541993)
          ·
            refine ⟨7360973040827550628156495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9814630721103400837541993 7360973040827550628156495)
            ·
              refine ⟨11041459561241325942234743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7360973040827550628156495 11041459561241325942234743)
              ·
                refine ⟨16562189341861988913352115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11041459561241325942234743 16562189341861988913352115)
                ·
                  refine ⟨24843284012792983370028173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16562189341861988913352115 24843284012792983370028173)
                  ·
                    refine ⟨9316231504797368763760565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24843284012792983370028173 9316231504797368763760565)
                    ·
                      refine ⟨873396703574753321602553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9316231504797368763760565 873396703574753321602553)
                      ·
                        rfl

theorem cell23_1700934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1700934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700934 prefixEnd_1700934 := by exact prefixLift 1700934
  have htrace : WordTrace (prefixWord ++ tailWord_1700934) baseStart_1700934 baseEnd_1700934 := by
    simpa [prefixWord, tailWord_1700934, baseEnd_1700934] using wordTrace_append hprefix tailTrace_1700934
  have hstable : (prefixWord ++ tailWord_1700934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700934).length < 2 ^ (prefixWord ++ tailWord_1700934).sum := by decide
  have hdescent : baseEnd_1700934 < baseStart_1700934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700937 : List Nat := [1, 2, 1, 1, 2, 2, 2, 7, 5]
def baseStart_1700937 : Nat := 118140960795 + 1700937 * 2 ^ 59
def prefixEnd_1700937 : Nat := 4983230072969 + 3 ^ 40 * 1700937 * 2
def baseEnd_1700937 : Nat := 97044249335190756651671

theorem tailTrace_1700937 : CollatzResearch.WordTrace tailWord_1700937 prefixEnd_1700937 97044249335190756651671 := by
  unfold tailWord_1700937
  simp only [CollatzResearch.WordTrace]
  refine ⟨62038269038803220757069065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41358846025868813838046043 62038269038803220757069065)
  ·
    refine ⟨46528701779102415567801799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62038269038803220757069065 46528701779102415567801799)
    ·
      refine ⟨69793052668653623351702699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46528701779102415567801799 69793052668653623351702699)
      ·
        refine ⟨104689579002980435027554049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69793052668653623351702699 104689579002980435027554049)
        ·
          refine ⟨78517184252235326270665537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104689579002980435027554049 78517184252235326270665537)
          ·
            refine ⟨58887888189176494702999153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78517184252235326270665537 58887888189176494702999153)
            ·
              refine ⟨44165916141882371027249365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58887888189176494702999153 44165916141882371027249365)
              ·
                refine ⟨1035138659575368070951157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44165916141882371027249365 1035138659575368070951157)
                ·
                  refine ⟨97044249335190756651671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1035138659575368070951157 97044249335190756651671)
                  ·
                    rfl

theorem cell23_1700937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 5].length) (baseStart_1700937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1700937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1700937 prefixEnd_1700937 := by exact prefixLift 1700937
  have htrace : WordTrace (prefixWord ++ tailWord_1700937) baseStart_1700937 baseEnd_1700937 := by
    simpa [prefixWord, tailWord_1700937, baseEnd_1700937] using wordTrace_append hprefix tailTrace_1700937
  have hstable : (prefixWord ++ tailWord_1700937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700937).length < 2 ^ (prefixWord ++ tailWord_1700937).sum := by decide
  have hdescent : baseEnd_1700937 < baseStart_1700937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701007 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 3]
def baseStart_1701007 : Nat := 118140960795 + 1701007 * 2 ^ 59
def prefixEnd_1701007 : Nat := 4983230072969 + 3 ^ 40 * 1701007 * 2
def baseEnd_1701007 : Nat := 873434187662531535989717

theorem tailTrace_1701007 : CollatzResearch.WordTrace tailWord_1701007 prefixEnd_1701007 873434187662531535989717 := by
  unfold tailWord_1701007
  simp only [CollatzResearch.WordTrace]
  refine ⟨62040822148549622712117275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41360548099033081808078183 62040822148549622712117275)
  ·
    refine ⟨93061233222824434068175913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62040822148549622712117275 93061233222824434068175913)
    ·
      refine ⟨69795924917118325551131935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93061233222824434068175913 69795924917118325551131935)
      ·
        refine ⟨104693887375677488326697903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69795924917118325551131935 104693887375677488326697903)
        ·
          refine ⟨157040831063516232490046855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104693887375677488326697903 157040831063516232490046855)
          ·
            refine ⟨235561246595274348735070283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157040831063516232490046855 235561246595274348735070283)
            ·
              refine ⟨353341869892911523102605425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235561246595274348735070283 353341869892911523102605425)
              ·
                refine ⟨265006402419683642326954069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353341869892911523102605425 265006402419683642326954069)
                ·
                  refine ⟨3105543778355667683518993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 265006402419683642326954069 3105543778355667683518993)
                  ·
                    refine ⟨2329157833766750762639245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3105543778355667683518993 2329157833766750762639245)
                    ·
                      refine ⟨873434187662531535989717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2329157833766750762639245 873434187662531535989717)
                      ·
                        rfl

theorem cell23_1701007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 3].length) (baseStart_1701007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701007 prefixEnd_1701007 := by exact prefixLift 1701007
  have htrace : WordTrace (prefixWord ++ tailWord_1701007) baseStart_1701007 baseEnd_1701007 := by
    simpa [prefixWord, tailWord_1701007, baseEnd_1701007] using wordTrace_append hprefix tailTrace_1701007
  have hstable : (prefixWord ++ tailWord_1701007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701007).length < 2 ^ (prefixWord ++ tailWord_1701007).sum := by decide
  have hdescent : baseEnd_1701007 < baseStart_1701007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701031 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1701031 : Nat := 118140960795 + 1701031 * 2 ^ 59
def prefixEnd_1701031 : Nat := 4983230072969 + 3 ^ 40 * 1701031 * 2
def baseEnd_1701031 : Nat := 291148837066079814029869

theorem tailTrace_1701031 : CollatzResearch.WordTrace tailWord_1701031 prefixEnd_1701031 291148837066079814029869 := by
  unfold tailWord_1701031
  simp only [CollatzResearch.WordTrace]
  refine ⟨62041697500462674810990947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41361131666975116540660631 62041697500462674810990947)
  ·
    refine ⟨93062546250694012216486421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62041697500462674810990947 93062546250694012216486421)
    ·
      refine ⟨4362306855501281822647801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93062546250694012216486421 4362306855501281822647801)
      ·
        refine ⟨3271730141625961366985851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4362306855501281822647801 3271730141625961366985851)
        ·
          refine ⟨4907595212438942050478777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271730141625961366985851 4907595212438942050478777)
          ·
            refine ⟨3680696409329206537859083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4907595212438942050478777 3680696409329206537859083)
            ·
              refine ⟨5521044613993809806788625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3680696409329206537859083 5521044613993809806788625)
              ·
                refine ⟨4140783460495357355091469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5521044613993809806788625 4140783460495357355091469)
                ·
                  refine ⟨1552793797685759008159301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4140783460495357355091469 1552793797685759008159301)
                  ·
                    refine ⟨291148837066079814029869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1552793797685759008159301 291148837066079814029869)
                    ·
                      rfl

theorem cell23_1701031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1701031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701031 prefixEnd_1701031 := by exact prefixLift 1701031
  have htrace : WordTrace (prefixWord ++ tailWord_1701031) baseStart_1701031 baseEnd_1701031 := by
    simpa [prefixWord, tailWord_1701031, baseEnd_1701031] using wordTrace_append hprefix tailTrace_1701031
  have hstable : (prefixWord ++ tailWord_1701031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701031).length < 2 ^ (prefixWord ++ tailWord_1701031).sum := by decide
  have hdescent : baseEnd_1701031 < baseStart_1701031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701041 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1701041 : Nat := 118140960795 + 1701041 * 2 ^ 59
def prefixEnd_1701041 : Nat := 4983230072969 + 3 ^ 40 * 1701041 * 2
def baseEnd_1701041 : Nat := 873451646004784402964561

theorem tailTrace_1701041 : CollatzResearch.WordTrace tailWord_1701041 prefixEnd_1701041 873451646004784402964561 := by
  unfold tailWord_1701041
  simp only [CollatzResearch.WordTrace]
  refine ⟨62042062230426446518854977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41361374820284297679236651 62042062230426446518854977)
  ·
    refine ⟨46531546672819834889141233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62042062230426446518854977 46531546672819834889141233)
    ·
      refine ⟨34898660004614876166855925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46531546672819834889141233 34898660004614876166855925)
      ·
        refine ⟨3271749375432644640642743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34898660004614876166855925 3271749375432644640642743)
        ·
          refine ⟨4907624063148966960964115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271749375432644640642743 4907624063148966960964115)
          ·
            refine ⟨7361436094723450441446173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907624063148966960964115 7361436094723450441446173)
            ·
              refine ⟨2760538535521293915542315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7361436094723450441446173 2760538535521293915542315)
              ·
                refine ⟨4140807803281940873313473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760538535521293915542315 4140807803281940873313473)
                ·
                  refine ⟨3105605852461455654985105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4140807803281940873313473 3105605852461455654985105)
                  ·
                    refine ⟨2329204389346091741238829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3105605852461455654985105 2329204389346091741238829)
                    ·
                      refine ⟨873451646004784402964561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2329204389346091741238829 873451646004784402964561)
                      ·
                        rfl

theorem cell23_1701041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1701041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701041 prefixEnd_1701041 := by exact prefixLift 1701041
  have htrace : WordTrace (prefixWord ++ tailWord_1701041) baseStart_1701041 baseEnd_1701041 := by
    simpa [prefixWord, tailWord_1701041, baseEnd_1701041] using wordTrace_append hprefix tailTrace_1701041
  have hstable : (prefixWord ++ tailWord_1701041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701041).length < 2 ^ (prefixWord ++ tailWord_1701041).sum := by decide
  have hdescent : baseEnd_1701041 < baseStart_1701041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701114 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5]
def baseStart_1701114 : Nat := 118140960795 + 1701114 * 2 ^ 59
def prefixEnd_1701114 : Nat := 4983230072969 + 3 ^ 40 * 1701114 * 2
def baseEnd_1701114 : Nat := 873489130092562617351725

theorem tailTrace_1701114 : CollatzResearch.WordTrace tailWord_1701114 prefixEnd_1701114 873489130092562617351725 := by
  unfold tailWord_1701114
  simp only [CollatzResearch.WordTrace]
  refine ⟨15511181189790494996565599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41363149839441319990841597 15511181189790494996565599)
  ·
    refine ⟨23266771784685742494848399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15511181189790494996565599 23266771784685742494848399)
    ·
      refine ⟨34900157677028613742272599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23266771784685742494848399 34900157677028613742272599)
      ·
        refine ⟨52350236515542920613408899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34900157677028613742272599 52350236515542920613408899)
        ·
          refine ⟨78525354773314380920113349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52350236515542920613408899 78525354773314380920113349)
          ·
            refine ⟨14723504019996446422521253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78525354773314380920113349 14723504019996446422521253)
            ·
              refine ⟨2760657003749333704222735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14723504019996446422521253 2760657003749333704222735)
              ·
                refine ⟨4140985505624000556334103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760657003749333704222735 4140985505624000556334103)
                ·
                  refine ⟨6211478258436000834501155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140985505624000556334103 6211478258436000834501155)
                  ·
                    refine ⟨9317217387654001251751733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6211478258436000834501155 9317217387654001251751733)
                    ·
                      refine ⟨873489130092562617351725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9317217387654001251751733 873489130092562617351725)
                      ·
                        rfl

theorem cell23_1701114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_1701114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701114 prefixEnd_1701114 := by exact prefixLift 1701114
  have htrace : WordTrace (prefixWord ++ tailWord_1701114) baseStart_1701114 baseEnd_1701114 := by
    simpa [prefixWord, tailWord_1701114, baseEnd_1701114] using wordTrace_append hprefix tailTrace_1701114
  have hstable : (prefixWord ++ tailWord_1701114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701114).length < 2 ^ (prefixWord ++ tailWord_1701114).sum := by decide
  have hdescent : baseEnd_1701114 < baseStart_1701114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701122 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_1701122 : Nat := 118140960795 + 1701122 * 2 ^ 59
def prefixEnd_1701122 : Nat := 4983230072969 + 3 ^ 40 * 1701122 * 2
def baseEnd_1701122 : Nat := 873493237937798586051689

theorem tailTrace_1701122 : CollatzResearch.WordTrace tailWord_1701122 prefixEnd_1701122 873493237937798586051689 := by
  unfold tailWord_1701122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15511254135783249338138405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41363344362088664901702413 15511254135783249338138405)
  ·
    refine ⟨2908360150459359250900951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15511254135783249338138405 2908360150459359250900951)
    ·
      refine ⟨4362540225689038876351427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2908360150459359250900951 4362540225689038876351427)
      ·
        refine ⟨6543810338533558314527141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4362540225689038876351427 6543810338533558314527141)
        ·
          refine ⟨1226964438475042183973839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6543810338533558314527141 1226964438475042183973839)
          ·
            refine ⟨1840446657712563275960759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226964438475042183973839 1840446657712563275960759)
            ·
              refine ⟨2760669986568844913941139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840446657712563275960759 2760669986568844913941139)
              ·
                refine ⟨4141004979853267370911709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760669986568844913941139 4141004979853267370911709)
                ·
                  refine ⟨1552876867444975264091891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4141004979853267370911709 1552876867444975264091891)
                  ·
                    refine ⟨2329315301167462896137837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1552876867444975264091891 2329315301167462896137837)
                    ·
                      refine ⟨873493237937798586051689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2329315301167462896137837 873493237937798586051689)
                      ·
                        rfl

theorem cell23_1701122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_1701122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701122 prefixEnd_1701122 := by exact prefixLift 1701122
  have htrace : WordTrace (prefixWord ++ tailWord_1701122) baseStart_1701122 baseEnd_1701122 := by
    simpa [prefixWord, tailWord_1701122, baseEnd_1701122] using wordTrace_append hprefix tailTrace_1701122
  have hstable : (prefixWord ++ tailWord_1701122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701122).length < 2 ^ (prefixWord ++ tailWord_1701122).sum := by decide
  have hdescent : baseEnd_1701122 < baseStart_1701122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701124 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1701124 : Nat := 118140960795 + 1701124 * 2 ^ 59
def prefixEnd_1701124 : Nat := 4983230072969 + 3 ^ 40 * 1701124 * 2
def baseEnd_1701124 : Nat := 873494264899107578226679

theorem tailTrace_1701124 : CollatzResearch.WordTrace tailWord_1701124 prefixEnd_1701124 873494264899107578226679 := by
  unfold tailWord_1701124
  simp only [CollatzResearch.WordTrace]
  refine ⟨31022544744562875847063213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41363392992750501129417617 31022544744562875847063213)
  ·
    refine ⟨11633454279211078442648705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31022544744562875847063213 11633454279211078442648705)
    ·
      refine ⟨8725090709408308831986529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11633454279211078442648705 8725090709408308831986529)
      ·
        refine ⟨6543818032056231623989897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8725090709408308831986529 6543818032056231623989897)
        ·
          refine ⟨4907863524042173717992423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6543818032056231623989897 4907863524042173717992423)
          ·
            refine ⟨7361795286063260576988635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907863524042173717992423 7361795286063260576988635)
            ·
              refine ⟨11042692929094890865482953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7361795286063260576988635 11042692929094890865482953)
              ·
                refine ⟨8282019696821168149112215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11042692929094890865482953 8282019696821168149112215)
                ·
                  refine ⟨12423029545231752223668323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8282019696821168149112215 12423029545231752223668323)
                  ·
                    refine ⟨18634544317847628335502485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12423029545231752223668323 18634544317847628335502485)
                    ·
                      refine ⟨873494264899107578226679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18634544317847628335502485 873494264899107578226679)
                      ·
                        rfl

theorem cell23_1701124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1701124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701124 prefixEnd_1701124 := by exact prefixLift 1701124
  have htrace : WordTrace (prefixWord ++ tailWord_1701124) baseStart_1701124 baseEnd_1701124 := by
    simpa [prefixWord, tailWord_1701124, baseEnd_1701124] using wordTrace_append hprefix tailTrace_1701124
  have hstable : (prefixWord ++ tailWord_1701124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701124).length < 2 ^ (prefixWord ++ tailWord_1701124).sum := by decide
  have hdescent : baseEnd_1701124 < baseStart_1701124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701134 : List Nat := [4, 1, 1, 2, 1, 4, 2, 8]
def baseStart_1701134 : Nat := 118140960795 + 1701134 * 2 ^ 59
def prefixEnd_1701134 : Nat := 4983230072969 + 3 ^ 40 * 1701134 * 2
def baseEnd_1701134 : Nat := 32351829618727871818579

theorem tailTrace_1701134 : CollatzResearch.WordTrace tailWord_1701134 prefixEnd_1701134 32351829618727871818579 := by
  unfold tailWord_1701134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7755681777386190425248807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41363636146059682267993637 7755681777386190425248807)
  ·
    refine ⟨11633522666079285637873211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7755681777386190425248807 11633522666079285637873211)
    ·
      refine ⟨17450283999118928456809817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11633522666079285637873211 17450283999118928456809817)
      ·
        refine ⟨13087712999339196342607363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17450283999118928456809817 13087712999339196342607363)
        ·
          refine ⟨19631569499008794513911045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13087712999339196342607363 19631569499008794513911045)
          ·
            refine ⟨3680919281064148971358321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19631569499008794513911045 3680919281064148971358321)
            ·
              refine ⟨2760689460798111728518741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680919281064148971358321 2760689460798111728518741)
              ·
                refine ⟨32351829618727871818579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2760689460798111728518741 32351829618727871818579)
                ·
                  rfl

theorem cell23_1701134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_1701134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701134 prefixEnd_1701134 := by exact prefixLift 1701134
  have htrace : WordTrace (prefixWord ++ tailWord_1701134) baseStart_1701134 baseEnd_1701134 := by
    simpa [prefixWord, tailWord_1701134, baseEnd_1701134] using wordTrace_append hprefix tailTrace_1701134
  have hstable : (prefixWord ++ tailWord_1701134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701134).length < 2 ^ (prefixWord ++ tailWord_1701134).sum := by decide
  have hdescent : baseEnd_1701134 < baseStart_1701134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701137 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_1701137 : Nat := 118140960795 + 1701137 * 2 ^ 59
def prefixEnd_1701137 : Nat := 4983230072969 + 3 ^ 40 * 1701137 * 2
def baseEnd_1701137 : Nat := 873500940147616027364119

theorem tailTrace_1701137 : CollatzResearch.WordTrace tailWord_1701137 prefixEnd_1701137 873500940147616027364119 := by
  unfold tailWord_1701137
  simp only [CollatzResearch.WordTrace]
  refine ⟨62045563638078654914349665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41363709092052436609566443 62045563638078654914349665)
  ·
    refine ⟨46534172728558991185762249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62045563638078654914349665 46534172728558991185762249)
    ·
      refine ⟨34900629546419243389321687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46534172728558991185762249 34900629546419243389321687)
      ·
        refine ⟨52350944319628865083982531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34900629546419243389321687 52350944319628865083982531)
        ·
          refine ⟨78526416479443297625973797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52350944319628865083982531 78526416479443297625973797)
          ·
            refine ⟨14723703089895618304870087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78526416479443297625973797 14723703089895618304870087)
            ·
              refine ⟨22085554634843427457305131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14723703089895618304870087 22085554634843427457305131)
              ·
                refine ⟨33128331952265141185957697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22085554634843427457305131 33128331952265141185957697)
                ·
                  refine ⟨24846248964198855889468273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33128331952265141185957697 24846248964198855889468273)
                  ·
                    refine ⟨18634686723149141917101205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24846248964198855889468273 18634686723149141917101205)
                    ·
                      refine ⟨873500940147616027364119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18634686723149141917101205 873500940147616027364119)
                      ·
                        rfl

theorem cell23_1701137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_1701137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701137 prefixEnd_1701137 := by exact prefixLift 1701137
  have htrace : WordTrace (prefixWord ++ tailWord_1701137) baseStart_1701137 baseEnd_1701137 := by
    simpa [prefixWord, tailWord_1701137, baseEnd_1701137] using wordTrace_append hprefix tailTrace_1701137
  have hstable : (prefixWord ++ tailWord_1701137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701137).length < 2 ^ (prefixWord ++ tailWord_1701137).sum := by decide
  have hdescent : baseEnd_1701137 < baseStart_1701137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701178 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3]
def baseStart_1701178 : Nat := 118140960795 + 1701178 * 2 ^ 59
def prefixEnd_1701178 : Nat := 4983230072969 + 3 ^ 40 * 1701178 * 2
def baseEnd_1701178 : Nat := 873521992854450366951431

theorem tailTrace_1701178 : CollatzResearch.WordTrace tailWord_1701178 prefixEnd_1701178 873521992854450366951431 := by
  unfold tailWord_1701178
  simp only [CollatzResearch.WordTrace]
  refine ⟨15511764757732529729148047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41364706020620079277728125 15511764757732529729148047)
  ·
    refine ⟨23267647136598794593722071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15511764757732529729148047 23267647136598794593722071)
    ·
      refine ⟨34901470704898191890583107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23267647136598794593722071 34901470704898191890583107)
      ·
        refine ⟨52352206057347287835874661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34901470704898191890583107 52352206057347287835874661)
        ·
          refine ⟨9816038635752616469226499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52352206057347287835874661 9816038635752616469226499)
          ·
            refine ⟨14724057953628924703839749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9816038635752616469226499 14724057953628924703839749)
            ·
              refine ⟨2760760866305423381969953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14724057953628924703839749 2760760866305423381969953)
              ·
                refine ⟨2070570649729067536477465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2760760866305423381969953 2070570649729067536477465)
                ·
                  refine ⟨1552927987296800652358099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2070570649729067536477465 1552927987296800652358099)
                  ·
                    refine ⟨2329391980945200978537149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1552927987296800652358099 2329391980945200978537149)
                    ·
                      refine ⟨873521992854450366951431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2329391980945200978537149 873521992854450366951431)
                      ·
                        rfl

theorem cell23_1701178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_1701178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701178 prefixEnd_1701178 := by exact prefixLift 1701178
  have htrace : WordTrace (prefixWord ++ tailWord_1701178) baseStart_1701178 baseEnd_1701178 := by
    simpa [prefixWord, tailWord_1701178, baseEnd_1701178] using wordTrace_append hprefix tailTrace_1701178
  have hstable : (prefixWord ++ tailWord_1701178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701178).length < 2 ^ (prefixWord ++ tailWord_1701178).sum := by decide
  have hdescent : baseEnd_1701178 < baseStart_1701178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701218 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_1701218 : Nat := 118140960795 + 1701218 * 2 ^ 59
def prefixEnd_1701218 : Nat := 4983230072969 + 3 ^ 40 * 1701218 * 2
def baseEnd_1701218 : Nat := 873542532080630210451247

theorem tailTrace_1701218 : CollatzResearch.WordTrace tailWord_1701218 prefixEnd_1701218 873542532080630210451247 := by
  unfold tailWord_1701218
  simp only [CollatzResearch.WordTrace]
  refine ⟨15512129487696301437012077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41365678633856803832032205 15512129487696301437012077)
  ·
    refine ⟨5817048557886113038879529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15512129487696301437012077 5817048557886113038879529)
    ·
      refine ⟨4362786418414584779159647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5817048557886113038879529 4362786418414584779159647)
      ·
        refine ⟨6544179627621877168739471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4362786418414584779159647 6544179627621877168739471)
        ·
          refine ⟨9816269441432815753109207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544179627621877168739471 9816269441432815753109207)
          ·
            refine ⟨14724404162149223629663811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9816269441432815753109207 14724404162149223629663811)
            ·
              refine ⟨22086606243223835444495717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14724404162149223629663811 22086606243223835444495717)
              ·
                refine ⟨4141238670604469145842947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22086606243223835444495717 4141238670604469145842947)
                ·
                  refine ⟨6211858005906703718764421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141238670604469145842947 6211858005906703718764421)
                  ·
                    refine ⟨1164723376107506947268329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6211858005906703718764421 1164723376107506947268329)
                    ·
                      refine ⟨873542532080630210451247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164723376107506947268329 873542532080630210451247)
                      ·
                        rfl

theorem cell23_1701218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_1701218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701218 prefixEnd_1701218 := by exact prefixLift 1701218
  have htrace : WordTrace (prefixWord ++ tailWord_1701218) baseStart_1701218 baseEnd_1701218 := by
    simpa [prefixWord, tailWord_1701218, baseEnd_1701218] using wordTrace_append hprefix tailTrace_1701218
  have hstable : (prefixWord ++ tailWord_1701218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701218).length < 2 ^ (prefixWord ++ tailWord_1701218).sum := by decide
  have hdescent : baseEnd_1701218 < baseStart_1701218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701241 : List Nat := [1, 2, 1, 3, 2, 1, 4, 4, 5]
def baseStart_1701241 : Nat := 118140960795 + 1701241 * 2 ^ 59
def prefixEnd_1701241 : Nat := 4983230072969 + 3 ^ 40 * 1701241 * 2
def baseEnd_1701241 : Nat := 97061593570631513384849

theorem tailTrace_1701241 : CollatzResearch.WordTrace tailWord_1701241 prefixEnd_1701241 97061593570631513384849 := by
  unfold tailWord_1701241
  simp only [CollatzResearch.WordTrace]
  refine ⟨62049356829701880676135577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41366237886467920450757051 62049356829701880676135577)
  ·
    refine ⟨46537017622276410507101683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62049356829701880676135577 46537017622276410507101683)
    ·
      refine ⟨69805526433414615760652525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46537017622276410507101683 69805526433414615760652525)
      ·
        refine ⟨26177072412530480910244697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69805526433414615760652525 26177072412530480910244697)
        ·
          refine ⟨19632804309397860682683523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26177072412530480910244697 19632804309397860682683523)
          ·
            refine ⟨29449206464096791024025285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19632804309397860682683523 29449206464096791024025285)
            ·
              refine ⟨5521726212018148317004741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29449206464096791024025285 5521726212018148317004741)
              ·
                refine ⟨1035323664753402809438389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5521726212018148317004741 1035323664753402809438389)
                ·
                  refine ⟨97061593570631513384849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1035323664753402809438389 97061593570631513384849)
                  ·
                    rfl

theorem cell23_1701241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 5].length) (baseStart_1701241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701241 prefixEnd_1701241 := by exact prefixLift 1701241
  have htrace : WordTrace (prefixWord ++ tailWord_1701241) baseStart_1701241 baseEnd_1701241 := by
    simpa [prefixWord, tailWord_1701241, baseEnd_1701241] using wordTrace_append hprefix tailTrace_1701241
  have hstable : (prefixWord ++ tailWord_1701241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701241).length < 2 ^ (prefixWord ++ tailWord_1701241).sum := by decide
  have hdescent : baseEnd_1701241 < baseStart_1701241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701251 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 3]
def baseStart_1701251 : Nat := 118140960795 + 1701251 * 2 ^ 59
def prefixEnd_1701251 : Nat := 4983230072969 + 3 ^ 40 * 1701251 * 2
def baseEnd_1701251 : Nat := 873559476942228581338595

theorem tailTrace_1701251 : CollatzResearch.WordTrace tailWord_1701251 prefixEnd_1701251 873559476942228581338595 := by
  unfold tailWord_1701251
  simp only [CollatzResearch.WordTrace]
  refine ⟨62049721559665652383999607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41366481039777101589333071 62049721559665652383999607)
  ·
    refine ⟨93074582339498478575999411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62049721559665652383999607 93074582339498478575999411)
    ·
      refine ⟨139611873509247717863999117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93074582339498478575999411 139611873509247717863999117)
      ·
        refine ⟨52354452565967894198999669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139611873509247717863999117 52354452565967894198999669)
        ·
          refine ⟨4908229928059490081156219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52354452565967894198999669 4908229928059490081156219)
          ·
            refine ⟨7362344892089235121734329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908229928059490081156219 7362344892089235121734329)
            ·
              refine ⟨5521758669066926341300747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7362344892089235121734329 5521758669066926341300747)
              ·
                refine ⟨8282638003600389511951121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5521758669066926341300747 8282638003600389511951121)
                ·
                  refine ⟨6211978502700292133963341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8282638003600389511951121 6211978502700292133963341)
                  ·
                    refine ⟨2329491938512609550236253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6211978502700292133963341 2329491938512609550236253)
                    ·
                      refine ⟨873559476942228581338595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2329491938512609550236253 873559476942228581338595)
                      ·
                        rfl

theorem cell23_1701251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_1701251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701251 prefixEnd_1701251 := by exact prefixLift 1701251
  have htrace : WordTrace (prefixWord ++ tailWord_1701251) baseStart_1701251 baseEnd_1701251 := by
    simpa [prefixWord, tailWord_1701251, baseEnd_1701251] using wordTrace_append hprefix tailTrace_1701251
  have hstable : (prefixWord ++ tailWord_1701251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701251).length < 2 ^ (prefixWord ++ tailWord_1701251).sum := by decide
  have hdescent : baseEnd_1701251 < baseStart_1701251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701252 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_1701252 : Nat := 118140960795 + 1701252 * 2 ^ 59
def prefixEnd_1701252 : Nat := 4983230072969 + 3 ^ 40 * 1701252 * 2
def baseEnd_1701252 : Nat := 873559990422883077426091

theorem tailTrace_1701252 : CollatzResearch.WordTrace tailWord_1701252 prefixEnd_1701252 873559990422883077426091 := by
  unfold tailWord_1701252
  simp only [CollatzResearch.WordTrace]
  refine ⟨31024879016331014777393005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41366505355108019703190673 31024879016331014777393005)
  ·
    refine ⟨11634329631124130541522377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31024879016331014777393005 11634329631124130541522377)
    ·
      refine ⟨8725747223343097906141783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11634329631124130541522377 8725747223343097906141783)
      ·
        refine ⟨13088620835014646859212675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8725747223343097906141783 13088620835014646859212675)
        ·
          refine ⟨19632931252521970288819013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13088620835014646859212675 19632931252521970288819013)
          ·
            refine ⟨3681174609847869429153565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19632931252521970288819013 3681174609847869429153565)
            ·
              refine ⟨1380440478692951035932587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3681174609847869429153565 1380440478692951035932587)
              ·
                refine ⟨2070660718039426553898881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380440478692951035932587 2070660718039426553898881)
                ·
                  refine ⟨1552995538529569915424161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2070660718039426553898881 1552995538529569915424161)
                  ·
                    refine ⟨1164746653897177436568121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1552995538529569915424161 1164746653897177436568121)
                    ·
                      refine ⟨873559990422883077426091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164746653897177436568121 873559990422883077426091)
                      ·
                        rfl

theorem cell23_1701252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_1701252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701252 prefixEnd_1701252 := by exact prefixLift 1701252
  have htrace : WordTrace (prefixWord ++ tailWord_1701252) baseStart_1701252 baseEnd_1701252 := by
    simpa [prefixWord, tailWord_1701252, baseEnd_1701252] using wordTrace_append hprefix tailTrace_1701252
  have hstable : (prefixWord ++ tailWord_1701252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701252).length < 2 ^ (prefixWord ++ tailWord_1701252).sum := by decide
  have hdescent : baseEnd_1701252 < baseStart_1701252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701304 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_1701304 : Nat := 118140960795 + 1701304 * 2 ^ 59
def prefixEnd_1701304 : Nat := 4983230072969 + 3 ^ 40 * 1701304 * 2
def baseEnd_1701304 : Nat := 873586691416916873975851

theorem tailTrace_1701304 : CollatzResearch.WordTrace tailWord_1701304 prefixEnd_1701304 873586691416916873975851 := by
  unfold tailWord_1701304
  simp only [CollatzResearch.WordTrace]
  refine ⟨31025827314236821217839483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41367769752315761623785977 31025827314236821217839483)
  ·
    refine ⟨46538740971355231826759225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31025827314236821217839483 46538740971355231826759225)
    ·
      refine ⟨34904055728516423870069419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46538740971355231826759225 34904055728516423870069419)
      ·
        refine ⟨52356083592774635805104129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34904055728516423870069419 52356083592774635805104129)
        ·
          refine ⟨39267062694580976853828097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52356083592774635805104129 39267062694580976853828097)
          ·
            refine ⟨29450297020935732640371073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39267062694580976853828097 29450297020935732640371073)
            ·
              refine ⟨22087722765701799480278305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29450297020935732640371073 22087722765701799480278305)
              ·
                refine ⟨16565792074276349610208729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22087722765701799480278305 16565792074276349610208729)
                ·
                  refine ⟨12424344055707262207656547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16565792074276349610208729 12424344055707262207656547)
                  ·
                    refine ⟨18636516083560893311484821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12424344055707262207656547 18636516083560893311484821)
                    ·
                      refine ⟨873586691416916873975851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18636516083560893311484821 873586691416916873975851)
                      ·
                        rfl

theorem cell23_1701304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_1701304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701304 prefixEnd_1701304 := by exact prefixLift 1701304
  have htrace : WordTrace (prefixWord ++ tailWord_1701304) baseStart_1701304 baseEnd_1701304 := by
    simpa [prefixWord, tailWord_1701304, baseEnd_1701304] using wordTrace_append hprefix tailTrace_1701304
  have hstable : (prefixWord ++ tailWord_1701304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701304).length < 2 ^ (prefixWord ++ tailWord_1701304).sum := by decide
  have hdescent : baseEnd_1701304 < baseStart_1701304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701361 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 3, 5]
def baseStart_1701361 : Nat := 118140960795 + 1701361 * 2 ^ 59
def prefixEnd_1701361 : Nat := 4983230072969 + 3 ^ 40 * 1701361 * 2
def baseEnd_1701361 : Nat := 291205319938074383654363

theorem tailTrace_1701361 : CollatzResearch.WordTrace tailWord_1701361 prefixEnd_1701361 291205319938074383654363 := by
  unfold tailWord_1701361
  simp only [CollatzResearch.WordTrace]
  refine ⟨62053733589267141170503937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41369155726178094113669291 62053733589267141170503937)
  ·
    refine ⟨46540300191950355877877953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62053733589267141170503937 46540300191950355877877953)
    ·
      refine ⟨34905225143962766908408465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46540300191950355877877953 34905225143962766908408465)
      ·
        refine ⟨26178918857972075181306349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34905225143962766908408465 26178918857972075181306349)
        ·
          refine ⟨9817094571739528192989881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26178918857972075181306349 9817094571739528192989881)
          ·
            refine ⟨7362820928804646144742411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9817094571739528192989881 7362820928804646144742411)
            ·
              refine ⟨11044231393206969217113617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362820928804646144742411 11044231393206969217113617)
              ·
                refine ⟨8283173544905226912835213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11044231393206969217113617 8283173544905226912835213)
                ·
                  refine ⟨3106190079339460092313205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8283173544905226912835213 3106190079339460092313205)
                  ·
                    refine ⟨291205319938074383654363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3106190079339460092313205 291205319938074383654363)
                    ·
                      rfl

theorem cell23_1701361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_1701361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701361 prefixEnd_1701361 := by exact prefixLift 1701361
  have htrace : WordTrace (prefixWord ++ tailWord_1701361) baseStart_1701361 baseEnd_1701361 := by
    simpa [prefixWord, tailWord_1701361, baseEnd_1701361] using wordTrace_append hprefix tailTrace_1701361
  have hstable : (prefixWord ++ tailWord_1701361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701361).length < 2 ^ (prefixWord ++ tailWord_1701361).sum := by decide
  have hdescent : baseEnd_1701361 < baseStart_1701361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701395 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 1, 5]
def baseStart_1701395 : Nat := 118140960795 + 1701395 * 2 ^ 59
def prefixEnd_1701395 : Nat := 4983230072969 + 3 ^ 40 * 1701395 * 2
def baseEnd_1701395 : Nat := 291211139385492005979311

theorem tailTrace_1701395 : CollatzResearch.WordTrace tailWord_1701395 prefixEnd_1701395 291211139385492005979311 := by
  unfold tailWord_1701395
  simp only [CollatzResearch.WordTrace]
  refine ⟨62054973671143964977241639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41369982447429309984827759 62054973671143964977241639)
  ·
    refine ⟨93082460506715947465862459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62054973671143964977241639 93082460506715947465862459)
    ·
      refine ⟨139623690760073921198793689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93082460506715947465862459 139623690760073921198793689)
      ·
        refine ⟨104717768070055440899095267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139623690760073921198793689 104717768070055440899095267)
        ·
          refine ⟨157076652105083161348642901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104717768070055440899095267 157076652105083161348642901)
          ·
            refine ⟨1840742016856443297054409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 157076652105083161348642901 1840742016856443297054409)
            ·
              refine ⟨1380556512642332472790807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1840742016856443297054409 1380556512642332472790807)
              ·
                refine ⟨2070834768963498709186211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380556512642332472790807 2070834768963498709186211)
                ·
                  refine ⟨3106252153445248063779317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070834768963498709186211 3106252153445248063779317)
                  ·
                    refine ⟨291211139385492005979311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3106252153445248063779317 291211139385492005979311)
                    ·
                      rfl

theorem cell23_1701395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 5].length) (baseStart_1701395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701395 prefixEnd_1701395 := by exact prefixLift 1701395
  have htrace : WordTrace (prefixWord ++ tailWord_1701395) baseStart_1701395 baseEnd_1701395 := by
    simpa [prefixWord, tailWord_1701395, baseEnd_1701395] using wordTrace_append hprefix tailTrace_1701395
  have hstable : (prefixWord ++ tailWord_1701395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701395).length < 2 ^ (prefixWord ++ tailWord_1701395).sum := by decide
  have hdescent : baseEnd_1701395 < baseStart_1701395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701418 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1701418 : Nat := 118140960795 + 1701418 * 2 ^ 59
def prefixEnd_1701418 : Nat := 4983230072969 + 3 ^ 40 * 1701418 * 2
def baseEnd_1701418 : Nat := 873645228211529427950327

theorem tailTrace_1701418 : CollatzResearch.WordTrace tailWord_1701418 prefixEnd_1701418 873645228211529427950327 := by
  unfold tailWord_1701418
  simp only [CollatzResearch.WordTrace]
  refine ⟨15513953137515159976332227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41370541700040426603552605 15513953137515159976332227)
  ·
    refine ⟨23270929706272739964498341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15513953137515159976332227 23270929706272739964498341)
    ·
      refine ⟨4363299319926138743343439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23270929706272739964498341 4363299319926138743343439)
      ·
        refine ⟨6544948979889208115015159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4363299319926138743343439 6544948979889208115015159)
        ·
          refine ⟨9817423469833812172522739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544948979889208115015159 9817423469833812172522739)
          ·
            refine ⟨14726135204750718258784109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9817423469833812172522739 14726135204750718258784109)
            ·
              refine ⟨5522300701781519347044041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14726135204750718258784109 5522300701781519347044041)
              ·
                refine ⟨4141725526336139510283031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5522300701781519347044041 4141725526336139510283031)
                ·
                  refine ⟨6212588289504209265424547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141725526336139510283031 6212588289504209265424547)
                  ·
                    refine ⟨9318882434256313898136821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6212588289504209265424547 9318882434256313898136821)
                    ·
                      refine ⟨873645228211529427950327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9318882434256313898136821 873645228211529427950327)
                      ·
                        rfl

theorem cell23_1701418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1701418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701418 prefixEnd_1701418 := by exact prefixLift 1701418
  have htrace : WordTrace (prefixWord ++ tailWord_1701418) baseStart_1701418 baseEnd_1701418 := by
    simpa [prefixWord, tailWord_1701418, baseEnd_1701418] using wordTrace_append hprefix tailTrace_1701418
  have hstable : (prefixWord ++ tailWord_1701418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701418).length < 2 ^ (prefixWord ++ tailWord_1701418).sum := by decide
  have hdescent : baseEnd_1701418 < baseStart_1701418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701461 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1701461 : Nat := 118140960795 + 1701461 * 2 ^ 59
def prefixEnd_1701461 : Nat := 4983230072969 + 3 ^ 40 * 1701461 * 2
def baseEnd_1701461 : Nat := 873667307879672759712629

theorem tailTrace_1701461 : CollatzResearch.WordTrace tailWord_1701461 prefixEnd_1701461 873667307879672759712629 := by
  unfold tailWord_1701461
  simp only [CollatzResearch.WordTrace]
  refine ⟨62057380888904858249144237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41371587259269905499429491 62057380888904858249144237)
  ·
    refine ⟨23271517833339321843429089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62057380888904858249144237 23271517833339321843429089)
    ·
      refine ⟨17453638375004491382571817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23271517833339321843429089 17453638375004491382571817)
      ·
        refine ⟨13090228781253368536928863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17453638375004491382571817 13090228781253368536928863)
        ·
          refine ⟨19635343171880052805393295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13090228781253368536928863 19635343171880052805393295)
          ·
            refine ⟨29453014757820079208089943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19635343171880052805393295 29453014757820079208089943)
            ·
              refine ⟨44179522136730118812134915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29453014757820079208089943 44179522136730118812134915)
              ·
                refine ⟨66269283205095178218202373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44179522136730118812134915 66269283205095178218202373)
                ·
                  refine ⟨12425490600955345915912945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66269283205095178218202373 12425490600955345915912945)
                  ·
                    refine ⟨9319117950716509436934709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12425490600955345915912945 9319117950716509436934709)
                    ·
                      refine ⟨873667307879672759712629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9319117950716509436934709 873667307879672759712629)
                      ·
                        rfl

theorem cell23_1701461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1701461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701461 prefixEnd_1701461 := by exact prefixLift 1701461
  have htrace : WordTrace (prefixWord ++ tailWord_1701461) baseStart_1701461 baseEnd_1701461 := by
    simpa [prefixWord, tailWord_1701461, baseEnd_1701461] using wordTrace_append hprefix tailTrace_1701461
  have hstable : (prefixWord ++ tailWord_1701461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701461).length < 2 ^ (prefixWord ++ tailWord_1701461).sum := by decide
  have hdescent : baseEnd_1701461 < baseStart_1701461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701481 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 2, 6]
def baseStart_1701481 : Nat := 118140960795 + 1701481 * 2 ^ 59
def prefixEnd_1701481 : Nat := 4983230072969 + 3 ^ 40 * 1701481 * 2
def baseEnd_1701481 : Nat := 291225859164254227154179

theorem tailTrace_1701481 : CollatzResearch.WordTrace tailWord_1701481 prefixEnd_1701481 291225859164254227154179 := by
  unfold tailWord_1701481
  simp only [CollatzResearch.WordTrace]
  refine ⟨62058110348832401664872297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41372073565888267776581531 62058110348832401664872297)
  ·
    refine ⟨46543582761624301248654223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62058110348832401664872297 46543582761624301248654223)
    ·
      refine ⟨69815374142436451872981335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46543582761624301248654223 69815374142436451872981335)
      ·
        refine ⟨104723061213654677809472003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69815374142436451872981335 104723061213654677809472003)
        ·
          refine ⟨157084591820482016714208005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104723061213654677809472003 157084591820482016714208005)
          ·
            refine ⟨29453360966340378133914001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157084591820482016714208005 29453360966340378133914001)
            ·
              refine ⟨22090020724755283600435501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29453360966340378133914001 22090020724755283600435501)
              ·
                refine ⟨8283757771783231350163313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22090020724755283600435501 8283757771783231350163313)
                ·
                  refine ⟨6212818328837423512622485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8283757771783231350163313 6212818328837423512622485)
                  ·
                    refine ⟨291225859164254227154179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6212818328837423512622485 291225859164254227154179)
                    ·
                      rfl

theorem cell23_1701481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_1701481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701481 prefixEnd_1701481 := by exact prefixLift 1701481
  have htrace : WordTrace (prefixWord ++ tailWord_1701481) baseStart_1701481 baseEnd_1701481 := by
    simpa [prefixWord, tailWord_1701481, baseEnd_1701481] using wordTrace_append hprefix tailTrace_1701481
  have hstable : (prefixWord ++ tailWord_1701481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701481).length < 2 ^ (prefixWord ++ tailWord_1701481).sum := by decide
  have hdescent : baseEnd_1701481 < baseStart_1701481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701482 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1701482 : Nat := 118140960795 + 1701482 * 2 ^ 59
def prefixEnd_1701482 : Nat := 4983230072969 + 3 ^ 40 * 1701482 * 2
def baseEnd_1701482 : Nat := 873678090973417177550033

theorem tailTrace_1701482 : CollatzResearch.WordTrace tailWord_1701482 prefixEnd_1701482 873678090973417177550033 := by
  unfold tailWord_1701482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15514536705457194708914675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41372097881219185890439133 15514536705457194708914675)
  ·
    refine ⟨23271805058185792063372013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15514536705457194708914675 23271805058185792063372013)
    ·
      refine ⟨8726926896819672023764505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23271805058185792063372013 8726926896819672023764505)
      ·
        refine ⟨6545195172614754017823379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8726926896819672023764505 6545195172614754017823379)
        ·
          refine ⟨9817792758922131026735069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545195172614754017823379 9817792758922131026735069)
          ·
            refine ⟨3681672284595799135025651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9817792758922131026735069 3681672284595799135025651)
            ·
              refine ⟨5522508426893698702538477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3681672284595799135025651 5522508426893698702538477)
              ·
                refine ⟨2070940660085137013451929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5522508426893698702538477 2070940660085137013451929)
                ·
                  refine ⟨1553205495063852760088947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2070940660085137013451929 1553205495063852760088947)
                  ·
                    refine ⟨2329808242595779140133421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1553205495063852760088947 2329808242595779140133421)
                    ·
                      refine ⟨873678090973417177550033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2329808242595779140133421 873678090973417177550033)
                      ·
                        rfl

theorem cell23_1701482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1701482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701482 prefixEnd_1701482 := by exact prefixLift 1701482
  have htrace : WordTrace (prefixWord ++ tailWord_1701482) baseStart_1701482 baseEnd_1701482 := by
    simpa [prefixWord, tailWord_1701482, baseEnd_1701482] using wordTrace_append hprefix tailTrace_1701482
  have hstable : (prefixWord ++ tailWord_1701482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701482).length < 2 ^ (prefixWord ++ tailWord_1701482).sum := by decide
  have hdescent : baseEnd_1701482 < baseStart_1701482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701505 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_1701505 : Nat := 118140960795 + 1701505 * 2 ^ 59
def prefixEnd_1701505 : Nat := 4983230072969 + 3 ^ 40 * 1701505 * 2
def baseEnd_1701505 : Nat := 873689901028470587562427

theorem tailTrace_1701505 : CollatzResearch.WordTrace tailWord_1701505 prefixEnd_1701505 873689901028470587562427 := by
  unfold tailWord_1701505
  simp only [CollatzResearch.WordTrace]
  refine ⟨62058985700745453763745969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41372657133830302509163979 62058985700745453763745969)
  ·
    refine ⟨46544239275559090322809477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62058985700745453763745969 46544239275559090322809477)
    ·
      refine ⟨8727044864167329435526777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46544239275559090322809477 8727044864167329435526777)
      ·
        refine ⟨6545283648125497076645083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8727044864167329435526777 6545283648125497076645083)
        ·
          refine ⟨9817925472188245614967625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545283648125497076645083 9817925472188245614967625)
          ·
            refine ⟨7363444104141184211225719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9817925472188245614967625 7363444104141184211225719)
            ·
              refine ⟨11045166156211776316838579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7363444104141184211225719 11045166156211776316838579)
              ·
                refine ⟨16567749234317664475257869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11045166156211776316838579 16567749234317664475257869)
                ·
                  refine ⟨6212905962869124178221701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16567749234317664475257869 6212905962869124178221701)
                  ·
                    refine ⟨1164919868037960783416569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6212905962869124178221701 1164919868037960783416569)
                    ·
                      refine ⟨873689901028470587562427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164919868037960783416569 873689901028470587562427)
                      ·
                        rfl

theorem cell23_1701505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_1701505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701505 prefixEnd_1701505 := by exact prefixLift 1701505
  have htrace : WordTrace (prefixWord ++ tailWord_1701505) baseStart_1701505 baseEnd_1701505 := by
    simpa [prefixWord, tailWord_1701505, baseEnd_1701505] using wordTrace_append hprefix tailTrace_1701505
  have hstable : (prefixWord ++ tailWord_1701505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701505).length < 2 ^ (prefixWord ++ tailWord_1701505).sum := by decide
  have hdescent : baseEnd_1701505 < baseStart_1701505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701571 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 3, 10]
def baseStart_1701571 : Nat := 118140960795 + 1701571 * 2 ^ 59
def prefixEnd_1701571 : Nat := 4983230072969 + 3 ^ 40 * 1701571 * 2
def baseEnd_1701571 : Nat := 291241263583889109779041

theorem tailTrace_1701571 : CollatzResearch.WordTrace tailWord_1701571 prefixEnd_1701571 291241263583889109779041 := by
  unfold tailWord_1701571
  simp only [CollatzResearch.WordTrace]
  refine ⟨62061392918506347035648567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41374261945670898023765711 62061392918506347035648567)
  ·
    refine ⟨93092089377759520553472851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62061392918506347035648567 93092089377759520553472851)
    ·
      refine ⟨139638134066639280830209277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93092089377759520553472851 139638134066639280830209277)
      ·
        refine ⟨52364300274989730311328479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139638134066639280830209277 52364300274989730311328479)
        ·
          refine ⟨78546450412484595466992719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52364300274989730311328479 78546450412484595466992719)
          ·
            refine ⟨117819675618726893200489079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78546450412484595466992719 117819675618726893200489079)
            ·
              refine ⟨176729513428090339800733619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117819675618726893200489079 176729513428090339800733619)
              ·
                refine ⟨265094270142135509701100429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176729513428090339800733619 265094270142135509701100429)
                ·
                  refine ⟨99410351303300816137912661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265094270142135509701100429 99410351303300816137912661)
                  ·
                    refine ⟨291241263583889109779041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 99410351303300816137912661 291241263583889109779041)
                    ·
                      rfl

theorem cell23_1701571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 10].length) (baseStart_1701571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701571 prefixEnd_1701571 := by exact prefixLift 1701571
  have htrace : WordTrace (prefixWord ++ tailWord_1701571) baseStart_1701571 baseEnd_1701571 := by
    simpa [prefixWord, tailWord_1701571, baseEnd_1701571] using wordTrace_append hprefix tailTrace_1701571
  have hstable : (prefixWord ++ tailWord_1701571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701571).length < 2 ^ (prefixWord ++ tailWord_1701571).sum := by decide
  have hdescent : baseEnd_1701571 < baseStart_1701571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701590 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1701590 : Nat := 118140960795 + 1701590 * 2 ^ 59
def prefixEnd_1701590 : Nat := 4983230072969 + 3 ^ 40 * 1701590 * 2
def baseEnd_1701590 : Nat := 873733546884102754999537

theorem tailTrace_1701590 : CollatzResearch.WordTrace tailWord_1701590 prefixEnd_1701590 873733546884102754999537 := by
  unfold tailWord_1701590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878880369089844580036889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41374723936958342187060149 3878880369089844580036889)
  ·
    refine ⟨2909160276817383435027667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3878880369089844580036889 2909160276817383435027667)
    ·
      refine ⟨4363740415226075152541501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2909160276817383435027667 4363740415226075152541501)
      ·
        refine ⟨1636402655709778182203063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4363740415226075152541501 1636402655709778182203063)
        ·
          refine ⟨2454603983564667273304595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636402655709778182203063 2454603983564667273304595)
          ·
            refine ⟨3681905975347000909956893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454603983564667273304595 3681905975347000909956893)
            ·
              refine ⟨1380714740755125341233835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3681905975347000909956893 1380714740755125341233835)
              ·
                refine ⟨2071072111132688011850753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380714740755125341233835 2071072111132688011850753)
                ·
                  refine ⟨1553304083349516008888065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2071072111132688011850753 1553304083349516008888065)
                  ·
                    refine ⟨1164978062512137006666049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1553304083349516008888065 1164978062512137006666049)
                    ·
                      refine ⟨873733546884102754999537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1164978062512137006666049 873733546884102754999537)
                      ·
                        rfl

theorem cell23_1701590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1701590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701590 prefixEnd_1701590 := by exact prefixLift 1701590
  have htrace : WordTrace (prefixWord ++ tailWord_1701590) baseStart_1701590 baseEnd_1701590 := by
    simpa [prefixWord, tailWord_1701590, baseEnd_1701590] using wordTrace_append hprefix tailTrace_1701590
  have hstable : (prefixWord ++ tailWord_1701590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701590).length < 2 ^ (prefixWord ++ tailWord_1701590).sum := by decide
  have hdescent : baseEnd_1701590 < baseStart_1701590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701605 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_1701605 : Nat := 118140960795 + 1701605 * 2 ^ 59
def prefixEnd_1701605 : Nat := 4983230072969 + 3 ^ 40 * 1701605 * 2
def baseEnd_1701605 : Nat := 291247083031306732103989

theorem tailTrace_1701605 : CollatzResearch.WordTrace tailWord_1701605 prefixEnd_1701605 291247083031306732103989 := by
  unfold tailWord_1701605
  simp only [CollatzResearch.WordTrace]
  refine ⟨62062633000383170842386269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41375088666922113894924179 62062633000383170842386269)
  ·
    refine ⟨23273487375143689065894851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62062633000383170842386269 23273487375143689065894851)
    ·
      refine ⟨34910231062715533598842277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23273487375143689065894851 34910231062715533598842277)
      ·
        refine ⟨6545668324259162549782927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34910231062715533598842277 6545668324259162549782927)
        ·
          refine ⟨9818502486388743824674391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545668324259162549782927 9818502486388743824674391)
          ·
            refine ⟨14727753729583115737011587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9818502486388743824674391 14727753729583115737011587)
            ·
              refine ⟨22091630594374673605517381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14727753729583115737011587 22091630594374673605517381)
              ·
                refine ⟨4142180736445251301034509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22091630594374673605517381 4142180736445251301034509)
                ·
                  refine ⟨1553317776166969237887941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4142180736445251301034509 1553317776166969237887941)
                  ·
                    refine ⟨291247083031306732103989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1553317776166969237887941 291247083031306732103989)
                    ·
                      rfl

theorem cell23_1701605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_1701605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701605 prefixEnd_1701605 := by exact prefixLift 1701605
  have htrace : WordTrace (prefixWord ++ tailWord_1701605) baseStart_1701605 baseEnd_1701605 := by
    simpa [prefixWord, tailWord_1701605, baseEnd_1701605] using wordTrace_append hprefix tailTrace_1701605
  have hstable : (prefixWord ++ tailWord_1701605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701605).length < 2 ^ (prefixWord ++ tailWord_1701605).sum := by decide
  have hdescent : baseEnd_1701605 < baseStart_1701605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701615 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 3]
def baseStart_1701615 : Nat := 118140960795 + 1701615 * 2 ^ 59
def prefixEnd_1701615 : Nat := 4983230072969 + 3 ^ 40 * 1701615 * 2
def baseEnd_1701615 : Nat := 873746383900465157186921

theorem tailTrace_1701615 : CollatzResearch.WordTrace tailWord_1701615 prefixEnd_1701615 873746383900465157186921 := by
  unfold tailWord_1701615
  simp only [CollatzResearch.WordTrace]
  refine ⟨62062997730346942550250299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41375331820231295033500199 62062997730346942550250299)
  ·
    refine ⟨93094496595520413825375449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62062997730346942550250299 93094496595520413825375449)
    ·
      refine ⟨69820872446640310369031587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93094496595520413825375449 69820872446640310369031587)
      ·
        refine ⟨104731308669960465553547381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69820872446640310369031587 104731308669960465553547381)
        ·
          refine ⟨9818560187808793645645067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104731308669960465553547381 9818560187808793645645067)
          ·
            refine ⟨14727840281713190468467601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9818560187808793645645067 14727840281713190468467601)
            ·
              refine ⟨11045880211284892851350701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14727840281713190468467601 11045880211284892851350701)
              ·
                refine ⟨4142205079231834819256513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11045880211284892851350701 4142205079231834819256513)
                ·
                  refine ⟨3106653809423876114442385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4142205079231834819256513 3106653809423876114442385)
                  ·
                    refine ⟨2329990357067907085831789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3106653809423876114442385 2329990357067907085831789)
                    ·
                      refine ⟨873746383900465157186921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2329990357067907085831789 873746383900465157186921)
                      ·
                        rfl

theorem cell23_1701615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 3].length) (baseStart_1701615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701615 prefixEnd_1701615 := by exact prefixLift 1701615
  have htrace : WordTrace (prefixWord ++ tailWord_1701615) baseStart_1701615 baseEnd_1701615 := by
    simpa [prefixWord, tailWord_1701615, baseEnd_1701615] using wordTrace_append hprefix tailTrace_1701615
  have hstable : (prefixWord ++ tailWord_1701615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701615).length < 2 ^ (prefixWord ++ tailWord_1701615).sum := by decide
  have hdescent : baseEnd_1701615 < baseStart_1701615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701618 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 10]
def baseStart_1701618 : Nat := 118140960795 + 1701618 * 2 ^ 59
def prefixEnd_1701618 : Nat := 4983230072969 + 3 ^ 40 * 1701618 * 2
def baseEnd_1701618 : Nat := 97083102704714293938823

theorem tailTrace_1701618 : CollatzResearch.WordTrace tailWord_1701618 prefixEnd_1701618 97083102704714293938823 := by
  unfold tailWord_1701618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15515776787334018515652377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41375404766224049375073005 15515776787334018515652377)
  ·
    refine ⟨11636832590500513886739283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15515776787334018515652377 11636832590500513886739283)
    ·
      refine ⟨17455248885750770830108925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11636832590500513886739283 17455248885750770830108925)
      ·
        refine ⟨6545718332156539061290847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17455248885750770830108925 6545718332156539061290847)
        ·
          refine ⟨9818577498234808591936271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545718332156539061290847 9818577498234808591936271)
          ·
            refine ⟨14727866247352212887904407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9818577498234808591936271 14727866247352212887904407)
            ·
              refine ⟨22091799371028319331856611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14727866247352212887904407 22091799371028319331856611)
              ·
                refine ⟨33137699056542478997784917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22091799371028319331856611 33137699056542478997784917)
                ·
                  refine ⟨97083102704714293938823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 33137699056542478997784917 97083102704714293938823)
                  ·
                    rfl

theorem cell23_1701618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_1701618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701618 prefixEnd_1701618 := by exact prefixLift 1701618
  have htrace : WordTrace (prefixWord ++ tailWord_1701618) baseStart_1701618 baseEnd_1701618 := by
    simpa [prefixWord, tailWord_1701618, baseEnd_1701618] using wordTrace_append hprefix tailTrace_1701618
  have hstable : (prefixWord ++ tailWord_1701618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701618).length < 2 ^ (prefixWord ++ tailWord_1701618).sum := by decide
  have hdescent : baseEnd_1701618 < baseStart_1701618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701639 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 3, 4]
def baseStart_1701639 : Nat := 118140960795 + 1701639 * 2 ^ 59
def prefixEnd_1701639 : Nat := 4983230072969 + 3 ^ 40 * 1701639 * 2
def baseEnd_1701639 : Nat := 291252902478724354428937

theorem tailTrace_1701639 : CollatzResearch.WordTrace tailWord_1701639 prefixEnd_1701639 291252902478724354428937 := by
  unfold tailWord_1701639
  simp only [CollatzResearch.WordTrace]
  refine ⟨62063873082259994649123971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41375915388173329766082647 62063873082259994649123971)
  ·
    refine ⟨93095809623389991973685957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62063873082259994649123971 93095809623389991973685957)
    ·
      refine ⟨17455464304385623495066117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93095809623389991973685957 17455464304385623495066117)
      ·
        refine ⟨3272899557072304405324897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17455464304385623495066117 3272899557072304405324897)
        ·
          refine ⟨2454674667804228303993673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3272899557072304405324897 2454674667804228303993673)
          ·
            refine ⟨1841006000853171227995255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2454674667804228303993673 1841006000853171227995255)
            ·
              refine ⟨2761509001279756841992883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841006000853171227995255 2761509001279756841992883)
              ·
                refine ⟨4142263501919635262989325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2761509001279756841992883 4142263501919635262989325)
                ·
                  refine ⟨1553348813219863223620997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4142263501919635262989325 1553348813219863223620997)
                  ·
                    refine ⟨291252902478724354428937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1553348813219863223620997 291252902478724354428937)
                    ·
                      rfl

theorem cell23_1701639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_1701639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701639 prefixEnd_1701639 := by exact prefixLift 1701639
  have htrace : WordTrace (prefixWord ++ tailWord_1701639) baseStart_1701639 baseEnd_1701639 := by
    simpa [prefixWord, tailWord_1701639, baseEnd_1701639] using wordTrace_append hprefix tailTrace_1701639
  have hstable : (prefixWord ++ tailWord_1701639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701639).length < 2 ^ (prefixWord ++ tailWord_1701639).sum := by decide
  have hdescent : baseEnd_1701639 < baseStart_1701639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701665 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 3, 5]
def baseStart_1701665 : Nat := 118140960795 + 1701665 * 2 ^ 59
def prefixEnd_1701665 : Nat := 4983230072969 + 3 ^ 40 * 1701665 * 2
def baseEnd_1701665 : Nat := 291257352644396653853897

theorem tailTrace_1701665 : CollatzResearch.WordTrace tailWord_1701665 prefixEnd_1701665 291257352644396653853897 := by
  unfold tailWord_1701665
  simp only [CollatzResearch.WordTrace]
  refine ⟨62064821380165801089570449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41376547586777200726380299 62064821380165801089570449)
  ·
    refine ⟨46548616035124350817177837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62064821380165801089570449 46548616035124350817177837)
    ·
      refine ⟨17455731013171631556441689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46548616035124350817177837 17455731013171631556441689)
      ·
        refine ⟨13091798259878723667331267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17455731013171631556441689 13091798259878723667331267)
        ·
          refine ⟨19637697389818085500996901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13091798259878723667331267 19637697389818085500996901)
          ·
            refine ⟨3682068260590891031436919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19637697389818085500996901 3682068260590891031436919)
            ·
              refine ⟨5523102390886336547155379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682068260590891031436919 5523102390886336547155379)
              ·
                refine ⟨8284653586329504820733069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523102390886336547155379 8284653586329504820733069)
                ·
                  refine ⟨3106745094873564307774901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8284653586329504820733069 3106745094873564307774901)
                  ·
                    refine ⟨291257352644396653853897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3106745094873564307774901 291257352644396653853897)
                    ·
                      rfl

theorem cell23_1701665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_1701665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701665 prefixEnd_1701665 := by exact prefixLift 1701665
  have htrace : WordTrace (prefixWord ++ tailWord_1701665) baseStart_1701665 baseEnd_1701665 := by
    simpa [prefixWord, tailWord_1701665, baseEnd_1701665] using wordTrace_append hprefix tailTrace_1701665
  have hstable : (prefixWord ++ tailWord_1701665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701665).length < 2 ^ (prefixWord ++ tailWord_1701665).sum := by decide
  have hdescent : baseEnd_1701665 < baseStart_1701665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701705 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 5, 2, 3]
def baseStart_1701705 : Nat := 118140960795 + 1701705 * 2 ^ 59
def prefixEnd_1701705 : Nat := 4983230072969 + 3 ^ 40 * 1701705 * 2
def baseEnd_1701705 : Nat := 873792597159369805061507

theorem tailTrace_1701705 : CollatzResearch.WordTrace tailWord_1701705 prefixEnd_1701705 873792597159369805061507 := by
  unfold tailWord_1701705
  simp only [CollatzResearch.WordTrace]
  refine ⟨62066280300020887921026569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41377520200013925280684379 62066280300020887921026569)
  ·
    refine ⟨46549710225015665940769927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62066280300020887921026569 46549710225015665940769927)
    ·
      refine ⟨69824565337523498911154891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46549710225015665940769927 69824565337523498911154891)
      ·
        refine ⟨104736848006285248366732337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69824565337523498911154891 104736848006285248366732337)
        ·
          refine ⟨78552636004713936275049253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104736848006285248366732337 78552636004713936275049253)
          ·
            refine ⟨14728619250883863051571735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78552636004713936275049253 14728619250883863051571735)
            ·
              refine ⟨22092928876325794577357603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14728619250883863051571735 22092928876325794577357603)
              ·
                refine ⟨33139393314488691866036405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22092928876325794577357603 33139393314488691866036405)
                ·
                  refine ⟨3106818123233314862440913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33139393314488691866036405 3106818123233314862440913)
                  ·
                    refine ⟨2330113592424986146830685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3106818123233314862440913 2330113592424986146830685)
                    ·
                      refine ⟨873792597159369805061507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2330113592424986146830685 873792597159369805061507)
                      ·
                        rfl

theorem cell23_1701705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2, 3].length) (baseStart_1701705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701705 prefixEnd_1701705 := by exact prefixLift 1701705
  have htrace : WordTrace (prefixWord ++ tailWord_1701705) baseStart_1701705 baseEnd_1701705 := by
    simpa [prefixWord, tailWord_1701705, baseEnd_1701705] using wordTrace_append hprefix tailTrace_1701705
  have hstable : (prefixWord ++ tailWord_1701705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701705).length < 2 ^ (prefixWord ++ tailWord_1701705).sum := by decide
  have hdescent : baseEnd_1701705 < baseStart_1701705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701722 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3]
def baseStart_1701722 : Nat := 118140960795 + 1701722 * 2 ^ 59
def prefixEnd_1701722 : Nat := 4983230072969 + 3 ^ 40 * 1701722 * 2
def baseEnd_1701722 : Nat := 873801326330496238548929

theorem tailTrace_1701722 : CollatzResearch.WordTrace tailWord_1701722 prefixEnd_1701722 873801326330496238548929 := by
  unfold tailWord_1701722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15516725085239824956098855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41377933560639533216263613 15516725085239824956098855)
  ·
    refine ⟨23275087627859737434148283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15516725085239824956098855 23275087627859737434148283)
    ·
      refine ⟨34912631441789606151222425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23275087627859737434148283 34912631441789606151222425)
      ·
        refine ⟨26184473581342204613416819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34912631441789606151222425 26184473581342204613416819)
        ·
          refine ⟨39276710372013306920125229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26184473581342204613416819 39276710372013306920125229)
          ·
            refine ⟨14728766389504990095046961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39276710372013306920125229 14728766389504990095046961)
            ·
              refine ⟨11046574792128742571285221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14728766389504990095046961 11046574792128742571285221)
              ·
                refine ⟨2071232773524139232115979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11046574792128742571285221 2071232773524139232115979)
                ·
                  refine ⟨3106849160286208848173969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2071232773524139232115979 3106849160286208848173969)
                  ·
                    refine ⟨2330136870214656636130477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3106849160286208848173969 2330136870214656636130477)
                    ·
                      refine ⟨873801326330496238548929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2330136870214656636130477 873801326330496238548929)
                      ·
                        rfl

theorem cell23_1701722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_1701722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701722 prefixEnd_1701722 := by exact prefixLift 1701722
  have htrace : WordTrace (prefixWord ++ tailWord_1701722) baseStart_1701722 baseEnd_1701722 := by
    simpa [prefixWord, tailWord_1701722, baseEnd_1701722] using wordTrace_append hprefix tailTrace_1701722
  have hstable : (prefixWord ++ tailWord_1701722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701722).length < 2 ^ (prefixWord ++ tailWord_1701722).sum := by decide
  have hdescent : baseEnd_1701722 < baseStart_1701722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701792 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 3, 4, 2]
def baseStart_1701792 : Nat := 118140960795 + 1701792 * 2 ^ 59
def prefixEnd_1701792 : Nat := 4983230072969 + 3 ^ 40 * 1701792 * 2
def baseEnd_1701792 : Nat := 873837269976310964673607

theorem tailTrace_1701792 : CollatzResearch.WordTrace tailWord_1701792 prefixEnd_1701792 873837269976310964673607 := by
  unfold tailWord_1701792
  simp only [CollatzResearch.WordTrace]
  refine ⟨31034726725352850889721815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41379635633803801186295753 31034726725352850889721815)
  ·
    refine ⟨46552090088029276334582723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31034726725352850889721815 46552090088029276334582723)
    ·
      refine ⟨69828135132043914501874085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46552090088029276334582723 69828135132043914501874085)
      ·
        refine ⟨13092775337258233969101391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69828135132043914501874085 13092775337258233969101391)
        ·
          refine ⟨19639163005887350953652087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13092775337258233969101391 19639163005887350953652087)
          ·
            refine ⟨29458744508831026430478131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19639163005887350953652087 29458744508831026430478131)
            ·
              refine ⟨44188116763246539645717197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29458744508831026430478131 44188116763246539645717197)
              ·
                refine ⟨16570543786217452367143949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44188116763246539645717197 16570543786217452367143949)
                ·
                  refine ⟨6213953919831544637678981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16570543786217452367143949 6213953919831544637678981)
                  ·
                    refine ⟨1165116359968414619564809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6213953919831544637678981 1165116359968414619564809)
                    ·
                      refine ⟨873837269976310964673607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165116359968414619564809 873837269976310964673607)
                      ·
                        rfl

theorem cell23_1701792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_1701792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701792 prefixEnd_1701792 := by exact prefixLift 1701792
  have htrace : WordTrace (prefixWord ++ tailWord_1701792) baseStart_1701792 baseEnd_1701792 := by
    simpa [prefixWord, tailWord_1701792, baseEnd_1701792] using wordTrace_append hprefix tailTrace_1701792
  have hstable : (prefixWord ++ tailWord_1701792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701792).length < 2 ^ (prefixWord ++ tailWord_1701792).sum := by decide
  have hdescent : baseEnd_1701792 < baseStart_1701792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701795 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1701795 : Nat := 118140960795 + 1701795 * 2 ^ 59
def prefixEnd_1701795 : Nat := 4983230072969 + 3 ^ 40 * 1701795 * 2
def baseEnd_1701795 : Nat := 873838810418274452936093

theorem tailTrace_1701795 : CollatzResearch.WordTrace tailWord_1701795 prefixEnd_1701795 873838810418274452936093 := by
  unfold tailWord_1701795
  simp only [CollatzResearch.WordTrace]
  refine ⟨62069562869694833291802839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41379708579796555527868559 62069562869694833291802839)
  ·
    refine ⟨93104344304542249937704259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62069562869694833291802839 93104344304542249937704259)
    ·
      refine ⟨139656516456813374906556389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93104344304542249937704259 139656516456813374906556389)
      ·
        refine ⟨26185596835652507794979323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139656516456813374906556389 26185596835652507794979323)
        ·
          refine ⟨39278395253478761692468985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26185596835652507794979323 39278395253478761692468985)
          ·
            refine ⟨29458796440109071269351739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39278395253478761692468985 29458796440109071269351739)
            ·
              refine ⟨44188194660163606904027609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29458796440109071269351739 44188194660163606904027609)
              ·
                refine ⟨33141145995122705178020707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44188194660163606904027609 33141145995122705178020707)
                ·
                  refine ⟨49711718992684057767031061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33141145995122705178020707 49711718992684057767031061)
                  ·
                    refine ⟨2330236827782065207829581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49711718992684057767031061 2330236827782065207829581)
                    ·
                      refine ⟨873838810418274452936093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2330236827782065207829581 873838810418274452936093)
                      ·
                        rfl

theorem cell23_1701795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1701795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701795 prefixEnd_1701795 := by exact prefixLift 1701795
  have htrace : WordTrace (prefixWord ++ tailWord_1701795) baseStart_1701795 baseEnd_1701795 := by
    simpa [prefixWord, tailWord_1701795, baseEnd_1701795] using wordTrace_append hprefix tailTrace_1701795
  have hstable : (prefixWord ++ tailWord_1701795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701795).length < 2 ^ (prefixWord ++ tailWord_1701795).sum := by decide
  have hdescent : baseEnd_1701795 < baseStart_1701795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701820 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1701820 : Nat := 118140960795 + 1701820 * 2 ^ 59
def prefixEnd_1701820 : Nat := 4983230072969 + 3 ^ 40 * 1701820 * 2
def baseEnd_1701820 : Nat := 873851647434636855123479

theorem tailTrace_1701820 : CollatzResearch.WordTrace tailWord_1701820 prefixEnd_1701820 873851647434636855123479 := by
  unfold tailWord_1701820
  simp only [CollatzResearch.WordTrace]
  refine ⟨31035237347302131280731457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41380316463069508374308609 31035237347302131280731457)
  ·
    refine ⟨23276428010476598460548593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31035237347302131280731457 23276428010476598460548593)
    ·
      refine ⟨17457321007857448845411445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23276428010476598460548593 17457321007857448845411445)
      ·
        refine ⟨1636623844486635829257323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17457321007857448845411445 1636623844486635829257323)
        ·
          refine ⟨2454935766729953743885985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636623844486635829257323 2454935766729953743885985)
          ·
            refine ⟨1841201825047465307914489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2454935766729953743885985 1841201825047465307914489)
            ·
              refine ⟨1380901368785598980935867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1841201825047465307914489 1380901368785598980935867)
              ·
                refine ⟨2071352053178398471403801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380901368785598980935867 2071352053178398471403801)
                ·
                  refine ⟨1553514039883798853552851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2071352053178398471403801 1553514039883798853552851)
                  ·
                    refine ⟨2330271059825698280329277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1553514039883798853552851 2330271059825698280329277)
                    ·
                      refine ⟨873851647434636855123479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2330271059825698280329277 873851647434636855123479)
                      ·
                        rfl

theorem cell23_1701820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1701820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701820 prefixEnd_1701820 := by exact prefixLift 1701820
  have htrace : WordTrace (prefixWord ++ tailWord_1701820) baseStart_1701820 baseEnd_1701820 := by
    simpa [prefixWord, tailWord_1701820, baseEnd_1701820] using wordTrace_append hprefix tailTrace_1701820
  have hstable : (prefixWord ++ tailWord_1701820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701820).length < 2 ^ (prefixWord ++ tailWord_1701820).sum := by decide
  have hdescent : baseEnd_1701820 < baseStart_1701820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701922 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 8]
def baseStart_1701922 : Nat := 118140960795 + 1701922 * 2 ^ 59
def prefixEnd_1701922 : Nat := 4983230072969 + 3 ^ 40 * 1701922 * 2
def baseEnd_1701922 : Nat := 97100446940155050672001

theorem tailTrace_1701922 : CollatzResearch.WordTrace tailWord_1701922 prefixEnd_1701922 97100446940155050672001 := by
  unfold tailWord_1701922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518548735058683495419005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41382796626823155987784013 15518548735058683495419005)
  ·
    refine ⟨5819455775647006310782127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15518548735058683495419005 5819455775647006310782127)
    ·
      refine ⟨8729183663470509466173191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5819455775647006310782127 8729183663470509466173191)
      ·
        refine ⟨13093775495205764199259787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8729183663470509466173191 13093775495205764199259787)
        ·
          refine ⟨19640663242808646298889681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13093775495205764199259787 19640663242808646298889681)
          ·
            refine ⟨14730497432106484724167261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19640663242808646298889681 14730497432106484724167261)
            ·
              refine ⟨5523936537039931771562723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14730497432106484724167261 5523936537039931771562723)
              ·
                refine ⟨8285904805559897657344085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523936537039931771562723 8285904805559897657344085)
                ·
                  refine ⟨97100446940155050672001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8285904805559897657344085 97100446940155050672001)
                  ·
                    rfl

theorem cell23_1701922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_1701922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701922 prefixEnd_1701922 := by exact prefixLift 1701922
  have htrace : WordTrace (prefixWord ++ tailWord_1701922) baseStart_1701922 baseEnd_1701922 := by
    simpa [prefixWord, tailWord_1701922, baseEnd_1701922] using wordTrace_append hprefix tailTrace_1701922
  have hstable : (prefixWord ++ tailWord_1701922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701922).length < 2 ^ (prefixWord ++ tailWord_1701922).sum := by decide
  have hdescent : baseEnd_1701922 < baseStart_1701922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701935 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 2, 9]
def baseStart_1701935 : Nat := 118140960795 + 1701935 * 2 ^ 59
def prefixEnd_1701935 : Nat := 4983230072969 + 3 ^ 40 * 1701935 * 2
def baseEnd_1701935 : Nat := 291303565903301301728483

theorem tailTrace_1701935 : CollatzResearch.WordTrace tailWord_1701935 prefixEnd_1701935 291303565903301301728483 := by
  unfold tailWord_1701935
  simp only [CollatzResearch.WordTrace]
  refine ⟨62074669089187637201899259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41383112726125091467932839 62074669089187637201899259)
  ·
    refine ⟨93112003633781455802848889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62074669089187637201899259 93112003633781455802848889)
    ·
      refine ⟨69834002725336091852136667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93112003633781455802848889 69834002725336091852136667)
      ·
        refine ⟨104751004088004137778205001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69834002725336091852136667 104751004088004137778205001)
        ·
          refine ⟨78563253066003103333653751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104751004088004137778205001 78563253066003103333653751)
          ·
            refine ⟨117844879599004655000480627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78563253066003103333653751 117844879599004655000480627)
            ·
              refine ⟨176767319398506982500720941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117844879599004655000480627 176767319398506982500720941)
              ·
                refine ⟨66287744774440118437770353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176767319398506982500720941 66287744774440118437770353)
                ·
                  refine ⟨49715808580830088828327765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66287744774440118437770353 49715808580830088828327765)
                  ·
                    refine ⟨291303565903301301728483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 49715808580830088828327765 291303565903301301728483)
                    ·
                      rfl

theorem cell23_1701935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_1701935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701935 prefixEnd_1701935 := by exact prefixLift 1701935
  have htrace : WordTrace (prefixWord ++ tailWord_1701935) baseStart_1701935 baseEnd_1701935 := by
    simpa [prefixWord, tailWord_1701935, baseEnd_1701935] using wordTrace_append hprefix tailTrace_1701935
  have hstable : (prefixWord ++ tailWord_1701935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701935).length < 2 ^ (prefixWord ++ tailWord_1701935).sum := by decide
  have hdescent : baseEnd_1701935 < baseStart_1701935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701959 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 1, 5, 2]
def baseStart_1701959 : Nat := 118140960795 + 1701959 * 2 ^ 59
def prefixEnd_1701959 : Nat := 4983230072969 + 3 ^ 40 * 1701959 * 2
def baseEnd_1701959 : Nat := 873923021245611811285339

theorem tailTrace_1701959 : CollatzResearch.WordTrace tailWord_1701959 prefixEnd_1701959 873923021245611811285339 := by
  unfold tailWord_1701959
  simp only [CollatzResearch.WordTrace]
  refine ⟨62075544441100689300772931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41383696294067126200515287 62075544441100689300772931)
  ·
    refine ⟨93113316661651033951159397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62075544441100689300772931 93113316661651033951159397)
    ·
      refine ⟨17458746874059568865842387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93113316661651033951159397 17458746874059568865842387)
      ·
        refine ⟨26188120311089353298763581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17458746874059568865842387 26188120311089353298763581)
        ·
          refine ⟨9820545116658507487036343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26188120311089353298763581 9820545116658507487036343)
          ·
            refine ⟨14730817674987761230554515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9820545116658507487036343 14730817674987761230554515)
            ·
              refine ⟨22096226512481641845831773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14730817674987761230554515 22096226512481641845831773)
              ·
                refine ⟨8286084942180615692186915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22096226512481641845831773 8286084942180615692186915)
                ·
                  refine ⟨12429127413270923538280373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286084942180615692186915 12429127413270923538280373)
                  ·
                    refine ⟨1165230694994149081713785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12429127413270923538280373 1165230694994149081713785)
                    ·
                      refine ⟨873923021245611811285339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165230694994149081713785 873923021245611811285339)
                      ·
                        rfl

theorem cell23_1701959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_1701959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701959 prefixEnd_1701959 := by exact prefixLift 1701959
  have htrace : WordTrace (prefixWord ++ tailWord_1701959) baseStart_1701959 baseEnd_1701959 := by
    simpa [prefixWord, tailWord_1701959, baseEnd_1701959] using wordTrace_append hprefix tailTrace_1701959
  have hstable : (prefixWord ++ tailWord_1701959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701959).length < 2 ^ (prefixWord ++ tailWord_1701959).sum := by decide
  have hdescent : baseEnd_1701959 < baseStart_1701959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701976 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 2, 3, 2]
def baseStart_1701976 : Nat := 118140960795 + 1701976 * 2 ^ 59
def prefixEnd_1701976 : Nat := 4983230072969 + 3 ^ 40 * 1701976 * 2
def baseEnd_1701976 : Nat := 873931750416738244772761

theorem tailTrace_1701976 : CollatzResearch.WordTrace tailWord_1701976 prefixEnd_1701976 873931750416738244772761 := by
  unfold tailWord_1701976
  simp only [CollatzResearch.WordTrace]
  refine ⟨31038082241019550602070891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41384109654692734136094521 31038082241019550602070891)
  ·
    refine ⟨46557123361529325903106337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31038082241019550602070891 46557123361529325903106337)
    ·
      refine ⟨34917842521146994427329753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46557123361529325903106337 34917842521146994427329753)
      ·
        refine ⟨26188381890860245820497315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34917842521146994427329753 26188381890860245820497315)
        ·
          refine ⟨39282572836290368730745973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26188381890860245820497315 39282572836290368730745973)
          ·
            refine ⟨3682741203402222068507435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39282572836290368730745973 3682741203402222068507435)
            ·
              refine ⟨5524111805103333102761153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682741203402222068507435 5524111805103333102761153)
              ·
                refine ⟨4143083853827499827070865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5524111805103333102761153 4143083853827499827070865)
                ·
                  refine ⟨3107312890370624870303149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4143083853827499827070865 3107312890370624870303149)
                  ·
                    refine ⟨1165242333888984326363681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3107312890370624870303149 1165242333888984326363681)
                    ·
                      refine ⟨873931750416738244772761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165242333888984326363681 873931750416738244772761)
                      ·
                        rfl

theorem cell23_1701976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_1701976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1701976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1701976 prefixEnd_1701976 := by exact prefixLift 1701976
  have htrace : WordTrace (prefixWord ++ tailWord_1701976) baseStart_1701976 baseEnd_1701976 := by
    simpa [prefixWord, tailWord_1701976, baseEnd_1701976] using wordTrace_append hprefix tailTrace_1701976
  have hstable : (prefixWord ++ tailWord_1701976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701976).length < 2 ^ (prefixWord ++ tailWord_1701976).sum := by decide
  have hdescent : baseEnd_1701976 < baseStart_1701976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702006 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1702006 : Nat := 118140960795 + 1702006 * 2 ^ 59
def prefixEnd_1702006 : Nat := 4983230072969 + 3 ^ 40 * 1702006 * 2
def baseEnd_1702006 : Nat := 873947154836373127397623

theorem tailTrace_1702006 : CollatzResearch.WordTrace tailWord_1702006 prefixEnd_1702006 873947154836373127397623 := by
  unfold tailWord_1702006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3879828666995651020483367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41384839114620277551822581 3879828666995651020483367)
  ·
    refine ⟨5819743000493476530725051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3879828666995651020483367 5819743000493476530725051)
    ·
      refine ⟨8729614500740214796087577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5819743000493476530725051 8729614500740214796087577)
      ·
        refine ⟨6547210875555161097065683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8729614500740214796087577 6547210875555161097065683)
        ·
          refine ⟨9820816313332741645598525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6547210875555161097065683 9820816313332741645598525)
          ·
            refine ⟨3682806117499778117099447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9820816313332741645598525 3682806117499778117099447)
            ·
              refine ⟨5524209176249667175649171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682806117499778117099447 5524209176249667175649171)
              ·
                refine ⟨8286313764374500763473757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524209176249667175649171 8286313764374500763473757)
                ·
                  refine ⟨3107367661640437786302659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8286313764374500763473757 3107367661640437786302659)
                  ·
                    refine ⟨4661051492460656679453989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3107367661640437786302659 4661051492460656679453989)
                    ·
                      refine ⟨873947154836373127397623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4661051492460656679453989 873947154836373127397623)
                      ·
                        rfl

theorem cell23_1702006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1702006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702006 prefixEnd_1702006 := by exact prefixLift 1702006
  have htrace : WordTrace (prefixWord ++ tailWord_1702006) baseStart_1702006 baseEnd_1702006 := by
    simpa [prefixWord, tailWord_1702006, baseEnd_1702006] using wordTrace_append hprefix tailTrace_1702006
  have hstable : (prefixWord ++ tailWord_1702006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702006).length < 2 ^ (prefixWord ++ tailWord_1702006).sum := by decide
  have hdescent : baseEnd_1702006 < baseStart_1702006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702012 : List Nat := [2, 2, 2, 1, 1, 4, 2, 9]
def baseStart_1702012 : Nat := 118140960795 + 1702012 * 2 ^ 59
def prefixEnd_1702012 : Nat := 4983230072969 + 3 ^ 40 * 1702012 * 2
def baseEnd_1702012 : Nat := 32368527248900003848985

theorem tailTrace_1702012 : CollatzResearch.WordTrace tailWord_1702012 prefixEnd_1702012 32368527248900003848985 := by
  unfold tailWord_1702012
  simp only [CollatzResearch.WordTrace]
  refine ⟨31038738754954339676226145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41384985006605786234968193 31038738754954339676226145)
  ·
    refine ⟨23279054066215754757169609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31038738754954339676226145 23279054066215754757169609)
    ·
      refine ⟨17459290549661816067877207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23279054066215754757169609 17459290549661816067877207)
      ·
        refine ⟨26188935824492724101815811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17459290549661816067877207 26188935824492724101815811)
        ·
          refine ⟨39283403736739086152723717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26188935824492724101815811 39283403736739086152723717)
          ·
            refine ⟨7365638200638578653635697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39283403736739086152723717 7365638200638578653635697)
            ·
              refine ⟨5524228650478933990226773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7365638200638578653635697 5524228650478933990226773)
              ·
                refine ⟨32368527248900003848985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5524228650478933990226773 32368527248900003848985)
                ·
                  rfl

theorem cell23_1702012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 9].length) (baseStart_1702012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702012 prefixEnd_1702012 := by exact prefixLift 1702012
  have htrace : WordTrace (prefixWord ++ tailWord_1702012) baseStart_1702012 baseEnd_1702012 := by
    simpa [prefixWord, tailWord_1702012, baseEnd_1702012] using wordTrace_append hprefix tailTrace_1702012
  have hstable : (prefixWord ++ tailWord_1702012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702012).length < 2 ^ (prefixWord ++ tailWord_1702012).sum := by decide
  have hdescent : baseEnd_1702012 < baseStart_1702012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702019 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 4]
def baseStart_1702019 : Nat := 118140960795 + 1702019 * 2 ^ 59
def prefixEnd_1702019 : Nat := 4983230072969 + 3 ^ 40 * 1702019 * 2
def baseEnd_1702019 : Nat := 873953830084881576535063

theorem tailTrace_1702019 : CollatzResearch.WordTrace tailWord_1702019 prefixEnd_1702019 873953830084881576535063 := by
  unfold tailWord_1702019
  simp only [CollatzResearch.WordTrace]
  refine ⟨62077732820883319547957111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41385155213922213031971407 62077732820883319547957111)
  ·
    refine ⟨93116599231324979321935667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62077732820883319547957111 93116599231324979321935667)
    ·
      refine ⟨139674898846987468982903501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93116599231324979321935667 139674898846987468982903501)
      ·
        refine ⟨52378087067620300868588813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139674898846987468982903501 52378087067620300868588813)
        ·
          refine ⟨19641782650357612825720805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52378087067620300868588813 19641782650357612825720805)
          ·
            refine ⟨3682834246942052404822651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19641782650357612825720805 3682834246942052404822651)
            ·
              refine ⟨5524251370413078607233977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682834246942052404822651 5524251370413078607233977)
              ·
                refine ⟨4143188527809808955425483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5524251370413078607233977 4143188527809808955425483)
                ·
                  refine ⟨6214782791714713433138225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4143188527809808955425483 6214782791714713433138225)
                  ·
                    refine ⟨4661087093786035074853669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6214782791714713433138225 4661087093786035074853669)
                    ·
                      refine ⟨873953830084881576535063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4661087093786035074853669 873953830084881576535063)
                      ·
                        rfl

theorem cell23_1702019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_1702019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702019 prefixEnd_1702019 := by exact prefixLift 1702019
  have htrace : WordTrace (prefixWord ++ tailWord_1702019) baseStart_1702019 baseEnd_1702019 := by
    simpa [prefixWord, tailWord_1702019, baseEnd_1702019] using wordTrace_append hprefix tailTrace_1702019
  have hstable : (prefixWord ++ tailWord_1702019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702019).length < 2 ^ (prefixWord ++ tailWord_1702019).sum := by decide
  have hdescent : baseEnd_1702019 < baseStart_1702019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702026 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_1702026 : Nat := 118140960795 + 1702026 * 2 ^ 59
def prefixEnd_1702026 : Nat := 4983230072969 + 3 ^ 40 * 1702026 * 2
def baseEnd_1702026 : Nat := 873957424449463049147531

theorem tailTrace_1702026 : CollatzResearch.WordTrace tailWord_1702026 prefixEnd_1702026 873957424449463049147531 := by
  unfold tailWord_1702026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15519497032964489935865483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41385325421238639828974621 15519497032964489935865483)
  ·
    refine ⟨23279245549446734903798225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15519497032964489935865483 23279245549446734903798225)
    ·
      refine ⟨17459434162085051177848669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23279245549446734903798225 17459434162085051177848669)
      ·
        refine ⟨6547287810781894191693251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17459434162085051177848669 6547287810781894191693251)
        ·
          refine ⟨9820931716172841287539877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6547287810781894191693251 9820931716172841287539877)
          ·
            refine ⟨1841424696782407741413727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9820931716172841287539877 1841424696782407741413727)
            ·
              refine ⟨2762137045173611612120591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841424696782407741413727 2762137045173611612120591)
              ·
                refine ⟨4143205567760417418180887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762137045173611612120591 4143205567760417418180887)
                ·
                  refine ⟨6214808351640626127271331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4143205567760417418180887 6214808351640626127271331)
                  ·
                    refine ⟨9322212527460939190906997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6214808351640626127271331 9322212527460939190906997)
                    ·
                      refine ⟨873957424449463049147531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9322212527460939190906997 873957424449463049147531)
                      ·
                        rfl

theorem cell23_1702026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_1702026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702026 prefixEnd_1702026 := by exact prefixLift 1702026
  have htrace : WordTrace (prefixWord ++ tailWord_1702026) baseStart_1702026 baseEnd_1702026 := by
    simpa [prefixWord, tailWord_1702026, baseEnd_1702026] using wordTrace_append hprefix tailTrace_1702026
  have hstable : (prefixWord ++ tailWord_1702026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702026).length < 2 ^ (prefixWord ++ tailWord_1702026).sum := by decide
  have hdescent : baseEnd_1702026 < baseStart_1702026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702066 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2]
def baseStart_1702066 : Nat := 118140960795 + 1702066 * 2 ^ 59
def prefixEnd_1702066 : Nat := 4983230072969 + 3 ^ 40 * 1702066 * 2
def baseEnd_1702066 : Nat := 873977963675642892647347

theorem tailTrace_1702066 : CollatzResearch.WordTrace tailWord_1702066 prefixEnd_1702066 873977963675642892647347 := by
  unfold tailWord_1702066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15519861762928261643729513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41386298034475364383278701 15519861762928261643729513)
  ·
    refine ⟨11639896322196196232797135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15519861762928261643729513 11639896322196196232797135)
    ·
      refine ⟨17459844483294294349195703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11639896322196196232797135 17459844483294294349195703)
      ·
        refine ⟨26189766724941441523793555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17459844483294294349195703 26189766724941441523793555)
        ·
          refine ⟨39284650087412162285690333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26189766724941441523793555 39284650087412162285690333)
          ·
            refine ⟨14731743782779560857133875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39284650087412162285690333 14731743782779560857133875)
            ·
              refine ⟨22097615674169341285700813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14731743782779560857133875 22097615674169341285700813)
              ·
                refine ⟨8286605877813502982137805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22097615674169341285700813 8286605877813502982137805)
                ·
                  refine ⟨3107477204180063618301677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8286605877813502982137805 3107477204180063618301677)
                  ·
                    refine ⟨1165303951567523856863129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3107477204180063618301677 1165303951567523856863129)
                    ·
                      refine ⟨873977963675642892647347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165303951567523856863129 873977963675642892647347)
                      ·
                        rfl

theorem cell23_1702066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_1702066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702066 prefixEnd_1702066 := by exact prefixLift 1702066
  have htrace : WordTrace (prefixWord ++ tailWord_1702066) baseStart_1702066 baseEnd_1702066 := by
    simpa [prefixWord, tailWord_1702066, baseEnd_1702066] using wordTrace_append hprefix tailTrace_1702066
  have hstable : (prefixWord ++ tailWord_1702066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702066).length < 2 ^ (prefixWord ++ tailWord_1702066).sum := by decide
  have hdescent : baseEnd_1702066 < baseStart_1702066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702072 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 1, 8]
def baseStart_1702072 : Nat := 118140960795 + 1702072 * 2 ^ 59
def prefixEnd_1702072 : Nat := 4983230072969 + 3 ^ 40 * 1702072 * 2
def baseEnd_1702072 : Nat := 291327014853189956390773

theorem tailTrace_1702072 : CollatzResearch.WordTrace tailWord_1702072 prefixEnd_1702072 291327014853189956390773 := by
  unfold tailWord_1702072
  simp only [CollatzResearch.WordTrace]
  refine ⟨31039832944845654799818235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41386443926460873066424313 31039832944845654799818235)
  ·
    refine ⟨46559749417268482199727353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31039832944845654799818235 46559749417268482199727353)
    ·
      refine ⟨34919812062951361649795515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46559749417268482199727353 34919812062951361649795515)
      ·
        refine ⟨52379718094427042474693273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34919812062951361649795515 52379718094427042474693273)
        ·
          refine ⟨39284788570820281856019955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52379718094427042474693273 39284788570820281856019955)
          ·
            refine ⟨58927182856230422784029933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39284788570820281856019955 58927182856230422784029933)
            ·
              refine ⟨22097693571086408544011225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58927182856230422784029933 22097693571086408544011225)
              ·
                refine ⟨16573270178314806408008419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22097693571086408544011225 16573270178314806408008419)
                ·
                  refine ⟨24859905267472209612012629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16573270178314806408008419 24859905267472209612012629)
                  ·
                    refine ⟨291327014853189956390773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24859905267472209612012629 291327014853189956390773)
                    ·
                      rfl

theorem cell23_1702072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_1702072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702072 prefixEnd_1702072 := by exact prefixLift 1702072
  have htrace : WordTrace (prefixWord ++ tailWord_1702072) baseStart_1702072 baseEnd_1702072 := by
    simpa [prefixWord, tailWord_1702072, baseEnd_1702072] using wordTrace_append hprefix tailTrace_1702072
  have hstable : (prefixWord ++ tailWord_1702072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702072).length < 2 ^ (prefixWord ++ tailWord_1702072).sum := by decide
  have hdescent : baseEnd_1702072 < baseStart_1702072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702129 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 1, 5, 3]
def baseStart_1702129 : Nat := 118140960795 + 1702129 * 2 ^ 59
def prefixEnd_1702129 : Nat := 4983230072969 + 3 ^ 40 * 1702129 * 2
def baseEnd_1702129 : Nat := 874010312956876146159557

theorem tailTrace_1702129 : CollatzResearch.WordTrace tailWord_1702129 prefixEnd_1702129 874010312956876146159557 := by
  unfold tailWord_1702129
  simp only [CollatzResearch.WordTrace]
  refine ⟨62081744850484808334461441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41387829900323205556307627 62081744850484808334461441)
  ·
    refine ⟨46561308637863606250846081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62081744850484808334461441 46561308637863606250846081)
    ·
      refine ⟨34920981478397704688134561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46561308637863606250846081 34920981478397704688134561)
      ·
        refine ⟨26190736108798278516100921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34920981478397704688134561 26190736108798278516100921)
        ·
          refine ⟨19643052081598708887075691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26190736108798278516100921 19643052081598708887075691)
          ·
            refine ⟨29464578122398063330613537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19643052081598708887075691 29464578122398063330613537)
            ·
              refine ⟨22098433591798547497960153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29464578122398063330613537 22098433591798547497960153)
              ·
                refine ⟨16573825193848910623470115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22098433591798547497960153 16573825193848910623470115)
                ·
                  refine ⟨24860737790773365935205173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16573825193848910623470115 24860737790773365935205173)
                  ·
                    refine ⟨2330694167885003056425485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24860737790773365935205173 2330694167885003056425485)
                    ·
                      refine ⟨874010312956876146159557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2330694167885003056425485 874010312956876146159557)
                      ·
                        rfl

theorem cell23_1702129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_1702129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702129 prefixEnd_1702129 := by exact prefixLift 1702129
  have htrace : WordTrace (prefixWord ++ tailWord_1702129) baseStart_1702129 baseEnd_1702129 := by
    simpa [prefixWord, tailWord_1702129, baseEnd_1702129] using wordTrace_append hprefix tailTrace_1702129
  have hstable : (prefixWord ++ tailWord_1702129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702129).length < 2 ^ (prefixWord ++ tailWord_1702129).sum := by decide
  have hdescent : baseEnd_1702129 < baseStart_1702129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702153 : List Nat := [1, 2, 1, 1, 3, 5, 3, 2, 5]
def baseStart_1702153 : Nat := 118140960795 + 1702153 * 2 ^ 59
def prefixEnd_1702153 : Nat := 4983230072969 + 3 ^ 40 * 1702153 * 2
def baseEnd_1702153 : Nat := 97113626276953783584383

theorem tailTrace_1702153 : CollatzResearch.WordTrace tailWord_1702153 prefixEnd_1702153 97113626276953783584383 := by
  unfold tailWord_1702153
  simp only [CollatzResearch.WordTrace]
  refine ⟨62082620202397860433335113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41388413468265240288890075 62082620202397860433335113)
  ·
    refine ⟨46561965151798395325001335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62082620202397860433335113 46561965151798395325001335)
    ·
      refine ⟨69842947727697592987502003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46561965151798395325001335 69842947727697592987502003)
      ·
        refine ⟨104764421591546389481253005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69842947727697592987502003 104764421591546389481253005)
        ·
          refine ⟨39286658096829896055469877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104764421591546389481253005 39286658096829896055469877)
          ·
            refine ⟨3683124196577802755200301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39286658096829896055469877 3683124196577802755200301)
            ·
              refine ⟨1381171573716676033200113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3683124196577802755200301 1381171573716676033200113)
              ·
                refine ⟨1035878680287507024900085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1381171573716676033200113 1035878680287507024900085)
                ·
                  refine ⟨97113626276953783584383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1035878680287507024900085 97113626276953783584383)
                  ·
                    rfl

theorem cell23_1702153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 5].length) (baseStart_1702153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702153 prefixEnd_1702153 := by exact prefixLift 1702153
  have htrace : WordTrace (prefixWord ++ tailWord_1702153) baseStart_1702153 baseEnd_1702153 := by
    simpa [prefixWord, tailWord_1702153, baseEnd_1702153] using wordTrace_append hprefix tailTrace_1702153
  have hstable : (prefixWord ++ tailWord_1702153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702153).length < 2 ^ (prefixWord ++ tailWord_1702153).sum := by decide
  have hdescent : baseEnd_1702153 < baseStart_1702153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702156 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 2, 5, 2]
def baseStart_1702156 : Nat := 118140960795 + 1702156 * 2 ^ 59
def prefixEnd_1702156 : Nat := 4983230072969 + 3 ^ 40 * 1702156 * 2
def baseEnd_1702156 : Nat := 874024176934547540521933

theorem tailTrace_1702156 : CollatzResearch.WordTrace tailWord_1702156 prefixEnd_1702156 874024176934547540521933 := by
  unfold tailWord_1702156
  simp only [CollatzResearch.WordTrace]
  refine ⟨31041364810693495972847161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41388486414257994630462881 31041364810693495972847161)
  ·
    refine ⟨23281023608020121979635371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31041364810693495972847161 23281023608020121979635371)
    ·
      refine ⟨34921535412030182969453057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23281023608020121979635371 34921535412030182969453057)
      ·
        refine ⟨26191151559022637227089793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34921535412030182969453057 26191151559022637227089793)
        ·
          refine ⟨19643363669266977920317345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26191151559022637227089793 19643363669266977920317345)
          ·
            refine ⟨14732522751950233440238009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19643363669266977920317345 14732522751950233440238009)
            ·
              refine ⟨11049392063962675080178507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14732522751950233440238009 11049392063962675080178507)
              ·
                refine ⟨16574088095944012620267761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11049392063962675080178507 16574088095944012620267761)
                ·
                  refine ⟨12430566071958009465200821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16574088095944012620267761 12430566071958009465200821)
                  ·
                    refine ⟨1165365569246063387362577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12430566071958009465200821 1165365569246063387362577)
                    ·
                      refine ⟨874024176934547540521933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165365569246063387362577 874024176934547540521933)
                      ·
                        rfl

theorem cell23_1702156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_1702156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702156 prefixEnd_1702156 := by exact prefixLift 1702156
  have htrace : WordTrace (prefixWord ++ tailWord_1702156) baseStart_1702156 baseEnd_1702156 := by
    simpa [prefixWord, tailWord_1702156, baseEnd_1702156] using wordTrace_append hprefix tailTrace_1702156
  have hstable : (prefixWord ++ tailWord_1702156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702156).length < 2 ^ (prefixWord ++ tailWord_1702156).sum := by decide
  have hdescent : baseEnd_1702156 < baseStart_1702156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702226 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 6]
def baseStart_1702226 : Nat := 118140960795 + 1702226 * 2 ^ 59
def prefixEnd_1702226 : Nat := 4983230072969 + 3 ^ 40 * 1702226 * 2
def baseEnd_1702226 : Nat := 97117791175595807405179

theorem tailTrace_1702226 : CollatzResearch.WordTrace tailWord_1702226 prefixEnd_1702226 97117791175595807405179 := by
  unfold tailWord_1702226
  simp only [CollatzResearch.WordTrace]
  refine ⟨15521320682783348475185633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41390188487422262600495021 15521320682783348475185633)
  ·
    refine ⟨11640990512087511356389225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15521320682783348475185633 11640990512087511356389225)
    ·
      refine ⟨8730742884065633517291919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11640990512087511356389225 8730742884065633517291919)
      ·
        refine ⟨13096114326098450275937879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8730742884065633517291919 13096114326098450275937879)
        ·
          refine ⟨19644171489147675413906819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13096114326098450275937879 19644171489147675413906819)
          ·
            refine ⟨29466257233721513120860229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19644171489147675413906819 29466257233721513120860229)
            ·
              refine ⟨5524923231322783710161293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29466257233721513120860229 5524923231322783710161293)
              ·
                refine ⟨2071846211746043891310485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5524923231322783710161293 2071846211746043891310485)
                ·
                  refine ⟨97117791175595807405179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2071846211746043891310485 97117791175595807405179)
                  ·
                    rfl

theorem cell23_1702226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_1702226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702226 prefixEnd_1702226 := by exact prefixLift 1702226
  have htrace : WordTrace (prefixWord ++ tailWord_1702226) baseStart_1702226 baseEnd_1702226 := by
    simpa [prefixWord, tailWord_1702226, baseEnd_1702226] using wordTrace_append hprefix tailTrace_1702226
  have hstable : (prefixWord ++ tailWord_1702226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702226).length < 2 ^ (prefixWord ++ tailWord_1702226).sum := by decide
  have hdescent : baseEnd_1702226 < baseStart_1702226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702240 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 3]
def baseStart_1702240 : Nat := 118140960795 + 1702240 * 2 ^ 59
def prefixEnd_1702240 : Nat := 4983230072969 + 3 ^ 40 * 1702240 * 2
def baseEnd_1702240 : Nat := 874067309309525211871547

theorem tailTrace_1702240 : CollatzResearch.WordTrace tailWord_1702240 prefixEnd_1702240 874067309309525211871547 := by
  unfold tailWord_1702240
  simp only [CollatzResearch.WordTrace]
  refine ⟨31042896676541337145876087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41390528902055116194501449 31042896676541337145876087)
  ·
    refine ⟨46564345014812005718814131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31042896676541337145876087 46564345014812005718814131)
    ·
      refine ⟨69846517522218008578221197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46564345014812005718814131 69846517522218008578221197)
      ·
        refine ⟨26192444070831753216832949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69846517522218008578221197 26192444070831753216832949)
        ·
          refine ⟨2455541631640476864078089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26192444070831753216832949 2455541631640476864078089)
          ·
            refine ⟨1841656223730357648058567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2455541631640476864078089 1841656223730357648058567)
            ·
              refine ⟨2762484335595536472087851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841656223730357648058567 2762484335595536472087851)
              ·
                refine ⟨4143726503393304708131777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762484335595536472087851 4143726503393304708131777)
                ·
                  refine ⟨3107794877544978531098833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4143726503393304708131777 3107794877544978531098833)
                  ·
                    refine ⟨2330846158158733898324125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3107794877544978531098833 2330846158158733898324125)
                    ·
                      refine ⟨874067309309525211871547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2330846158158733898324125 874067309309525211871547)
                      ·
                        rfl

theorem cell23_1702240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_1702240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702240 prefixEnd_1702240 := by exact prefixLift 1702240
  have htrace : WordTrace (prefixWord ++ tailWord_1702240) baseStart_1702240 baseEnd_1702240 := by
    simpa [prefixWord, tailWord_1702240, baseEnd_1702240] using wordTrace_append hprefix tailTrace_1702240
  have hstable : (prefixWord ++ tailWord_1702240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702240).length < 2 ^ (prefixWord ++ tailWord_1702240).sum := by decide
  have hdescent : baseEnd_1702240 < baseStart_1702240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702253 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1702253 : Nat := 118140960795 + 1702253 * 2 ^ 59
def prefixEnd_1702253 : Nat := 4983230072969 + 3 ^ 40 * 1702253 * 2
def baseEnd_1702253 : Nat := 874073984558033661008987

theorem tailTrace_1702253 : CollatzResearch.WordTrace tailWord_1702253 prefixEnd_1702253 874073984558033661008987 := by
  unfold tailWord_1702253
  simp only [CollatzResearch.WordTrace]
  refine ⟨62086267502035577511975413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41390845001357051674650275 62086267502035577511975413)
  ·
    refine ⟨5820587578315835391747695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62086267502035577511975413 5820587578315835391747695)
    ·
      refine ⟨8730881367473753087621543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5820587578315835391747695 8730881367473753087621543)
      ·
        refine ⟨13096322051210629631432315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8730881367473753087621543 13096322051210629631432315)
        ·
          refine ⟨19644483076815944447148473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13096322051210629631432315 19644483076815944447148473)
          ·
            refine ⟨14733362307611958335361355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19644483076815944447148473 14733362307611958335361355)
            ·
              refine ⟨22100043461417937503042033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14733362307611958335361355 22100043461417937503042033)
              ·
                refine ⟨16575032596063453127281525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22100043461417937503042033 16575032596063453127281525)
                ·
                  refine ⟨1553909305880948730682643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16575032596063453127281525 1553909305880948730682643)
                  ·
                    refine ⟨2330863958821423096023965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1553909305880948730682643 2330863958821423096023965)
                    ·
                      refine ⟨874073984558033661008987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2330863958821423096023965 874073984558033661008987)
                      ·
                        rfl

theorem cell23_1702253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1702253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702253 prefixEnd_1702253 := by exact prefixLift 1702253
  have htrace : WordTrace (prefixWord ++ tailWord_1702253) baseStart_1702253 baseEnd_1702253 := by
    simpa [prefixWord, tailWord_1702253, baseEnd_1702253] using wordTrace_append hprefix tailTrace_1702253
  have hstable : (prefixWord ++ tailWord_1702253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702253).length < 2 ^ (prefixWord ++ tailWord_1702253).sum := by decide
  have hdescent : baseEnd_1702253 < baseStart_1702253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702327 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 3, 2, 2]
def baseStart_1702327 : Nat := 118140960795 + 1702327 * 2 ^ 59
def prefixEnd_1702327 : Nat := 4983230072969 + 3 ^ 40 * 1702327 * 2
def baseEnd_1702327 : Nat := 874111982126466371483647

theorem tailTrace_1702327 : CollatzResearch.WordTrace tailWord_1702327 prefixEnd_1702327 874111982126466371483647 := by
  unfold tailWord_1702327
  simp only [CollatzResearch.WordTrace]
  refine ⟨62088966503767488150169235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41392644335844992100112823 62088966503767488150169235)
  ·
    refine ⟨93133449755651232225253853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62088966503767488150169235 93133449755651232225253853)
    ·
      refine ⟨34925043658369212084470195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93133449755651232225253853 34925043658369212084470195)
      ·
        refine ⟨52387565487553818126705293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34925043658369212084470195 52387565487553818126705293)
        ·
          refine ⟨19645337057832681797514485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52387565487553818126705293 19645337057832681797514485)
          ·
            refine ⟨1841750349171813918516983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19645337057832681797514485 1841750349171813918516983)
            ·
              refine ⟨2762625523757720877775475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841750349171813918516983 2762625523757720877775475)
              ·
                refine ⟨4143938285636581316663213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762625523757720877775475 4143938285636581316663213)
                ·
                  refine ⟨1553976857113717993748705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4143938285636581316663213 1553976857113717993748705)
                  ·
                    refine ⟨1165482642835288495311529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1553976857113717993748705 1165482642835288495311529)
                    ·
                      refine ⟨874111982126466371483647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165482642835288495311529 874111982126466371483647)
                      ·
                        rfl

theorem cell23_1702327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_1702327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702327 prefixEnd_1702327 := by exact prefixLift 1702327
  have htrace : WordTrace (prefixWord ++ tailWord_1702327) baseStart_1702327 baseEnd_1702327 := by
    simpa [prefixWord, tailWord_1702327, baseEnd_1702327] using wordTrace_append hprefix tailTrace_1702327
  have hstable : (prefixWord ++ tailWord_1702327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702327).length < 2 ^ (prefixWord ++ tailWord_1702327).sum := by decide
  have hdescent : baseEnd_1702327 < baseStart_1702327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702383 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 5, 4, 2]
def baseStart_1702383 : Nat := 118140960795 + 1702383 * 2 ^ 59
def prefixEnd_1702383 : Nat := 4983230072969 + 3 ^ 40 * 1702383 * 2
def baseEnd_1702383 : Nat := 874140737043118152383389

theorem tailTrace_1702383 : CollatzResearch.WordTrace tailWord_1702383 prefixEnd_1702383 874140737043118152383389 := by
  unfold tailWord_1702383
  simp only [CollatzResearch.WordTrace]
  refine ⟨62091008991564609714207803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41394005994376406476138535 62091008991564609714207803)
  ·
    refine ⟨93136513487346914571311705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62091008991564609714207803 93136513487346914571311705)
    ·
      refine ⟨69852385115510185928483779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93136513487346914571311705 69852385115510185928483779)
      ·
        refine ⟨104778577673265278892725669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69852385115510185928483779 104778577673265278892725669)
        ·
          refine ⟨19645983313737239792386063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104778577673265278892725669 19645983313737239792386063)
          ·
            refine ⟨29468974970605859688579095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19645983313737239792386063 29468974970605859688579095)
            ·
              refine ⟨44203462455908789532868643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29468974970605859688579095 44203462455908789532868643)
              ·
                refine ⟨66305193683863184299302965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44203462455908789532868643 66305193683863184299302965)
                ·
                  refine ⟨6216111907862173528059653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66305193683863184299302965 6216111907862173528059653)
                  ·
                    refine ⟨1165520982724157536511185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6216111907862173528059653 1165520982724157536511185)
                    ·
                      refine ⟨874140737043118152383389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165520982724157536511185 874140737043118152383389)
                      ·
                        rfl

theorem cell23_1702383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 4, 2].length) (baseStart_1702383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702383 prefixEnd_1702383 := by exact prefixLift 1702383
  have htrace : WordTrace (prefixWord ++ tailWord_1702383) baseStart_1702383 baseEnd_1702383 := by
    simpa [prefixWord, tailWord_1702383, baseEnd_1702383] using wordTrace_append hprefix tailTrace_1702383
  have hstable : (prefixWord ++ tailWord_1702383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702383).length < 2 ^ (prefixWord ++ tailWord_1702383).sum := by decide
  have hdescent : baseEnd_1702383 < baseStart_1702383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702433 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1702433 : Nat := 118140960795 + 1702433 * 2 ^ 59
def prefixEnd_1702433 : Nat := 4983230072969 + 3 ^ 40 * 1702433 * 2
def baseEnd_1702433 : Nat := 874166411075842956758159

theorem tailTrace_1702433 : CollatzResearch.WordTrace tailWord_1702433 prefixEnd_1702433 874166411075842956758159 := by
  unfold tailWord_1702433
  simp only [CollatzResearch.WordTrace]
  refine ⟨62092832641383468253527953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41395221760922312169018635 62092832641383468253527953)
  ·
    refine ⟨46569624481037601190145965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62092832641383468253527953 46569624481037601190145965)
    ·
      refine ⟨17463609180389100446304737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46569624481037601190145965 17463609180389100446304737)
      ·
        refine ⟨13097706885291825334728553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17463609180389100446304737 13097706885291825334728553)
        ·
          refine ⟨9823280163968869001046415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13097706885291825334728553 9823280163968869001046415)
          ·
            refine ⟨14734920245953303501569623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9823280163968869001046415 14734920245953303501569623)
            ·
              refine ⟨22102380368929955252354435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14734920245953303501569623 22102380368929955252354435)
              ·
                refine ⟨33153570553394932878531653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22102380368929955252354435 33153570553394932878531653)
                ·
                  refine ⟨6216294478761549914724685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33153570553394932878531653 6216294478761549914724685)
                  ·
                    refine ⟨2331110429535581218021757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6216294478761549914724685 2331110429535581218021757)
                    ·
                      refine ⟨874166411075842956758159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2331110429535581218021757 874166411075842956758159)
                      ·
                        rfl

theorem cell23_1702433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1702433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702433 prefixEnd_1702433 := by exact prefixLift 1702433
  have htrace : WordTrace (prefixWord ++ tailWord_1702433) baseStart_1702433 baseEnd_1702433 := by
    simpa [prefixWord, tailWord_1702433, baseEnd_1702433] using wordTrace_append hprefix tailTrace_1702433
  have hstable : (prefixWord ++ tailWord_1702433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702433).length < 2 ^ (prefixWord ++ tailWord_1702433).sum := by decide
  have hdescent : baseEnd_1702433 < baseStart_1702433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702440 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 7]
def baseStart_1702440 : Nat := 118140960795 + 1702440 * 2 ^ 59
def prefixEnd_1702440 : Nat := 4983230072969 + 3 ^ 40 * 1702440 * 2
def baseEnd_1702440 : Nat := 97130000604491603263403

theorem tailTrace_1702440 : CollatzResearch.WordTrace tailWord_1702440 prefixEnd_1702440 97130000604491603263403 := by
  unfold tailWord_1702440
  simp only [CollatzResearch.WordTrace]
  refine ⟨31046543976179054224516387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41395391968238738966021849 31046543976179054224516387)
  ·
    refine ⟨46569815964268581336774581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31046543976179054224516387 46569815964268581336774581)
    ·
      refine ⟨4365920246650179500322617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46569815964268581336774581 4365920246650179500322617)
      ·
        refine ⟨3274440184987634625241963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4365920246650179500322617 3274440184987634625241963)
        ·
          refine ⟨4911660277481451937862945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274440184987634625241963 4911660277481451937862945)
          ·
            refine ⟨3683745208111088953397209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4911660277481451937862945 3683745208111088953397209)
            ·
              refine ⟨2762808906083316715047907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3683745208111088953397209 2762808906083316715047907)
              ·
                refine ⟨4144213359124975072571861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762808906083316715047907 4144213359124975072571861)
                ·
                  refine ⟨97130000604491603263403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4144213359124975072571861 97130000604491603263403)
                  ·
                    rfl

theorem cell23_1702440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 7].length) (baseStart_1702440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702440 prefixEnd_1702440 := by exact prefixLift 1702440
  have htrace : WordTrace (prefixWord ++ tailWord_1702440) baseStart_1702440 baseEnd_1702440 := by
    simpa [prefixWord, tailWord_1702440, baseEnd_1702440] using wordTrace_append hprefix tailTrace_1702440
  have hstable : (prefixWord ++ tailWord_1702440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702440).length < 2 ^ (prefixWord ++ tailWord_1702440).sum := by decide
  have hdescent : baseEnd_1702440 < baseStart_1702440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702443 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 1, 7, 2]
def baseStart_1702443 : Nat := 118140960795 + 1702443 * 2 ^ 59
def prefixEnd_1702443 : Nat := 4983230072969 + 3 ^ 40 * 1702443 * 2
def baseEnd_1702443 : Nat := 874171545882387917633113

theorem tailTrace_1702443 : CollatzResearch.WordTrace tailWord_1702443 prefixEnd_1702443 874171545882387917633113 := by
  unfold tailWord_1702443
  simp only [CollatzResearch.WordTrace]
  refine ⟨62093197371347239961391983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41395464914231493307594655 62093197371347239961391983)
  ·
    refine ⟨93139796057020859942087975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62093197371347239961391983 93139796057020859942087975)
    ·
      refine ⟨139709694085531289913131963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93139796057020859942087975 139709694085531289913131963)
      ·
        refine ⟨209564541128296934869697945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139709694085531289913131963 209564541128296934869697945)
        ·
          refine ⟨157173405846222701152273459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209564541128296934869697945 157173405846222701152273459)
          ·
            refine ⟨235760108769334051728410189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157173405846222701152273459 235760108769334051728410189)
            ·
              refine ⟨88410040788500269398153821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235760108769334051728410189 88410040788500269398153821)
              ·
                refine ⟨33153765295687601024307683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88410040788500269398153821 33153765295687601024307683)
                ·
                  refine ⟨49730647943531401536461525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33153765295687601024307683 49730647943531401536461525)
                  ·
                    refine ⟨1165562061176517223510817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49730647943531401536461525 1165562061176517223510817)
                    ·
                      refine ⟨874171545882387917633113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165562061176517223510817 874171545882387917633113)
                      ·
                        rfl

theorem cell23_1702443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 7, 2].length) (baseStart_1702443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702443 prefixEnd_1702443 := by exact prefixLift 1702443
  have htrace : WordTrace (prefixWord ++ tailWord_1702443) baseStart_1702443 baseEnd_1702443 := by
    simpa [prefixWord, tailWord_1702443, baseEnd_1702443] using wordTrace_append hprefix tailTrace_1702443
  have hstable : (prefixWord ++ tailWord_1702443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702443).length < 2 ^ (prefixWord ++ tailWord_1702443).sum := by decide
  have hdescent : baseEnd_1702443 < baseStart_1702443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702540 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 7, 1, 3]
def baseStart_1702540 : Nat := 118140960795 + 1702540 * 2 ^ 59
def prefixEnd_1702540 : Nat := 4983230072969 + 3 ^ 40 * 1702540 * 2
def baseEnd_1702540 : Nat := 874221353505874038120167

theorem tailTrace_1702540 : CollatzResearch.WordTrace tailWord_1702540 prefixEnd_1702540 874221353505874038120167 := by
  unfold tailWord_1702540
  simp only [CollatzResearch.WordTrace]
  refine ⟨31048367625997912763836537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41397823501330550351782049 31048367625997912763836537)
  ·
    refine ⟨23286275719498434572877403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31048367625997912763836537 23286275719498434572877403)
    ·
      refine ⟨34929413579247651859316105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23286275719498434572877403 34929413579247651859316105)
      ·
        refine ⟨26197060184435738894487079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34929413579247651859316105 26197060184435738894487079)
        ·
          refine ⟨39295590276653608341730619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26197060184435738894487079 39295590276653608341730619)
          ·
            refine ⟨58943385414980412512595929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39295590276653608341730619 58943385414980412512595929)
            ·
              refine ⟨44207539061235309384446947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58943385414980412512595929 44207539061235309384446947)
              ·
                refine ⟨66311308591852964076670421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44207539061235309384446947 66311308591852964076670421)
                ·
                  refine ⟨1554171295121553845546963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 66311308591852964076670421 1554171295121553845546963)
                  ·
                    refine ⟨2331256942682330768320445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1554171295121553845546963 2331256942682330768320445)
                    ·
                      refine ⟨874221353505874038120167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2331256942682330768320445 874221353505874038120167)
                      ·
                        rfl

theorem cell23_1702540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_1702540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702540 prefixEnd_1702540 := by exact prefixLift 1702540
  have htrace : WordTrace (prefixWord ++ tailWord_1702540) baseStart_1702540 baseEnd_1702540 := by
    simpa [prefixWord, tailWord_1702540, baseEnd_1702540] using wordTrace_append hprefix tailTrace_1702540
  have hstable : (prefixWord ++ tailWord_1702540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702540).length < 2 ^ (prefixWord ++ tailWord_1702540).sum := by decide
  have hdescent : baseEnd_1702540 < baseStart_1702540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702574 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1702574 : Nat := 118140960795 + 1702574 * 2 ^ 59
def prefixEnd_1702574 : Nat := 4983230072969 + 3 ^ 40 * 1702574 * 2
def baseEnd_1702574 : Nat := 874238811848126905095011

theorem tailTrace_1702574 : CollatzResearch.WordTrace tailWord_1702574 prefixEnd_1702574 874238811848126905095011 := by
  unfold tailWord_1702574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762246916734081166801347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41398650222581766222940517 7762246916734081166801347)
  ·
    refine ⟨11643370375101121750202021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7762246916734081166801347 11643370375101121750202021)
    ·
      refine ⟨2183131945331460328162879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11643370375101121750202021 2183131945331460328162879)
      ·
        refine ⟨3274697917997190492244319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2183131945331460328162879 3274697917997190492244319)
        ·
          refine ⟨4912046876995785738366479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274697917997190492244319 4912046876995785738366479)
          ·
            refine ⟨7368070315493678607549719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912046876995785738366479 7368070315493678607549719)
            ·
              refine ⟨11052105473240517911324579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7368070315493678607549719 11052105473240517911324579)
              ·
                refine ⟨16578158209860776866986869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11052105473240517911324579 16578158209860776866986869)
                ·
                  refine ⟨1554202332174447831280019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16578158209860776866986869 1554202332174447831280019)
                  ·
                    refine ⟨2331303498261671746920029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1554202332174447831280019 2331303498261671746920029)
                    ·
                      refine ⟨874238811848126905095011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2331303498261671746920029 874238811848126905095011)
                      ·
                        rfl

theorem cell23_1702574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1702574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702574 prefixEnd_1702574 := by exact prefixLift 1702574
  have htrace : WordTrace (prefixWord ++ tailWord_1702574) baseStart_1702574 baseEnd_1702574 := by
    simpa [prefixWord, tailWord_1702574, baseEnd_1702574] using wordTrace_append hprefix tailTrace_1702574
  have hstable : (prefixWord ++ tailWord_1702574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702574).length < 2 ^ (prefixWord ++ tailWord_1702574).sum := by decide
  have hdescent : baseEnd_1702574 < baseStart_1702574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702590 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1702590 : Nat := 118140960795 + 1702590 * 2 ^ 59
def prefixEnd_1702590 : Nat := 4983230072969 + 3 ^ 40 * 1702590 * 2
def baseEnd_1702590 : Nat := 291415675846199614164979

theorem tailTrace_1702590 : CollatzResearch.WordTrace tailWord_1702590 prefixEnd_1702590 291415675846199614164979 := by
  unfold tailWord_1702590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762319862726835508374153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41399039267876456044662149 7762319862726835508374153)
  ·
    refine ⟨5821739897045126631280615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7762319862726835508374153 5821739897045126631280615)
    ·
      refine ⟨8732609845567689946920923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5821739897045126631280615 8732609845567689946920923)
      ·
        refine ⟨13098914768351534920381385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8732609845567689946920923 13098914768351534920381385)
        ·
          refine ⟨9824186076263651190286039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13098914768351534920381385 9824186076263651190286039)
          ·
            refine ⟨14736279114395476785429059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9824186076263651190286039 14736279114395476785429059)
            ·
              refine ⟨22104418671593215178143589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14736279114395476785429059 22104418671593215178143589)
              ·
                refine ⟨4144578500923727845901923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22104418671593215178143589 4144578500923727845901923)
                ·
                  refine ⟨6216867751385591768852885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144578500923727845901923 6216867751385591768852885)
                  ·
                    refine ⟨291415675846199614164979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6216867751385591768852885 291415675846199614164979)
                    ·
                      rfl

theorem cell23_1702590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1702590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702590 prefixEnd_1702590 := by exact prefixLift 1702590
  have htrace : WordTrace (prefixWord ++ tailWord_1702590) baseStart_1702590 baseEnd_1702590 := by
    simpa [prefixWord, tailWord_1702590, baseEnd_1702590] using wordTrace_append hprefix tailTrace_1702590
  have hstable : (prefixWord ++ tailWord_1702590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702590).length < 2 ^ (prefixWord ++ tailWord_1702590).sum := by decide
  have hdescent : baseEnd_1702590 < baseStart_1702590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702598 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_1702598 : Nat := 118140960795 + 1702598 * 2 ^ 59
def prefixEnd_1702598 : Nat := 4983230072969 + 3 ^ 40 * 1702598 * 2
def baseEnd_1702598 : Nat := 97139015042648312354989

theorem tailTrace_1702598 : CollatzResearch.WordTrace tailWord_1702598 prefixEnd_1702598 97139015042648312354989 := by
  unfold tailWord_1702598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1940589083930803169790139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41399233790523800955522965 1940589083930803169790139)
  ·
    refine ⟨2910883625896204754685209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1940589083930803169790139 2910883625896204754685209)
    ·
      refine ⟨2183162719422153566013907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2910883625896204754685209 2183162719422153566013907)
      ·
        refine ⟨3274744079133230349020861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2183162719422153566013907 3274744079133230349020861)
        ·
          refine ⟨1228029029674961380882823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3274744079133230349020861 1228029029674961380882823)
          ·
            refine ⟨1842043544512442071324235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228029029674961380882823 1842043544512442071324235)
            ·
              refine ⟨2763065316768663106986353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842043544512442071324235 2763065316768663106986353)
              ·
                refine ⟨2072298987576497330239765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763065316768663106986353 2072298987576497330239765)
                ·
                  refine ⟨97139015042648312354989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2072298987576497330239765 97139015042648312354989)
                  ·
                    rfl

theorem cell23_1702598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_1702598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702598 prefixEnd_1702598 := by exact prefixLift 1702598
  have htrace : WordTrace (prefixWord ++ tailWord_1702598) baseStart_1702598 baseEnd_1702598 := by
    simpa [prefixWord, tailWord_1702598, baseEnd_1702598] using wordTrace_append hprefix tailTrace_1702598
  have hstable : (prefixWord ++ tailWord_1702598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702598).length < 2 ^ (prefixWord ++ tailWord_1702598).sum := by decide
  have hdescent : baseEnd_1702598 < baseStart_1702598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702627 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1702627 : Nat := 118140960795 + 1702627 * 2 ^ 59
def prefixEnd_1702627 : Nat := 4983230072969 + 3 ^ 40 * 1702627 * 2
def baseEnd_1702627 : Nat := 874266026322815197732267

theorem tailTrace_1702627 : CollatzResearch.WordTrace tailWord_1702627 prefixEnd_1702627 874266026322815197732267 := by
  unfold tailWord_1702627
  simp only [CollatzResearch.WordTrace]
  refine ⟨62099908402680639386090135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41399938935120426257393423 62099908402680639386090135)
  ·
    refine ⟨93149862604020959079135203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62099908402680639386090135 93149862604020959079135203)
    ·
      refine ⟨139724793906031438618702805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93149862604020959079135203 139724793906031438618702805)
      ·
        refine ⟨3274799857172611842625847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 139724793906031438618702805 3274799857172611842625847)
        ·
          refine ⟨4912199785758917763938771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274799857172611842625847 4912199785758917763938771)
          ·
            refine ⟨7368299678638376645908157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912199785758917763938771 7368299678638376645908157)
            ·
              refine ⟨2763112379489391242215559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7368299678638376645908157 2763112379489391242215559)
              ·
                refine ⟨4144668569234086863323339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763112379489391242215559 4144668569234086863323339)
                ·
                  refine ⟨6217002853851130294985009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144668569234086863323339 6217002853851130294985009)
                  ·
                    refine ⟨4662752140388347721238757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6217002853851130294985009 4662752140388347721238757)
                    ·
                      refine ⟨874266026322815197732267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4662752140388347721238757 874266026322815197732267)
                      ·
                        rfl

theorem cell23_1702627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1702627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702627 prefixEnd_1702627 := by exact prefixLift 1702627
  have htrace : WordTrace (prefixWord ++ tailWord_1702627) baseStart_1702627 baseEnd_1702627 := by
    simpa [prefixWord, tailWord_1702627, baseEnd_1702627] using wordTrace_append hprefix tailTrace_1702627
  have hstable : (prefixWord ++ tailWord_1702627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702627).length < 2 ^ (prefixWord ++ tailWord_1702627).sum := by decide
  have hdescent : baseEnd_1702627 < baseStart_1702627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702633 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 2, 7]
def baseStart_1702633 : Nat := 118140960795 + 1702633 * 2 ^ 59
def prefixEnd_1702633 : Nat := 4983230072969 + 3 ^ 40 * 1702633 * 2
def baseEnd_1702633 : Nat := 291423035735580724752413

theorem tailTrace_1702633 : CollatzResearch.WordTrace tailWord_1702633 prefixEnd_1702633 291423035735580724752413 := by
  unfold tailWord_1702633
  simp only [CollatzResearch.WordTrace]
  refine ⟨62100127240658902410808553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41400084827105934940539035 62100127240658902410808553)
  ·
    refine ⟨46575095430494176808106415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62100127240658902410808553 46575095430494176808106415)
    ·
      refine ⟨69862643145741265212159623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46575095430494176808106415 69862643145741265212159623)
      ·
        refine ⟨104793964718611897818239435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69862643145741265212159623 104793964718611897818239435)
        ·
          refine ⟨157190947077917846727359153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104793964718611897818239435 157190947077917846727359153)
          ·
            refine ⟨117893210308438385045519365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157190947077917846727359153 117893210308438385045519365)
            ·
              refine ⟨22104976932832197196034881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117893210308438385045519365 22104976932832197196034881)
              ·
                refine ⟨16578732699624147897026161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22104976932832197196034881 16578732699624147897026161)
                ·
                  refine ⟨12434049524718110922769621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16578732699624147897026161 12434049524718110922769621)
                  ·
                    refine ⟨291423035735580724752413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12434049524718110922769621 291423035735580724752413)
                    ·
                      rfl

theorem cell23_1702633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_1702633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702633 prefixEnd_1702633 := by exact prefixLift 1702633
  have htrace : WordTrace (prefixWord ++ tailWord_1702633) baseStart_1702633 baseEnd_1702633 := by
    simpa [prefixWord, tailWord_1702633, baseEnd_1702633] using wordTrace_append hprefix tailTrace_1702633
  have hstable : (prefixWord ++ tailWord_1702633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702633).length < 2 ^ (prefixWord ++ tailWord_1702633).sum := by decide
  have hdescent : baseEnd_1702633 < baseStart_1702633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702657 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_1702657 : Nat := 118140960795 + 1702657 * 2 ^ 59
def prefixEnd_1702657 : Nat := 4983230072969 + 3 ^ 40 * 1702657 * 2
def baseEnd_1702657 : Nat := 874281430742450080357129

theorem tailTrace_1702657 : CollatzResearch.WordTrace tailWord_1702657 prefixEnd_1702657 874281430742450080357129 := by
  unfold tailWord_1702657
  simp only [CollatzResearch.WordTrace]
  refine ⟨62101002592571954509682225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41400668395047969673121483 62101002592571954509682225)
  ·
    refine ⟨46575751944428965882261669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62101002592571954509682225 46575751944428965882261669)
    ·
      refine ⟨8732953489580431102924063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46575751944428965882261669 8732953489580431102924063)
      ·
        refine ⟨13099430234370646654386095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8732953489580431102924063 13099430234370646654386095)
        ·
          refine ⟨19649145351555969981579143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13099430234370646654386095 19649145351555969981579143)
          ·
            refine ⟨29473718027333954972368715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19649145351555969981579143 29473718027333954972368715)
            ·
              refine ⟨44210577041000932458553073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29473718027333954972368715 44210577041000932458553073)
              ·
                refine ⟨33157932780750699343914805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44210577041000932458553073 33157932780750699343914805)
                ·
                  refine ⟨3108556198195378063492013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33157932780750699343914805 3108556198195378063492013)
                  ·
                    refine ⟨1165708574323266773809505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3108556198195378063492013 1165708574323266773809505)
                    ·
                      refine ⟨874281430742450080357129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165708574323266773809505 874281430742450080357129)
                      ·
                        rfl

theorem cell23_1702657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_1702657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702657 prefixEnd_1702657 := by exact prefixLift 1702657
  have htrace : WordTrace (prefixWord ++ tailWord_1702657) baseStart_1702657 baseEnd_1702657 := by
    simpa [prefixWord, tailWord_1702657, baseEnd_1702657] using wordTrace_append hprefix tailTrace_1702657
  have hstable : (prefixWord ++ tailWord_1702657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702657).length < 2 ^ (prefixWord ++ tailWord_1702657).sum := by decide
  have hdescent : baseEnd_1702657 < baseStart_1702657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702660 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1702660 : Nat := 118140960795 + 1702660 * 2 ^ 59
def prefixEnd_1702660 : Nat := 4983230072969 + 3 ^ 40 * 1702660 * 2
def baseEnd_1702660 : Nat := 874282971184413568619615

theorem tailTrace_1702660 : CollatzResearch.WordTrace tailWord_1702660 prefixEnd_1702660 874282971184413568619615 := by
  unfold tailWord_1702660
  simp only [CollatzResearch.WordTrace]
  refine ⟨31050556005780543011020717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41400741341040724014694289 31050556005780543011020717)
  ·
    refine ⟨11643958502167703629132769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31050556005780543011020717 11643958502167703629132769)
    ·
      refine ⟨8732968876625777721849577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11643958502167703629132769 8732968876625777721849577)
      ·
        refine ⟨6549726657469333291387183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8732968876625777721849577 6549726657469333291387183)
        ·
          refine ⟨9824589986203999937080775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6549726657469333291387183 9824589986203999937080775)
          ·
            refine ⟨14736884979305999905621163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9824589986203999937080775 14736884979305999905621163)
            ·
              refine ⟨22105327468958999858431745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14736884979305999905621163 22105327468958999858431745)
              ·
                refine ⟨16578995601719249893823809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22105327468958999858431745 16578995601719249893823809)
                ·
                  refine ⟨12434246701289437420367857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16578995601719249893823809 12434246701289437420367857)
                  ·
                    refine ⟨9325685025967078065275893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12434246701289437420367857 9325685025967078065275893)
                    ·
                      refine ⟨874282971184413568619615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9325685025967078065275893 874282971184413568619615)
                      ·
                        rfl

theorem cell23_1702660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1702660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702660 prefixEnd_1702660 := by exact prefixLift 1702660
  have htrace : WordTrace (prefixWord ++ tailWord_1702660) baseStart_1702660 baseEnd_1702660 := by
    simpa [prefixWord, tailWord_1702660, baseEnd_1702660] using wordTrace_append hprefix tailTrace_1702660
  have hstable : (prefixWord ++ tailWord_1702660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702660).length < 2 ^ (prefixWord ++ tailWord_1702660).sum := by decide
  have hdescent : baseEnd_1702660 < baseStart_1702660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702670 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1702670 : Nat := 118140960795 + 1702670 * 2 ^ 59
def prefixEnd_1702670 : Nat := 4983230072969 + 3 ^ 40 * 1702670 * 2
def baseEnd_1702670 : Nat := 874288105990958529494569

theorem tailTrace_1702670 : CollatzResearch.WordTrace tailWord_1702670 prefixEnd_1702670 874288105990958529494569 := by
  unfold tailWord_1702670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762684592690607216238183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41400984494349905153270309 7762684592690607216238183)
  ·
    refine ⟨11644026889035910824357275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7762684592690607216238183 11644026889035910824357275)
    ·
      refine ⟨17466040333553866236535913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11644026889035910824357275 17466040333553866236535913)
      ·
        refine ⟨13099530250165399677401935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17466040333553866236535913 13099530250165399677401935)
        ·
          refine ⟨19649295375248099516102903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13099530250165399677401935 19649295375248099516102903)
          ·
            refine ⟨29473943062872149274154355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19649295375248099516102903 29473943062872149274154355)
            ·
              refine ⟨44210914594308223911231533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29473943062872149274154355 44210914594308223911231533)
              ·
                refine ⟨16579092972865583966711825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44210914594308223911231533 16579092972865583966711825)
                ·
                  refine ⟨12434319729649187975033869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16579092972865583966711825 12434319729649187975033869)
                  ·
                    refine ⟨4662869898618445490637701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12434319729649187975033869 4662869898618445490637701)
                    ·
                      refine ⟨874288105990958529494569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4662869898618445490637701 874288105990958529494569)
                      ·
                        rfl

theorem cell23_1702670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1702670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702670 prefixEnd_1702670 := by exact prefixLift 1702670
  have htrace : WordTrace (prefixWord ++ tailWord_1702670) baseStart_1702670 baseEnd_1702670 := by
    simpa [prefixWord, tailWord_1702670, baseEnd_1702670] using wordTrace_append hprefix tailTrace_1702670
  have hstable : (prefixWord ++ tailWord_1702670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702670).length < 2 ^ (prefixWord ++ tailWord_1702670).sum := by decide
  have hdescent : baseEnd_1702670 < baseStart_1702670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702720 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 3]
def baseStart_1702720 : Nat := 118140960795 + 1702720 * 2 ^ 59
def prefixEnd_1702720 : Nat := 4983230072969 + 3 ^ 40 * 1702720 * 2
def baseEnd_1702720 : Nat := 874313780023683333869339

theorem tailTrace_1702720 : CollatzResearch.WordTrace tailWord_1702720 prefixEnd_1702720 874313780023683333869339 := by
  unfold tailWord_1702720
  simp only [CollatzResearch.WordTrace]
  refine ⟨31051650195671858134612807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41402200260895810846150409 31051650195671858134612807)
  ·
    refine ⟨46577475293507787201919211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31051650195671858134612807 46577475293507787201919211)
    ·
      refine ⟨69866212940261680802878817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46577475293507787201919211 69866212940261680802878817)
      ·
        refine ⟨52399659705196260602159113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69866212940261680802878817 52399659705196260602159113)
        ·
          refine ⟨39299744778897195451619335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52399659705196260602159113 39299744778897195451619335)
          ·
            refine ⟨58949617168345793177429003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39299744778897195451619335 58949617168345793177429003)
            ·
              refine ⟨88424425752518689766143505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58949617168345793177429003 88424425752518689766143505)
              ·
                refine ⟨66318319314389017324607629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88424425752518689766143505 66318319314389017324607629)
                ·
                  refine ⟨24869369742895881496727861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66318319314389017324607629 24869369742895881496727861)
                  ·
                    refine ⟨2331503413396488890318237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24869369742895881496727861 2331503413396488890318237)
                    ·
                      refine ⟨874313780023683333869339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2331503413396488890318237 874313780023683333869339)
                      ·
                        rfl

theorem cell23_1702720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_1702720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702720 prefixEnd_1702720 := by exact prefixLift 1702720
  have htrace : WordTrace (prefixWord ++ tailWord_1702720) baseStart_1702720 baseEnd_1702720 := by
    simpa [prefixWord, tailWord_1702720, baseEnd_1702720] using wordTrace_append hprefix tailTrace_1702720
  have hstable : (prefixWord ++ tailWord_1702720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702720).length < 2 ^ (prefixWord ++ tailWord_1702720).sum := by decide
  have hdescent : baseEnd_1702720 < baseStart_1702720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702757 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_1702757 : Nat := 118140960795 + 1702757 * 2 ^ 59
def prefixEnd_1702757 : Nat := 4983230072969 + 3 ^ 40 * 1702757 * 2
def baseEnd_1702757 : Nat := 291444259602633229702223

theorem tailTrace_1702757 : CollatzResearch.WordTrace tailWord_1702757 prefixEnd_1702757 291444259602633229702223 := by
  unfold tailWord_1702757
  simp only [CollatzResearch.WordTrace]
  refine ⟨62104649892209671588322525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41403099928139781058881683 62104649892209671588322525)
  ·
    refine ⟨23289243709578626845620947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62104649892209671588322525 23289243709578626845620947)
    ·
      refine ⟨34933865564367940268431421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23289243709578626845620947 34933865564367940268431421)
      ·
        refine ⟨13100199586637977600661783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34933865564367940268431421 13100199586637977600661783)
        ·
          refine ⟨19650299379956966400992675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13100199586637977600661783 19650299379956966400992675)
          ·
            refine ⟨29475449069935449601489013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19650299379956966400992675 29475449069935449601489013)
            ·
              refine ⟨2763323350306448400139595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29475449069935449601489013 2763323350306448400139595)
              ·
                refine ⟨4144985025459672600209393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763323350306448400139595 4144985025459672600209393)
                ·
                  refine ⟨3108738769094754450157045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4144985025459672600209393 3108738769094754450157045)
                  ·
                    refine ⟨291444259602633229702223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3108738769094754450157045 291444259602633229702223)
                    ·
                      rfl

theorem cell23_1702757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_1702757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702757 prefixEnd_1702757 := by exact prefixLift 1702757
  have htrace : WordTrace (prefixWord ++ tailWord_1702757) baseStart_1702757 baseEnd_1702757 := by
    simpa [prefixWord, tailWord_1702757, baseEnd_1702757] using wordTrace_append hprefix tailTrace_1702757
  have hstable : (prefixWord ++ tailWord_1702757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702757).length < 2 ^ (prefixWord ++ tailWord_1702757).sum := by decide
  have hdescent : baseEnd_1702757 < baseStart_1702757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702780 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_1702780 : Nat := 118140960795 + 1702780 * 2 ^ 59
def prefixEnd_1702780 : Nat := 4983230072969 + 3 ^ 40 * 1702780 * 2
def baseEnd_1702780 : Nat := 874344588862953099119063

theorem tailTrace_1702780 : CollatzResearch.WordTrace tailWord_1702780 prefixEnd_1702780 874344588862953099119063 := by
  unfold tailWord_1702780
  simp only [CollatzResearch.WordTrace]
  refine ⟨31052744385563173258204897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41403659180750897677606529 31052744385563173258204897)
  ·
    refine ⟨23289558289172379943653673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31052744385563173258204897 23289558289172379943653673)
    ·
      refine ⟨17467168716879284957740255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23289558289172379943653673 17467168716879284957740255)
      ·
        refine ⟨26200753075318927436610383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17467168716879284957740255 26200753075318927436610383)
        ·
          refine ⟨39301129612978391154915575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26200753075318927436610383 39301129612978391154915575)
          ·
            refine ⟨58951694419467586732373363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39301129612978391154915575 58951694419467586732373363)
            ·
              refine ⟨88427541629201380098560045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58951694419467586732373363 88427541629201380098560045)
              ·
                refine ⟨33160328110950517536960017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88427541629201380098560045 33160328110950517536960017)
                ·
                  refine ⟨24870246083212888152720013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33160328110950517536960017 24870246083212888152720013)
                  ·
                    refine ⟨9326342281204833057270005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24870246083212888152720013 9326342281204833057270005)
                    ·
                      refine ⟨874344588862953099119063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9326342281204833057270005 874344588862953099119063)
                      ·
                        rfl

theorem cell23_1702780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_1702780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702780 prefixEnd_1702780 := by exact prefixLift 1702780
  have htrace : WordTrace (prefixWord ++ tailWord_1702780) baseStart_1702780 baseEnd_1702780 := by
    simpa [prefixWord, tailWord_1702780, baseEnd_1702780] using wordTrace_append hprefix tailTrace_1702780
  have hstable : (prefixWord ++ tailWord_1702780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702780).length < 2 ^ (prefixWord ++ tailWord_1702780).sum := by decide
  have hdescent : baseEnd_1702780 < baseStart_1702780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702804 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1702804 : Nat := 118140960795 + 1702804 * 2 ^ 59
def prefixEnd_1702804 : Nat := 4983230072969 + 3 ^ 40 * 1702804 * 2
def baseEnd_1702804 : Nat := 291452304132887001739651

theorem tailTrace_1702804 : CollatzResearch.WordTrace tailWord_1702804 prefixEnd_1702804 291452304132887001739651 := by
  unfold tailWord_1702804
  simp only [CollatzResearch.WordTrace]
  refine ⟨31053182061519699307641733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41404242748692932410188977 31053182061519699307641733)
  ·
    refine ⟨5822471636534943620182825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31053182061519699307641733 5822471636534943620182825)
    ·
      refine ⟨4366853727401207715137119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5822471636534943620182825 4366853727401207715137119)
      ·
        refine ⟨6550280591101811572705679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4366853727401207715137119 6550280591101811572705679)
        ·
          refine ⟨9825420886652717359058519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6550280591101811572705679 9825420886652717359058519)
          ·
            refine ⟨14738131329979076038587779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9825420886652717359058519 14738131329979076038587779)
            ·
              refine ⟨22107196994968614057881669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14738131329979076038587779 22107196994968614057881669)
              ·
                refine ⟨4145099436556615135852813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22107196994968614057881669 4145099436556615135852813)
                ·
                  refine ⟨1554412288708730675944805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4145099436556615135852813 1554412288708730675944805)
                  ·
                    refine ⟨291452304132887001739651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1554412288708730675944805 291452304132887001739651)
                    ·
                      rfl

theorem cell23_1702804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1702804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702804 prefixEnd_1702804 := by exact prefixLift 1702804
  have htrace : WordTrace (prefixWord ++ tailWord_1702804) baseStart_1702804 baseEnd_1702804 := by
    simpa [prefixWord, tailWord_1702804, baseEnd_1702804] using wordTrace_append hprefix tailTrace_1702804
  have hstable : (prefixWord ++ tailWord_1702804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702804).length < 2 ^ (prefixWord ++ tailWord_1702804).sum := by decide
  have hdescent : baseEnd_1702804 < baseStart_1702804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702817 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 8]
def baseStart_1702817 : Nat := 118140960795 + 1702817 * 2 ^ 59
def prefixEnd_1702817 : Nat := 4983230072969 + 3 ^ 40 * 1702817 * 2
def baseEnd_1702817 : Nat := 97151509738574383817377

theorem tailTrace_1702817 : CollatzResearch.WordTrace tailWord_1702817 prefixEnd_1702817 97151509738574383817377 := by
  unfold tailWord_1702817
  simp only [CollatzResearch.WordTrace]
  refine ⟨62106838271992301835506705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41404558847994867890337803 62106838271992301835506705)
  ·
    refine ⟨46580128703994226376630029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62106838271992301835506705 46580128703994226376630029)
    ·
      refine ⟨17467548263997834891236261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46580128703994226376630029 17467548263997834891236261)
      ·
        refine ⟨3275165299499594042106799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17467548263997834891236261 3275165299499594042106799)
        ·
          refine ⟨4912747949249391063160199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3275165299499594042106799 4912747949249391063160199)
          ·
            refine ⟨7369121923874086594740299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912747949249391063160199 7369121923874086594740299)
            ·
              refine ⟨11053682885811129892110449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369121923874086594740299 11053682885811129892110449)
              ·
                refine ⟨8290262164358347419082837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11053682885811129892110449 8290262164358347419082837)
                ·
                  refine ⟨97151509738574383817377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8290262164358347419082837 97151509738574383817377)
                  ·
                    rfl

theorem cell23_1702817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 8].length) (baseStart_1702817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702817 prefixEnd_1702817 := by exact prefixLift 1702817
  have htrace : WordTrace (prefixWord ++ tailWord_1702817) baseStart_1702817 baseEnd_1702817 := by
    simpa [prefixWord, tailWord_1702817, baseEnd_1702817] using wordTrace_append hprefix tailTrace_1702817
  have hstable : (prefixWord ++ tailWord_1702817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702817).length < 2 ^ (prefixWord ++ tailWord_1702817).sum := by decide
  have hdescent : baseEnd_1702817 < baseStart_1702817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702895 : List Nat := [1, 1, 2, 1, 4, 5, 2, 2, 1, 1, 3]
def baseStart_1702895 : Nat := 118140960795 + 1702895 * 2 ^ 59
def prefixEnd_1702895 : Nat := 4983230072969 + 3 ^ 40 * 1702895 * 2
def baseEnd_1702895 : Nat := 874403639138220149181035

theorem tailTrace_1702895 : CollatzResearch.WordTrace tailWord_1702895 prefixEnd_1702895 874403639138220149181035 := by
  unfold tailWord_1702895
  simp only [CollatzResearch.WordTrace]
  refine ⟨62109683165709721156846139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41406455443806480771230759 62109683165709721156846139)
  ·
    refine ⟨93164524748564581735269209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62109683165709721156846139 93164524748564581735269209)
    ·
      refine ⟨69873393561423436301451907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93164524748564581735269209 69873393561423436301451907)
      ·
        refine ⟨104810090342135154452177861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69873393561423436301451907 104810090342135154452177861)
        ·
          refine ⟨19651891939150341459783349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104810090342135154452177861 19651891939150341459783349)
          ·
            refine ⟨1842364869295344511854689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19651891939150341459783349 1842364869295344511854689)
            ·
              refine ⟨1381773651971508383891017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1842364869295344511854689 1381773651971508383891017)
              ·
                refine ⟨1036330238978631287918263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1381773651971508383891017 1036330238978631287918263)
                ·
                  refine ⟨1554495358467946931877395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036330238978631287918263 1554495358467946931877395)
                  ·
                    refine ⟨2331743037701920397816093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1554495358467946931877395 2331743037701920397816093)
                    ·
                      refine ⟨874403639138220149181035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2331743037701920397816093 874403639138220149181035)
                      ·
                        rfl

theorem cell23_1702895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 1, 1, 3].length) (baseStart_1702895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702895 prefixEnd_1702895 := by exact prefixLift 1702895
  have htrace : WordTrace (prefixWord ++ tailWord_1702895) baseStart_1702895 baseEnd_1702895 := by
    simpa [prefixWord, tailWord_1702895, baseEnd_1702895] using wordTrace_append hprefix tailTrace_1702895
  have hstable : (prefixWord ++ tailWord_1702895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702895).length < 2 ^ (prefixWord ++ tailWord_1702895).sum := by decide
  have hdescent : baseEnd_1702895 < baseStart_1702895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702924 : List Nat := [2, 2, 1, 2, 3, 3, 3, 7]
def baseStart_1702924 : Nat := 118140960795 + 1702924 * 2 ^ 59
def prefixEnd_1702924 : Nat := 4983230072969 + 3 ^ 40 * 1702924 * 2
def baseEnd_1702924 : Nat := 32385871484340760582163

theorem tailTrace_1702924 : CollatzResearch.WordTrace tailWord_1702924 prefixEnd_1702924 32385871484340760582163 := by
  unfold tailWord_1702924
  simp only [CollatzResearch.WordTrace]
  refine ⟨31055370441302329554825913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41407160588403106073101217 31055370441302329554825913)
  ·
    refine ⟨23291527830976747166119435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31055370441302329554825913 23291527830976747166119435)
    ·
      refine ⟨34937291746465120749179153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23291527830976747166119435 34937291746465120749179153)
      ·
        refine ⟨26202968809848840561884365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34937291746465120749179153 26202968809848840561884365)
        ·
          refine ⟨9826113303693315210706637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26202968809848840561884365 9826113303693315210706637)
          ·
            refine ⟨3684792488884993204014989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9826113303693315210706637 3684792488884993204014989)
            ·
              refine ⟨1381797183331872451505621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3684792488884993204014989 1381797183331872451505621)
              ·
                refine ⟨32385871484340760582163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1381797183331872451505621 32385871484340760582163)
                ·
                  rfl

theorem cell23_1702924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 7].length) (baseStart_1702924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702924 prefixEnd_1702924 := by exact prefixLift 1702924
  have htrace : WordTrace (prefixWord ++ tailWord_1702924) baseStart_1702924 baseEnd_1702924 := by
    simpa [prefixWord, tailWord_1702924, baseEnd_1702924] using wordTrace_append hprefix tailTrace_1702924
  have hstable : (prefixWord ++ tailWord_1702924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702924).length < 2 ^ (prefixWord ++ tailWord_1702924).sum := by decide
  have hdescent : baseEnd_1702924 < baseStart_1702924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702935 : List Nat := [1, 1, 3, 5, 1, 1, 1, 5, 1, 2, 2]
def baseStart_1702935 : Nat := 118140960795 + 1702935 * 2 ^ 59
def prefixEnd_1702935 : Nat := 4983230072969 + 3 ^ 40 * 1702935 * 2
def baseEnd_1702935 : Nat := 874424178364399992680851

theorem tailTrace_1702935 : CollatzResearch.WordTrace tailWord_1702935 prefixEnd_1702935 874424178364399992680851 := by
  unfold tailWord_1702935
  simp only [CollatzResearch.WordTrace]
  refine ⟨62111142085564807988302259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41407428057043205325534839 62111142085564807988302259)
  ·
    refine ⟨93166713128347211982453389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62111142085564807988302259 93166713128347211982453389)
    ·
      refine ⟨34937517423130204493420021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93166713128347211982453389 34937517423130204493420021)
      ·
        refine ⟨3275392258418456671258127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34937517423130204493420021 3275392258418456671258127)
        ·
          refine ⟨4913088387627685006887191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3275392258418456671258127 4913088387627685006887191)
          ·
            refine ⟨7369632581441527510330787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913088387627685006887191 7369632581441527510330787)
            ·
              refine ⟨11054448872162291265496181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369632581441527510330787 11054448872162291265496181)
              ·
                refine ⟨1036354581765214806140267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11054448872162291265496181 1036354581765214806140267)
                ·
                  refine ⟨1554531872647822209210401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036354581765214806140267 1554531872647822209210401)
                  ·
                    refine ⟨1165898904485866656907801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1554531872647822209210401 1165898904485866656907801)
                    ·
                      refine ⟨874424178364399992680851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165898904485866656907801 874424178364399992680851)
                      ·
                        rfl

theorem cell23_1702935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_1702935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702935 prefixEnd_1702935 := by exact prefixLift 1702935
  have htrace : WordTrace (prefixWord ++ tailWord_1702935) baseStart_1702935 baseEnd_1702935 := by
    simpa [prefixWord, tailWord_1702935, baseEnd_1702935] using wordTrace_append hprefix tailTrace_1702935
  have hstable : (prefixWord ++ tailWord_1702935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702935).length < 2 ^ (prefixWord ++ tailWord_1702935).sum := by decide
  have hdescent : baseEnd_1702935 < baseStart_1702935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702994 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1702994 : Nat := 118140960795 + 1702994 * 2 ^ 59
def prefixEnd_1702994 : Nat := 4983230072969 + 3 ^ 40 * 1702994 * 2
def baseEnd_1702994 : Nat := 874454473723015261843079

theorem tailTrace_1702994 : CollatzResearch.WordTrace tailWord_1702994 prefixEnd_1702994 874454473723015261843079 := by
  unfold tailWord_1702994
  simp only [CollatzResearch.WordTrace]
  refine ⟨15528323498087765266175009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41408862661567374043133357 15528323498087765266175009)
  ·
    refine ⟨11646242623565823949631257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15528323498087765266175009 11646242623565823949631257)
    ·
      refine ⟨8734681967674367962223443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11646242623565823949631257 8734681967674367962223443)
      ·
        refine ⟨13102022951511551943335165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8734681967674367962223443 13102022951511551943335165)
        ·
          refine ⟨4913258606816831978750687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13102022951511551943335165 4913258606816831978750687)
          ·
            refine ⟨7369887910225247968126031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913258606816831978750687 7369887910225247968126031)
            ·
              refine ⟨11054831865337871952189047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369887910225247968126031 11054831865337871952189047)
              ·
                refine ⟨16582247798006807928283571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11054831865337871952189047 16582247798006807928283571)
                ·
                  refine ⟨24873371697010211892425357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16582247798006807928283571 24873371697010211892425357)
                  ·
                    refine ⟨9327514386378829459659509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24873371697010211892425357 9327514386378829459659509)
                    ·
                      refine ⟨874454473723015261843079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9327514386378829459659509 874454473723015261843079)
                      ·
                        rfl

theorem cell23_1702994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1702994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1702994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1702994 prefixEnd_1702994 := by exact prefixLift 1702994
  have htrace : WordTrace (prefixWord ++ tailWord_1702994) baseStart_1702994 baseEnd_1702994 := by
    simpa [prefixWord, tailWord_1702994, baseEnd_1702994] using wordTrace_append hprefix tailTrace_1702994
  have hstable : (prefixWord ++ tailWord_1702994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702994).length < 2 ^ (prefixWord ++ tailWord_1702994).sum := by decide
  have hdescent : baseEnd_1702994 < baseStart_1702994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703007 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1703007 : Nat := 118140960795 + 1703007 * 2 ^ 59
def prefixEnd_1703007 : Nat := 4983230072969 + 3 ^ 40 * 1703007 * 2
def baseEnd_1703007 : Nat := 874461148971523710980519

theorem tailTrace_1703007 : CollatzResearch.WordTrace tailWord_1703007 prefixEnd_1703007 874461148971523710980519 := by
  unfold tailWord_1703007
  simp only [CollatzResearch.WordTrace]
  refine ⟨62113768141303964284923275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41409178760869309523282183 62113768141303964284923275)
  ·
    refine ⟨93170652211955946427384913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62113768141303964284923275 93170652211955946427384913)
    ·
      refine ⟨69877989158966959820538685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93170652211955946427384913 69877989158966959820538685)
      ·
        refine ⟨26204245934612609932702007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69877989158966959820538685 26204245934612609932702007)
        ·
          refine ⟨39306368901918914899053011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26204245934612609932702007 39306368901918914899053011)
          ·
            refine ⟨58959553352878372348579517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39306368901918914899053011 58959553352878372348579517)
            ·
              refine ⟨22109832507329389630717319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58959553352878372348579517 22109832507329389630717319)
              ·
                refine ⟨33164748760994084446075979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22109832507329389630717319 33164748760994084446075979)
                ·
                  refine ⟨49747123141491126669113969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33164748760994084446075979 49747123141491126669113969)
                  ·
                    refine ⟨37310342356118345001835477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49747123141491126669113969 37310342356118345001835477)
                    ·
                      refine ⟨874461148971523710980519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37310342356118345001835477 874461148971523710980519)
                      ·
                        rfl

theorem cell23_1703007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1703007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703007 prefixEnd_1703007 := by exact prefixLift 1703007
  have htrace : WordTrace (prefixWord ++ tailWord_1703007) baseStart_1703007 baseEnd_1703007 := by
    simpa [prefixWord, tailWord_1703007, baseEnd_1703007] using wordTrace_append hprefix tailTrace_1703007
  have hstable : (prefixWord ++ tailWord_1703007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703007).length < 2 ^ (prefixWord ++ tailWord_1703007).sum := by decide
  have hdescent : baseEnd_1703007 < baseStart_1703007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703008 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 2, 2, 2]
def baseStart_1703008 : Nat := 118140960795 + 1703008 * 2 ^ 59
def prefixEnd_1703008 : Nat := 4983230072969 + 3 ^ 40 * 1703008 * 2
def baseEnd_1703008 : Nat := 874461662452178207068015

theorem tailTrace_1703008 : CollatzResearch.WordTrace tailWord_1703008 prefixEnd_1703008 874461662452178207068015 := by
  unfold tailWord_1703008
  simp only [CollatzResearch.WordTrace]
  refine ⟨31056902307150170727854839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41409203076200227637139785 31056902307150170727854839)
  ·
    refine ⟨46585353460725256091782259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31056902307150170727854839 46585353460725256091782259)
    ·
      refine ⟨69878030191087884137673389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46585353460725256091782259 69878030191087884137673389)
      ·
        refine ⟨26204261321657956551627521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69878030191087884137673389 26204261321657956551627521)
        ·
          refine ⟨19653195991243467413720641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26204261321657956551627521 19653195991243467413720641)
          ·
            refine ⟨14739896993432600560290481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19653195991243467413720641 14739896993432600560290481)
            ·
              refine ⟨11054922745074450420217861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14739896993432600560290481 11054922745074450420217861)
              ·
                refine ⟨2072798014701459453790849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11054922745074450420217861 2072798014701459453790849)
                ·
                  refine ⟨1554598511026094590343137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2072798014701459453790849 1554598511026094590343137)
                  ·
                    refine ⟨1165948883269570942757353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1554598511026094590343137 1165948883269570942757353)
                    ·
                      refine ⟨874461662452178207068015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165948883269570942757353 874461662452178207068015)
                      ·
                        rfl

theorem cell23_1703008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_1703008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703008 prefixEnd_1703008 := by exact prefixLift 1703008
  have htrace : WordTrace (prefixWord ++ tailWord_1703008) baseStart_1703008 baseEnd_1703008 := by
    simpa [prefixWord, tailWord_1703008, baseEnd_1703008] using wordTrace_append hprefix tailTrace_1703008
  have hstable : (prefixWord ++ tailWord_1703008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703008).length < 2 ^ (prefixWord ++ tailWord_1703008).sum := by decide
  have hdescent : baseEnd_1703008 < baseStart_1703008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703024 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 3]
def baseStart_1703024 : Nat := 118140960795 + 1703024 * 2 ^ 59
def prefixEnd_1703024 : Nat := 4983230072969 + 3 ^ 40 * 1703024 * 2
def baseEnd_1703024 : Nat := 874469878142650144467941

theorem tailTrace_1703024 : CollatzResearch.WordTrace tailWord_1703024 prefixEnd_1703024 874469878142650144467941 := by
  unfold tailWord_1703024
  simp only [CollatzResearch.WordTrace]
  refine ⟨31057194091121188094146063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41409592121494917458861417 31057194091121188094146063)
  ·
    refine ⟨46585791136681782141219095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31057194091121188094146063 46585791136681782141219095)
    ·
      refine ⟨69878686705022673211828643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46585791136681782141219095 69878686705022673211828643)
      ·
        refine ⟨104818030057534009817742965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69878686705022673211828643 104818030057534009817742965)
        ·
          refine ⟨9826690317893813420413403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104818030057534009817742965 9826690317893813420413403)
          ·
            refine ⟨14740035476840720130620105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9826690317893813420413403 14740035476840720130620105)
            ·
              refine ⟨11055026607630540097965079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14740035476840720130620105 11055026607630540097965079)
              ·
                refine ⟨16582539911445810146947619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11055026607630540097965079 16582539911445810146947619)
                ·
                  refine ⟨24873809867168715220421429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16582539911445810146947619 24873809867168715220421429)
                  ·
                    refine ⟨2331919675047067051914509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24873809867168715220421429 2331919675047067051914509)
                    ·
                      refine ⟨874469878142650144467941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2331919675047067051914509 874469878142650144467941)
                      ·
                        rfl

theorem cell23_1703024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 3].length) (baseStart_1703024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703024 prefixEnd_1703024 := by exact prefixLift 1703024
  have htrace : WordTrace (prefixWord ++ tailWord_1703024) baseStart_1703024 baseEnd_1703024 := by
    simpa [prefixWord, tailWord_1703024, baseEnd_1703024] using wordTrace_append hprefix tailTrace_1703024
  have hstable : (prefixWord ++ tailWord_1703024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703024).length < 2 ^ (prefixWord ++ tailWord_1703024).sum := by decide
  have hdescent : baseEnd_1703024 < baseStart_1703024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703029 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1703029 : Nat := 118140960795 + 1703029 * 2 ^ 59
def prefixEnd_1703029 : Nat := 4983230072969 + 3 ^ 40 * 1703029 * 2
def baseEnd_1703029 : Nat := 874472445545922624905419

theorem tailTrace_1703029 : CollatzResearch.WordTrace tailWord_1703029 prefixEnd_1703029 874472445545922624905419 := by
  unfold tailWord_1703029
  simp only [CollatzResearch.WordTrace]
  refine ⟨62114570547224262042224141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41409713698149508028149427 62114570547224262042224141)
  ·
    refine ⟨23292963955209098265834053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62114570547224262042224141 23292963955209098265834053)
    ·
      refine ⟨4367430741601705924843885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23292963955209098265834053 4367430741601705924843885)
      ·
        refine ⟨1637786528100639721816457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4367430741601705924843885 1637786528100639721816457)
        ·
          refine ⟨1228339896075479791362343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1637786528100639721816457 1228339896075479791362343)
          ·
            refine ⟨1842509844113219687043515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228339896075479791362343 1842509844113219687043515)
            ·
              refine ⟨2763764766169829530565273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842509844113219687043515 2763764766169829530565273)
              ·
                refine ⟨2072823574627372147923955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763764766169829530565273 2072823574627372147923955)
                ·
                  refine ⟨3109235361941058221885933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072823574627372147923955 3109235361941058221885933)
                  ·
                    refine ⟨1165963260727896833207225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3109235361941058221885933 1165963260727896833207225)
                    ·
                      refine ⟨874472445545922624905419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1165963260727896833207225 874472445545922624905419)
                      ·
                        rfl

theorem cell23_1703029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1703029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703029 prefixEnd_1703029 := by exact prefixLift 1703029
  have htrace : WordTrace (prefixWord ++ tailWord_1703029) baseStart_1703029 baseEnd_1703029 := by
    simpa [prefixWord, tailWord_1703029, baseEnd_1703029] using wordTrace_append hprefix tailTrace_1703029
  have hstable : (prefixWord ++ tailWord_1703029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703029).length < 2 ^ (prefixWord ++ tailWord_1703029).sum := by decide
  have hdescent : baseEnd_1703029 < baseStart_1703029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
