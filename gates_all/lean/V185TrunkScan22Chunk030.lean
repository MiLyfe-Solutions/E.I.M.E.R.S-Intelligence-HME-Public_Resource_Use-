import V185TrunkScan22Chunk029

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_268300 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 6]
def baseStart_268300 : Nat := 118140960795 + 268300 * 2 ^ 59
def prefixEnd_268300 : Nat := 4983230072969 + 3 ^ 40 * 268300 * 2
def baseEnd_268300 : Nat := 30614857689201224159137

theorem tailTrace_268300 : CollatzResearch.WordTrace tailWord_268300 prefixEnd_268300 30614857689201224159137 := by
  unfold tailWord_268300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4892852464001198418517177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6523803285334931224689569 4892852464001198418517177)
  ·
    refine ⟨3669639348000898813887883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4892852464001198418517177 3669639348000898813887883)
    ·
      refine ⟨5504459022001348220831825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3669639348000898813887883 5504459022001348220831825)
      ·
        refine ⟨4128344266501011165623869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5504459022001348220831825 4128344266501011165623869)
        ·
          refine ⟨1548129099937879187108951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4128344266501011165623869 1548129099937879187108951)
          ·
            refine ⟨2322193649906818780663427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548129099937879187108951 2322193649906818780663427)
            ·
              refine ⟨3483290474860228170995141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2322193649906818780663427 3483290474860228170995141)
              ·
                refine ⟨653116964036292782061589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3483290474860228170995141 653116964036292782061589)
                ·
                  refine ⟨30614857689201224159137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 653116964036292782061589 30614857689201224159137)
                  ·
                    rfl

theorem cell22_268300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_268300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268300 prefixEnd_268300 := by exact prefixLift 268300
  have htrace : WordTrace (prefixWord ++ tailWord_268300) baseStart_268300 baseEnd_268300 := by
    simpa [prefixWord, tailWord_268300, baseEnd_268300] using wordTrace_append hprefix tailTrace_268300
  have hstable : (prefixWord ++ tailWord_268300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268300).length < 2 ^ (prefixWord ++ tailWord_268300).sum := by decide
  have hdescent : baseEnd_268300 < baseStart_268300 := by decide
  rcases family_descends (prefixWord ++ tailWord_268300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268334 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_268334 : Nat := 118140960795 + 268334 * 2 ^ 59
def prefixEnd_268334 : Nat := 4983230072969 + 3 ^ 40 * 268334 * 2
def baseEnd_268334 : Nat := 30618737320812972375769

theorem tailTrace_268334 : CollatzResearch.WordTrace tailWord_268334 prefixEnd_268334 30618737320812972375769 := by
  unfold tailWord_268334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223368126234902580471507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6524630006586147095848037 1223368126234902580471507)
  ·
    refine ⟨1835052189352353870707261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1223368126234902580471507 1835052189352353870707261)
    ·
      refine ⟨688144571007132701515223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1835052189352353870707261 688144571007132701515223)
      ·
        refine ⟨1032216856510699052272835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688144571007132701515223 1032216856510699052272835)
        ·
          refine ⟨1548325284766048578409253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032216856510699052272835 1548325284766048578409253)
          ·
            refine ⟨290310990893634108451735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1548325284766048578409253 290310990893634108451735)
            ·
              refine ⟨435466486340451162677603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290310990893634108451735 435466486340451162677603)
              ·
                refine ⟨653199729510676744016405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435466486340451162677603 653199729510676744016405)
                ·
                  refine ⟨30618737320812972375769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 653199729510676744016405 30618737320812972375769)
                  ·
                    rfl

theorem cell22_268334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_268334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268334 prefixEnd_268334 := by exact prefixLift 268334
  have htrace : WordTrace (prefixWord ++ tailWord_268334) baseStart_268334 baseEnd_268334 := by
    simpa [prefixWord, tailWord_268334, baseEnd_268334] using wordTrace_append hprefix tailTrace_268334
  have hstable : (prefixWord ++ tailWord_268334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268334).length < 2 ^ (prefixWord ++ tailWord_268334).sum := by decide
  have hdescent : baseEnd_268334 < baseStart_268334 := by decide
  rcases family_descends (prefixWord ++ tailWord_268334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268349 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_268349 : Nat := 118140960795 + 268349 * 2 ^ 59
def prefixEnd_268349 : Nat := 4983230072969 + 3 ^ 40 * 268349 * 2
def baseEnd_268349 : Nat := 91861346768983878002261

theorem tailTrace_268349 : CollatzResearch.WordTrace tailWord_268349 prefixEnd_268349 91861346768983878002261 := by
  unfold tailWord_268349
  simp only [CollatzResearch.WordTrace]
  refine ⟨9787492104824878205568101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6524994736549918803712067 9787492104824878205568101)
  ·
    refine ⟨1835154769654664663544019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9787492104824878205568101 1835154769654664663544019)
    ·
      refine ⟨2752732154481996995316029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1835154769654664663544019 2752732154481996995316029)
      ·
        refine ⟨1032274557930748873243511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2752732154481996995316029 1032274557930748873243511)
        ·
          refine ⟨1548411836896123309865267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032274557930748873243511 1548411836896123309865267)
          ·
            refine ⟨2322617755344184964797901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548411836896123309865267 2322617755344184964797901)
            ·
              refine ⟨870981658254069361799213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2322617755344184964797901 870981658254069361799213)
              ·
                refine ⟨326618121845276010674705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 870981658254069361799213 326618121845276010674705)
                ·
                  refine ⟨244963591383957008006029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326618121845276010674705 244963591383957008006029)
                  ·
                    refine ⟨91861346768983878002261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244963591383957008006029 91861346768983878002261)
                    ·
                      rfl

theorem cell22_268349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_268349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268349 prefixEnd_268349 := by exact prefixLift 268349
  have htrace : WordTrace (prefixWord ++ tailWord_268349) baseStart_268349 baseEnd_268349 := by
    simpa [prefixWord, tailWord_268349, baseEnd_268349] using wordTrace_append hprefix tailTrace_268349
  have hstable : (prefixWord ++ tailWord_268349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268349).length < 2 ^ (prefixWord ++ tailWord_268349).sum := by decide
  have hdescent : baseEnd_268349 < baseStart_268349 := by decide
  rcases family_descends (prefixWord ++ tailWord_268349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268407 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 5]
def baseStart_268407 : Nat := 118140960795 + 268407 * 2 ^ 59
def prefixEnd_268407 : Nat := 4983230072969 + 3 ^ 40 * 268407 * 2
def baseEnd_268407 : Nat := 30627067118097020017361

theorem tailTrace_268407 : CollatzResearch.WordTrace tailWord_268407 prefixEnd_268407 30627067118097020017361 := by
  unfold tailWord_268407
  simp only [CollatzResearch.WordTrace]
  refine ⟨9789607538614754111179475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6526405025743169407452983 9789607538614754111179475)
  ·
    refine ⟨14684411307922131166769213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9789607538614754111179475 14684411307922131166769213)
    ·
      refine ⟨5506654240470799187538455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14684411307922131166769213 5506654240470799187538455)
      ·
        refine ⟨8259981360706198781307683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5506654240470799187538455 8259981360706198781307683)
        ·
          refine ⟨12389972041059298171961525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8259981360706198781307683 12389972041059298171961525)
          ·
            refine ⟨1161559878849309203621393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12389972041059298171961525 1161559878849309203621393)
            ·
              refine ⟨871169909136981902716045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161559878849309203621393 871169909136981902716045)
              ·
                refine ⟨326688715926368213518517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 871169909136981902716045 326688715926368213518517)
                ·
                  refine ⟨30627067118097020017361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326688715926368213518517 30627067118097020017361)
                  ·
                    rfl

theorem cell22_268407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 5].length) (baseStart_268407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268407 prefixEnd_268407 := by exact prefixLift 268407
  have htrace : WordTrace (prefixWord ++ tailWord_268407) baseStart_268407 baseEnd_268407 := by
    simpa [prefixWord, tailWord_268407, baseEnd_268407] using wordTrace_append hprefix tailTrace_268407
  have hstable : (prefixWord ++ tailWord_268407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268407).length < 2 ^ (prefixWord ++ tailWord_268407).sum := by decide
  have hdescent : baseEnd_268407 < baseStart_268407 := by decide
  rcases family_descends (prefixWord ++ tailWord_268407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268435 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 10]
def baseStart_268435 : Nat := 118140960795 + 268435 * 2 ^ 59
def prefixEnd_268435 : Nat := 4983230072969 + 3 ^ 40 * 268435 * 2
def baseEnd_268435 : Nat := 30630262108836106783999

theorem tailTrace_268435 : CollatzResearch.WordTrace tailWord_268435 prefixEnd_268435 30630262108836106783999 := by
  unfold tailWord_268435
  simp only [CollatzResearch.WordTrace]
  refine ⟨9790628782513314893198759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6527085855008876595465839 9790628782513314893198759)
  ·
    refine ⟨14685943173769972339798139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9790628782513314893198759 14685943173769972339798139)
    ·
      refine ⟨22028914760654958509697209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14685943173769972339798139 22028914760654958509697209)
      ·
        refine ⟨16521686070491218882272907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22028914760654958509697209 16521686070491218882272907)
        ·
          refine ⟨24782529105736828323409361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16521686070491218882272907 24782529105736828323409361)
          ·
            refine ⟨18586896829302621242557021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24782529105736828323409361 18586896829302621242557021)
            ·
              refine ⟨6970086310988482965958883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18586896829302621242557021 6970086310988482965958883)
              ·
                refine ⟨10455129466482724448938325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6970086310988482965958883 10455129466482724448938325)
                ·
                  refine ⟨30630262108836106783999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 10455129466482724448938325 30630262108836106783999)
                  ·
                    rfl

theorem cell22_268435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 10].length) (baseStart_268435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268435 prefixEnd_268435 := by exact prefixLift 268435
  have htrace : WordTrace (prefixWord ++ tailWord_268435) baseStart_268435 baseEnd_268435 := by
    simpa [prefixWord, tailWord_268435, baseEnd_268435] using wordTrace_append hprefix tailTrace_268435
  have hstable : (prefixWord ++ tailWord_268435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268435).length < 2 ^ (prefixWord ++ tailWord_268435).sum := by decide
  have hdescent : baseEnd_268435 < baseStart_268435 := by decide
  rcases family_descends (prefixWord ++ tailWord_268435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268458 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_268458 : Nat := 118140960795 + 268458 * 2 ^ 59
def prefixEnd_268458 : Nat := 4983230072969 + 3 ^ 40 * 268458 * 2
def baseEnd_268458 : Nat := 30632886565514642342309

theorem tailTrace_268458 : CollatzResearch.WordTrace tailWord_268458 prefixEnd_268458 30632886565514642342309 := by
  unfold tailWord_268458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447866915357497455321507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6527645107619993214190685 2447866915357497455321507)
  ·
    refine ⟨3671800373036246182982261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2447866915357497455321507 3671800373036246182982261)
    ·
      refine ⟨344231284972148079654587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3671800373036246182982261 344231284972148079654587)
      ·
        refine ⟨516346927458222119481881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344231284972148079654587 516346927458222119481881)
        ·
          refine ⟨387260195593666589611411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516346927458222119481881 387260195593666589611411)
          ·
            refine ⟨580890293390499884417117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387260195593666589611411 580890293390499884417117)
            ·
              refine ⟨217833860021437456656419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580890293390499884417117 217833860021437456656419)
              ·
                refine ⟨326750790032156184984629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217833860021437456656419 326750790032156184984629)
                ·
                  refine ⟨30632886565514642342309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326750790032156184984629 30632886565514642342309)
                  ·
                    rfl

theorem cell22_268458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_268458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268458 prefixEnd_268458 := by exact prefixLift 268458
  have htrace : WordTrace (prefixWord ++ tailWord_268458) baseStart_268458 baseEnd_268458 := by
    simpa [prefixWord, tailWord_268458, baseEnd_268458] using wordTrace_append hprefix tailTrace_268458
  have hstable : (prefixWord ++ tailWord_268458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268458).length < 2 ^ (prefixWord ++ tailWord_268458).sum := by decide
  have hdescent : baseEnd_268458 < baseStart_268458 := by decide
  rcases family_descends (prefixWord ++ tailWord_268458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268529 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 3, 3]
def baseStart_268529 : Nat := 118140960795 + 268529 * 2 ^ 59
def prefixEnd_268529 : Nat := 4983230072969 + 3 ^ 40 * 268529 * 2
def baseEnd_268529 : Nat := 91922964447523408501709

theorem tailTrace_268529 : CollatzResearch.WordTrace tailWord_268529 prefixEnd_268529 91922964447523408501709 := by
  unfold tailWord_268529
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794057244172768947120641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6529371496115179298080427 9794057244172768947120641)
  ·
    refine ⟨7345542933129576710340481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9794057244172768947120641 7345542933129576710340481)
    ·
      refine ⟨5509157199847182532755361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7345542933129576710340481 5509157199847182532755361)
      ·
        refine ⟨4131867899885386899566521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5509157199847182532755361 4131867899885386899566521)
        ·
          refine ⟨3098900924914040174674891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4131867899885386899566521 3098900924914040174674891)
          ·
            refine ⟨4648351387371060262012337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3098900924914040174674891 4648351387371060262012337)
            ·
              refine ⟨3486263540528295196509253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4648351387371060262012337 3486263540528295196509253)
              ·
                refine ⟨653674413849055349345485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3486263540528295196509253 653674413849055349345485)
                ·
                  refine ⟨245127905193395756004557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653674413849055349345485 245127905193395756004557)
                  ·
                    refine ⟨91922964447523408501709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245127905193395756004557 91922964447523408501709)
                    ·
                      rfl

theorem cell22_268529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_268529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268529 prefixEnd_268529 := by exact prefixLift 268529
  have htrace : WordTrace (prefixWord ++ tailWord_268529) baseStart_268529 baseEnd_268529 := by
    simpa [prefixWord, tailWord_268529, baseEnd_268529] using wordTrace_append hprefix tailTrace_268529
  have hstable : (prefixWord ++ tailWord_268529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268529).length < 2 ^ (prefixWord ++ tailWord_268529).sum := by decide
  have hdescent : baseEnd_268529 < baseStart_268529 := by decide
  rcases family_descends (prefixWord ++ tailWord_268529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268679 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 2, 6]
def baseStart_268679 : Nat := 118140960795 + 268679 * 2 ^ 59
def prefixEnd_268679 : Nat := 4983230072969 + 3 ^ 40 * 268679 * 2
def baseEnd_268679 : Nat := 91974312512973017251249

theorem tailTrace_268679 : CollatzResearch.WordTrace tailWord_268679 prefixEnd_268679 91974312512973017251249 := by
  unfold tailWord_268679
  simp only [CollatzResearch.WordTrace]
  refine ⟨9799528193629344565081091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6533018795752896376720727 9799528193629344565081091)
  ·
    refine ⟨14699292290444016847621637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9799528193629344565081091 14699292290444016847621637)
    ·
      refine ⟨2756117304458253158929057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14699292290444016847621637 2756117304458253158929057)
      ·
        refine ⟨2067087978343689869196793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2756117304458253158929057 2067087978343689869196793)
        ·
          refine ⟨1550315983757767401897595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2067087978343689869196793 1550315983757767401897595)
          ·
            refine ⟨2325473975636651102846393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550315983757767401897595 2325473975636651102846393)
            ·
              refine ⟨1744105481727488327134795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2325473975636651102846393 1744105481727488327134795)
              ·
                refine ⟨2616158222591232490702193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744105481727488327134795 2616158222591232490702193)
                ·
                  refine ⟨1962118666943424368026645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2616158222591232490702193 1962118666943424368026645)
                  ·
                    refine ⟨91974312512973017251249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1962118666943424368026645 91974312512973017251249)
                    ·
                      rfl

theorem cell22_268679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_268679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268679 prefixEnd_268679 := by exact prefixLift 268679
  have htrace : WordTrace (prefixWord ++ tailWord_268679) baseStart_268679 baseEnd_268679 := by
    simpa [prefixWord, tailWord_268679, baseEnd_268679] using wordTrace_append hprefix tailTrace_268679
  have hstable : (prefixWord ++ tailWord_268679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268679).length < 2 ^ (prefixWord ++ tailWord_268679).sum := by decide
  have hdescent : baseEnd_268679 < baseStart_268679 := by decide
  rcases family_descends (prefixWord ++ tailWord_268679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268732 : List Nat := [2, 2, 2, 4, 1, 1, 4, 2, 1, 3]
def baseStart_268732 : Nat := 118140960795 + 268732 * 2 ^ 59
def prefixEnd_268732 : Nat := 4983230072969 + 3 ^ 40 * 268732 * 2
def baseEnd_268732 : Nat := 91992455496098545676087

theorem tailTrace_268732 : CollatzResearch.WordTrace tailWord_268732 prefixEnd_268732 91992455496098545676087 := by
  unfold tailWord_268732
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900730631218667308380225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6534307508291556411173633 4900730631218667308380225)
  ·
    refine ⟨3675547973414000481285169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4900730631218667308380225 3675547973414000481285169)
    ·
      refine ⟨2756660980060500360963877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3675547973414000481285169 2756660980060500360963877)
      ·
        refine ⟨516873933761343817680727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2756660980060500360963877 516873933761343817680727)
        ·
          refine ⟨775310900642015726521091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516873933761343817680727 775310900642015726521091)
          ·
            refine ⟨1162966350963023589781637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775310900642015726521091 1162966350963023589781637)
            ·
              refine ⟨218056190805566923084057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1162966350963023589781637 218056190805566923084057)
              ·
                refine ⟨163542143104175192313043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218056190805566923084057 163542143104175192313043)
                ·
                  refine ⟨245313214656262788469565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163542143104175192313043 245313214656262788469565)
                  ·
                    refine ⟨91992455496098545676087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245313214656262788469565 91992455496098545676087)
                    ·
                      rfl

theorem cell22_268732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_268732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268732 prefixEnd_268732 := by exact prefixLift 268732
  have htrace : WordTrace (prefixWord ++ tailWord_268732) baseStart_268732 baseEnd_268732 := by
    simpa [prefixWord, tailWord_268732, baseEnd_268732] using wordTrace_append hprefix tailTrace_268732
  have hstable : (prefixWord ++ tailWord_268732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268732).length < 2 ^ (prefixWord ++ tailWord_268732).sum := by decide
  have hdescent : baseEnd_268732 < baseStart_268732 := by decide
  rcases family_descends (prefixWord ++ tailWord_268732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268739 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 6]
def baseStart_268739 : Nat := 118140960795 + 268739 * 2 ^ 59
def prefixEnd_268739 : Nat := 4983230072969 + 3 ^ 40 * 268739 * 2
def baseEnd_268739 : Nat := 30664950579717620250355

theorem tailTrace_268739 : CollatzResearch.WordTrace tailWord_268739 prefixEnd_268739 30664950579717620250355 := by
  unfold tailWord_268739
  simp only [CollatzResearch.WordTrace]
  refine ⟨9801716573411974812265271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6534477715607983208176847 9801716573411974812265271)
  ·
    refine ⟨14702574860117962218397907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9801716573411974812265271 14702574860117962218397907)
    ·
      refine ⟨22053862290176943327596861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14702574860117962218397907 22053862290176943327596861)
      ·
        refine ⟨8270198358816353747848823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22053862290176943327596861 8270198358816353747848823)
        ·
          refine ⟨12405297538224530621773235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8270198358816353747848823 12405297538224530621773235)
          ·
            refine ⟨18607946307336795932659853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12405297538224530621773235 18607946307336795932659853)
            ·
              refine ⟨6977979865251298474747445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18607946307336795932659853 6977979865251298474747445)
              ·
                refine ⟨654185612367309232007573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6977979865251298474747445 654185612367309232007573)
                ·
                  refine ⟨30664950579717620250355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 654185612367309232007573 30664950579717620250355)
                  ·
                    rfl

theorem cell22_268739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 6].length) (baseStart_268739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268739 prefixEnd_268739 := by exact prefixLift 268739
  have htrace : WordTrace (prefixWord ++ tailWord_268739) baseStart_268739 baseEnd_268739 := by
    simpa [prefixWord, tailWord_268739, baseEnd_268739] using wordTrace_append hprefix tailTrace_268739
  have hstable : (prefixWord ++ tailWord_268739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268739).length < 2 ^ (prefixWord ++ tailWord_268739).sum := by decide
  have hdescent : baseEnd_268739 < baseStart_268739 := by decide
  rcases family_descends (prefixWord ++ tailWord_268739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268756 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 8]
def baseStart_268756 : Nat := 118140960795 + 268756 * 2 ^ 59
def prefixEnd_268756 : Nat := 4983230072969 + 3 ^ 40 * 268756 * 2
def baseEnd_268756 : Nat := 30666890395523494358671

theorem tailTrace_268756 : CollatzResearch.WordTrace tailWord_268756 prefixEnd_268756 30666890395523494358671 := by
  unfold tailWord_268756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4901168307175193357817061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6534891076233591143756081 4901168307175193357817061)
  ·
    refine ⟨918969057595348754590699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4901168307175193357817061 918969057595348754590699)
    ·
      refine ⟨1378453586393023131886049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 918969057595348754590699 1378453586393023131886049)
      ·
        refine ⟨1033840189794767348914537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1378453586393023131886049 1033840189794767348914537)
        ·
          refine ⟨775380142346075511685903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1033840189794767348914537 775380142346075511685903)
          ·
            refine ⟨1163070213519113267528855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775380142346075511685903 1163070213519113267528855)
            ·
              refine ⟨1744605320278669901293283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163070213519113267528855 1744605320278669901293283)
              ·
                refine ⟨2616907980418004851939925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744605320278669901293283 2616907980418004851939925)
                ·
                  refine ⟨30666890395523494358671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2616907980418004851939925 30666890395523494358671)
                  ·
                    rfl

theorem cell22_268756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_268756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268756 prefixEnd_268756 := by exact prefixLift 268756
  have htrace : WordTrace (prefixWord ++ tailWord_268756) baseStart_268756 baseEnd_268756 := by
    simpa [prefixWord, tailWord_268756, baseEnd_268756] using wordTrace_append hprefix tailTrace_268756
  have hstable : (prefixWord ++ tailWord_268756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268756).length < 2 ^ (prefixWord ++ tailWord_268756).sum := by decide
  have hdescent : baseEnd_268756 < baseStart_268756 := by decide
  rcases family_descends (prefixWord ++ tailWord_268756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268758 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_268758 : Nat := 118140960795 + 268758 * 2 ^ 59
def prefixEnd_268758 : Nat := 4983230072969 + 3 ^ 40 * 268758 * 2
def baseEnd_268758 : Nat := 92001355827443144526007

theorem tailTrace_268758 : CollatzResearch.WordTrace tailWord_268758 prefixEnd_268758 92001355827443144526007 := by
  unfold tailWord_268758
  simp only [CollatzResearch.WordTrace]
  refine ⟨612650597521446316075433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6534939706895427371471285 612650597521446316075433)
  ·
    refine ⟨459487948141084737056575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 612650597521446316075433 459487948141084737056575)
    ·
      refine ⟨689231922211627105584863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459487948141084737056575 689231922211627105584863)
      ·
        refine ⟨1033847883317440658377295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689231922211627105584863 1033847883317440658377295)
        ·
          refine ⟨1550771824976160987565943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033847883317440658377295 1550771824976160987565943)
          ·
            refine ⟨2326157737464241481348915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550771824976160987565943 2326157737464241481348915)
            ·
              refine ⟨3489236606196362222023373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326157737464241481348915 3489236606196362222023373)
              ·
                refine ⟨1308463727323635833258765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3489236606196362222023373 1308463727323635833258765)
                ·
                  refine ⟨490673897746363437472037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1308463727323635833258765 490673897746363437472037)
                  ·
                    refine ⟨92001355827443144526007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 490673897746363437472037 92001355827443144526007)
                    ·
                      rfl

theorem cell22_268758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_268758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268758 prefixEnd_268758 := by exact prefixLift 268758
  have htrace : WordTrace (prefixWord ++ tailWord_268758) baseStart_268758 baseEnd_268758 := by
    simpa [prefixWord, tailWord_268758, baseEnd_268758] using wordTrace_append hprefix tailTrace_268758
  have hstable : (prefixWord ++ tailWord_268758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268758).length < 2 ^ (prefixWord ++ tailWord_268758).sum := by decide
  have hdescent : baseEnd_268758 < baseStart_268758 := by decide
  rcases family_descends (prefixWord ++ tailWord_268758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268784 : List Nat := [2, 1, 1, 1, 3, 3, 11]
def baseStart_268784 : Nat := 118140960795 + 268784 * 2 ^ 59
def prefixEnd_268784 : Nat := 4983230072969 + 3 ^ 40 * 268784 * 2
def baseEnd_268784 : Nat := 3407787265140286791701

theorem tailTrace_268784 : CollatzResearch.WordTrace tailWord_268784 prefixEnd_268784 3407787265140286791701 := by
  unfold tailWord_268784
  simp only [CollatzResearch.WordTrace]
  refine ⟨4901678929124473748826703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6535571905499298331768937 4901678929124473748826703)
  ·
    refine ⟨7352518393686710623240055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4901678929124473748826703 7352518393686710623240055)
    ·
      refine ⟨11028777590530065934860083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7352518393686710623240055 11028777590530065934860083)
      ·
        refine ⟨16543166385795098902290125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11028777590530065934860083 16543166385795098902290125)
        ·
          refine ⟨6203687394673162088358797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16543166385795098902290125 6203687394673162088358797)
          ·
            refine ⟨2326382773002435783134549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6203687394673162088358797 2326382773002435783134549)
            ·
              refine ⟨3407787265140286791701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2326382773002435783134549 3407787265140286791701)
              ·
                rfl

theorem cell22_268784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 11].length) (baseStart_268784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268784 prefixEnd_268784 := by exact prefixLift 268784
  have htrace : WordTrace (prefixWord ++ tailWord_268784) baseStart_268784 baseEnd_268784 := by
    simpa [prefixWord, tailWord_268784, baseEnd_268784] using wordTrace_append hprefix tailTrace_268784
  have hstable : (prefixWord ++ tailWord_268784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268784).length < 2 ^ (prefixWord ++ tailWord_268784).sum := by decide
  have hdescent : baseEnd_268784 < baseStart_268784 := by decide
  rcases family_descends (prefixWord ++ tailWord_268784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268816 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 9, 3]
def baseStart_268816 : Nat := 118140960795 + 268816 * 2 ^ 59
def prefixEnd_268816 : Nat := 4983230072969 + 3 ^ 40 * 268816 * 2
def baseEnd_268816 : Nat := 92021210412750326575829

theorem tailTrace_268816 : CollatzResearch.WordTrace tailWord_268816 prefixEnd_268816 92021210412750326575829 := by
  unfold tailWord_268816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4902262497066508481409151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6536349996088677975212201 4902262497066508481409151)
  ·
    refine ⟨7353393745599762722113727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4902262497066508481409151 7353393745599762722113727)
    ·
      refine ⟨11030090618399644083170591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7353393745599762722113727 11030090618399644083170591)
      ·
        refine ⟨16545135927599466124755887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11030090618399644083170591 16545135927599466124755887)
        ·
          refine ⟨24817703891399199187133831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16545135927599466124755887 24817703891399199187133831)
          ·
            refine ⟨37226555837098798780700747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24817703891399199187133831 37226555837098798780700747)
            ·
              refine ⟨55839833755648198171051121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37226555837098798780700747 55839833755648198171051121)
              ·
                refine ⟨41879875316736148628288341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55839833755648198171051121 41879875316736148628288341)
                ·
                  refine ⟨245389894434000870868877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41879875316736148628288341 245389894434000870868877)
                  ·
                    refine ⟨92021210412750326575829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245389894434000870868877 92021210412750326575829)
                    ·
                      rfl

theorem cell22_268816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9, 3].length) (baseStart_268816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268816 prefixEnd_268816 := by exact prefixLift 268816
  have htrace : WordTrace (prefixWord ++ tailWord_268816) baseStart_268816 baseEnd_268816 := by
    simpa [prefixWord, tailWord_268816, baseEnd_268816] using wordTrace_append hprefix tailTrace_268816
  have hstable : (prefixWord ++ tailWord_268816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268816).length < 2 ^ (prefixWord ++ tailWord_268816).sum := by decide
  have hdescent : baseEnd_268816 < baseStart_268816 := by decide
  rcases family_descends (prefixWord ++ tailWord_268816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268850 : List Nat := [3, 2, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_268850 : Nat := 118140960795 + 268850 * 2 ^ 59
def prefixEnd_268850 : Nat := 4983230072969 + 3 ^ 40 * 268850 * 2
def baseEnd_268850 : Nat := 92032849307585571225725

theorem tailTrace_268850 : CollatzResearch.WordTrace tailWord_268850 prefixEnd_268850 92032849307585571225725 := by
  unfold tailWord_268850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451441269002460192389001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6537176717339893846370669 2451441269002460192389001)
  ·
    refine ⟨1838580951751845144291751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2451441269002460192389001 1838580951751845144291751)
    ·
      refine ⟨2757871427627767716437627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1838580951751845144291751 2757871427627767716437627)
      ·
        refine ⟨4136807141441651574656441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2757871427627767716437627 4136807141441651574656441)
        ·
          refine ⟨3102605356081238680992331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4136807141441651574656441 3102605356081238680992331)
          ·
            refine ⟨4653908034121858021488497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102605356081238680992331 4653908034121858021488497)
            ·
              refine ⟨3490431025591393516116373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4653908034121858021488497 3490431025591393516116373)
              ·
                refine ⟨163613954324596571067955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3490431025591393516116373 163613954324596571067955)
                ·
                  refine ⟨245420931486894856601933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163613954324596571067955 245420931486894856601933)
                  ·
                    refine ⟨92032849307585571225725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245420931486894856601933 92032849307585571225725)
                    ·
                      rfl

theorem cell22_268850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_268850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268850 prefixEnd_268850 := by exact prefixLift 268850
  have htrace : WordTrace (prefixWord ++ tailWord_268850) baseStart_268850 baseEnd_268850 := by
    simpa [prefixWord, tailWord_268850, baseEnd_268850] using wordTrace_append hprefix tailTrace_268850
  have hstable : (prefixWord ++ tailWord_268850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268850).length < 2 ^ (prefixWord ++ tailWord_268850).sum := by decide
  have hdescent : baseEnd_268850 < baseStart_268850 := by decide
  rcases family_descends (prefixWord ++ tailWord_268850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268901 : List Nat := [1, 3, 1, 3, 5, 1, 2, 2, 1, 3]
def baseStart_268901 : Nat := 118140960795 + 268901 * 2 ^ 59
def prefixEnd_268901 : Nat := 4983230072969 + 3 ^ 40 * 268901 * 2
def baseEnd_268901 : Nat := 92050307649838438200569

theorem tailTrace_268901 : CollatzResearch.WordTrace tailWord_268901 prefixEnd_268901 92050307649838438200569 := by
  unfold tailWord_268901
  simp only [CollatzResearch.WordTrace]
  refine ⟨9807625198825076479662557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6538416799216717653108371 9807625198825076479662557)
  ·
    refine ⟨3677859449559403679873459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9807625198825076479662557 3677859449559403679873459)
    ·
      refine ⟨5516789174339105519810189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3677859449559403679873459 5516789174339105519810189)
      ·
        refine ⟨2068795940377164569928821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5516789174339105519810189 2068795940377164569928821)
        ·
          refine ⟨193949619410359178430827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2068795940377164569928821 193949619410359178430827)
          ·
            refine ⟨290924429115538767646241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193949619410359178430827 290924429115538767646241)
            ·
              refine ⟨218193321836654075734681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290924429115538767646241 218193321836654075734681)
              ·
                refine ⟨163644991377490556801011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218193321836654075734681 163644991377490556801011)
                ·
                  refine ⟨245467487066235835201517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163644991377490556801011 245467487066235835201517)
                  ·
                    refine ⟨92050307649838438200569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245467487066235835201517 92050307649838438200569)
                    ·
                      rfl

theorem cell22_268901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_268901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268901 prefixEnd_268901 := by exact prefixLift 268901
  have htrace : WordTrace (prefixWord ++ tailWord_268901) baseStart_268901 baseEnd_268901 := by
    simpa [prefixWord, tailWord_268901, baseEnd_268901] using wordTrace_append hprefix tailTrace_268901
  have hstable : (prefixWord ++ tailWord_268901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268901).length < 2 ^ (prefixWord ++ tailWord_268901).sum := by decide
  have hdescent : baseEnd_268901 < baseStart_268901 := by decide
  rcases family_descends (prefixWord ++ tailWord_268901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269092 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_269092 : Nat := 118140960795 + 269092 * 2 ^ 59
def prefixEnd_269092 : Nat := 4983230072969 + 3 ^ 40 * 269092 * 2
def baseEnd_269092 : Nat := 92115690853177606674983

theorem tailTrace_269092 : CollatzResearch.WordTrace tailWord_269092 prefixEnd_269092 92115690853177606674983 := by
  unfold tailWord_269092
  simp only [CollatzResearch.WordTrace]
  refine ⟨4907295770566558049932765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6543061027422077399910353 4907295770566558049932765)
  ·
    refine ⟨1840235913962459268724787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4907295770566558049932765 1840235913962459268724787)
    ·
      refine ⟨2760353870943688903087181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1840235913962459268724787 2760353870943688903087181)
      ·
        refine ⟨1035132701603883338657693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2760353870943688903087181 1035132701603883338657693)
        ·
          refine ⟨388174763101456251996635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1035132701603883338657693 388174763101456251996635)
          ·
            refine ⟨582262144652184377994953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388174763101456251996635 582262144652184377994953)
            ·
              refine ⟨436696608489138283496215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582262144652184377994953 436696608489138283496215)
              ·
                refine ⟨655044912733707425244323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436696608489138283496215 655044912733707425244323)
                ·
                  refine ⟨982567369100561137866485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655044912733707425244323 982567369100561137866485)
                  ·
                    refine ⟨92115690853177606674983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 982567369100561137866485 92115690853177606674983)
                    ·
                      rfl

theorem cell22_269092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_269092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269092 prefixEnd_269092 := by exact prefixLift 269092
  have htrace : WordTrace (prefixWord ++ tailWord_269092) baseStart_269092 baseEnd_269092 := by
    simpa [prefixWord, tailWord_269092, baseEnd_269092] using wordTrace_append hprefix tailTrace_269092
  have hstable : (prefixWord ++ tailWord_269092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269092).length < 2 ^ (prefixWord ++ tailWord_269092).sum := by decide
  have hdescent : baseEnd_269092 < baseStart_269092 := by decide
  rcases family_descends (prefixWord ++ tailWord_269092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269105 : List Nat := [1, 2, 2, 3, 2, 1, 5, 6]
def baseStart_269105 : Nat := 118140960795 + 269105 * 2 ^ 59
def prefixEnd_269105 : Nat := 4983230072969 + 3 ^ 40 * 269105 * 2
def baseEnd_269105 : Nat := 10235571224316656233327

theorem tailTrace_269105 : CollatzResearch.WordTrace tailWord_269105 prefixEnd_269105 10235571224316656233327 := by
  unfold tailWord_269105
  simp only [CollatzResearch.WordTrace]
  refine ⟨9815065690086019320088769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6543377126724012880059179 9815065690086019320088769)
  ·
    refine ⟨7361299267564514490066577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9815065690086019320088769 7361299267564514490066577)
    ·
      refine ⟨5520974450673385867549933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7361299267564514490066577 5520974450673385867549933)
      ·
        refine ⟨2070365419002519700331225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5520974450673385867549933 2070365419002519700331225)
        ·
          refine ⟨1552774064251889775248419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2070365419002519700331225 1552774064251889775248419)
          ·
            refine ⟨2329161096377834662872629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552774064251889775248419 2329161096377834662872629)
            ·
              refine ⟨218358852785421999644309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2329161096377834662872629 218358852785421999644309)
              ·
                refine ⟨10235571224316656233327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 218358852785421999644309 10235571224316656233327)
                ·
                  rfl

theorem cell22_269105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 6].length) (baseStart_269105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269105 prefixEnd_269105 := by exact prefixLift 269105
  have htrace : WordTrace (prefixWord ++ tailWord_269105) baseStart_269105 baseEnd_269105 := by
    simpa [prefixWord, tailWord_269105, baseEnd_269105] using wordTrace_append hprefix tailTrace_269105
  have hstable : (prefixWord ++ tailWord_269105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269105).length < 2 ^ (prefixWord ++ tailWord_269105).sum := by decide
  have hdescent : baseEnd_269105 < baseStart_269105 := by decide
  rcases family_descends (prefixWord ++ tailWord_269105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269107 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 2, 4]
def baseStart_269107 : Nat := 118140960795 + 269107 * 2 ^ 59
def prefixEnd_269107 : Nat := 4983230072969 + 3 ^ 40 * 269107 * 2
def baseEnd_269107 : Nat := 92120825659722567549937

theorem tailTrace_269107 : CollatzResearch.WordTrace tailWord_269107 prefixEnd_269107 92120825659722567549937 := by
  unfold tailWord_269107
  simp only [CollatzResearch.WordTrace]
  refine ⟨9815138636078773661661575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6543425757385849107774383 9815138636078773661661575)
  ·
    refine ⟨14722707954118160492492363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9815138636078773661661575 14722707954118160492492363)
    ·
      refine ⟨22084061931177240738738545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14722707954118160492492363 22084061931177240738738545)
      ·
        refine ⟨16563046448382930554053909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22084061931177240738738545 16563046448382930554053909)
        ·
          refine ⟨776392802267949869721277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16563046448382930554053909 776392802267949869721277)
          ·
            refine ⟨291147300850481201145479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 776392802267949869721277 291147300850481201145479)
            ·
              refine ⟨436720951275721801718219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291147300850481201145479 436720951275721801718219)
              ·
                refine ⟨655081426913582702577329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436720951275721801718219 655081426913582702577329)
                ·
                  refine ⟨491311070185187026932997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655081426913582702577329 491311070185187026932997)
                  ·
                    refine ⟨92120825659722567549937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 491311070185187026932997 92120825659722567549937)
                    ·
                      rfl

theorem cell22_269107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 4].length) (baseStart_269107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269107 prefixEnd_269107 := by exact prefixLift 269107
  have htrace : WordTrace (prefixWord ++ tailWord_269107) baseStart_269107 baseEnd_269107 := by
    simpa [prefixWord, tailWord_269107, baseEnd_269107] using wordTrace_append hprefix tailTrace_269107
  have hstable : (prefixWord ++ tailWord_269107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269107).length < 2 ^ (prefixWord ++ tailWord_269107).sum := by decide
  have hdescent : baseEnd_269107 < baseStart_269107 := by decide
  rcases family_descends (prefixWord ++ tailWord_269107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269126 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_269126 : Nat := 118140960795 + 269126 * 2 ^ 59
def prefixEnd_269126 : Nat := 4983230072969 + 3 ^ 40 * 269126 * 2
def baseEnd_269126 : Nat := 92127329748012851324879

theorem tailTrace_269126 : CollatzResearch.WordTrace tailWord_269126 prefixEnd_269126 92127329748012851324879 := by
  unfold tailWord_269126
  simp only [CollatzResearch.WordTrace]
  refine ⟨306744738219060622081351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6543887748673293271068821 306744738219060622081351)
  ·
    refine ⟨460117107328590933122027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 306744738219060622081351 460117107328590933122027)
    ·
      refine ⟨690175660992886399683041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 460117107328590933122027 690175660992886399683041)
      ·
        refine ⟨517631745744664799762281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 690175660992886399683041 517631745744664799762281)
        ·
          refine ⟨388223809308498599821711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517631745744664799762281 388223809308498599821711)
          ·
            refine ⟨582335713962747899732567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388223809308498599821711 582335713962747899732567)
            ·
              refine ⟨873503570944121849598851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582335713962747899732567 873503570944121849598851)
              ·
                refine ⟨1310255356416182774398277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873503570944121849598851 1310255356416182774398277)
                ·
                  refine ⟨245672879328034270199677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1310255356416182774398277 245672879328034270199677)
                  ·
                    refine ⟨92127329748012851324879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245672879328034270199677 92127329748012851324879)
                    ·
                      rfl

theorem cell22_269126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_269126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269126 prefixEnd_269126 := by exact prefixLift 269126
  have htrace : WordTrace (prefixWord ++ tailWord_269126) baseStart_269126 baseEnd_269126 := by
    simpa [prefixWord, tailWord_269126, baseEnd_269126] using wordTrace_append hprefix tailTrace_269126
  have hstable : (prefixWord ++ tailWord_269126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269126).length < 2 ^ (prefixWord ++ tailWord_269126).sum := by decide
  have hdescent : baseEnd_269126 < baseStart_269126 := by decide
  rcases family_descends (prefixWord ++ tailWord_269126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269195 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 6]
def baseStart_269195 : Nat := 118140960795 + 269195 * 2 ^ 59
def prefixEnd_269195 : Nat := 4983230072969 + 3 ^ 40 * 269195 * 2
def baseEnd_269195 : Nat := 30716983286039890449889

theorem tailTrace_269195 : CollatzResearch.WordTrace tailWord_269195 prefixEnd_269195 30716983286039890449889 := by
  unfold tailWord_269195
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818348259759964690865039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6545565506506643127243359 9818348259759964690865039)
  ·
    refine ⟨14727522389639947036297559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9818348259759964690865039 14727522389639947036297559)
    ·
      refine ⟨22091283584459920554446339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14727522389639947036297559 22091283584459920554446339)
      ·
        refine ⟨33136925376689880831669509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22091283584459920554446339 33136925376689880831669509)
        ·
          refine ⟨6213173508129352655938033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33136925376689880831669509 6213173508129352655938033)
          ·
            refine ⟨4659880131097014491953525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6213173508129352655938033 4659880131097014491953525)
            ·
              refine ⟨436863762290345108620643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4659880131097014491953525 436863762290345108620643)
              ·
                refine ⟨655295643435517662930965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436863762290345108620643 655295643435517662930965)
                ·
                  refine ⟨30716983286039890449889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 655295643435517662930965 30716983286039890449889)
                  ·
                    rfl

theorem cell22_269195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 6].length) (baseStart_269195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269195 prefixEnd_269195 := by exact prefixLift 269195
  have htrace : WordTrace (prefixWord ++ tailWord_269195) baseStart_269195 baseEnd_269195 := by
    simpa [prefixWord, tailWord_269195, baseEnd_269195] using wordTrace_append hprefix tailTrace_269195
  have hstable : (prefixWord ++ tailWord_269195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269195).length < 2 ^ (prefixWord ++ tailWord_269195).sum := by decide
  have hdescent : baseEnd_269195 < baseStart_269195 := by decide
  rcases family_descends (prefixWord ++ tailWord_269195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269272 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 5, 3]
def baseStart_269272 : Nat := 118140960795 + 269272 * 2 ^ 59
def prefixEnd_269272 : Nat := 4983230072969 + 3 ^ 40 * 269272 * 2
def baseEnd_269272 : Nat := 92177308531717137174431

theorem tailTrace_269272 : CollatzResearch.WordTrace tailWord_269272 prefixEnd_269272 92177308531717137174431 := by
  unfold tailWord_269272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4910578340240503420709035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6547437786987337894278713 4910578340240503420709035)
  ·
    refine ⟨7365867510360755131063553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4910578340240503420709035 7365867510360755131063553)
    ·
      refine ⟨5524400632770566348297665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7365867510360755131063553 5524400632770566348297665)
      ·
        refine ⟨4143300474577924761223249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5524400632770566348297665 4143300474577924761223249)
        ·
          refine ⟨3107475355933443570917437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4143300474577924761223249 3107475355933443570917437)
          ·
            refine ⟨1165303258475041339094039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3107475355933443570917437 1165303258475041339094039)
            ·
              refine ⟨1747954887712562008641059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165303258475041339094039 1747954887712562008641059)
              ·
                refine ⟨2621932331568843012961589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747954887712562008641059 2621932331568843012961589)
                ·
                  refine ⟨245806156084579032465149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2621932331568843012961589 245806156084579032465149)
                  ·
                    refine ⟨92177308531717137174431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245806156084579032465149 92177308531717137174431)
                    ·
                      rfl

theorem cell22_269272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_269272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269272 prefixEnd_269272 := by exact prefixLift 269272
  have htrace : WordTrace (prefixWord ++ tailWord_269272) baseStart_269272 baseEnd_269272 := by
    simpa [prefixWord, tailWord_269272, baseEnd_269272] using wordTrace_append hprefix tailTrace_269272
  have hstable : (prefixWord ++ tailWord_269272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269272).length < 2 ^ (prefixWord ++ tailWord_269272).sum := by decide
  have hdescent : baseEnd_269272 < baseStart_269272 := by decide
  rcases family_descends (prefixWord ++ tailWord_269272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269319 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 5]
def baseStart_269319 : Nat := 118140960795 + 269319 * 2 ^ 59
def prefixEnd_269319 : Nat := 4983230072969 + 3 ^ 40 * 269319 * 2
def baseEnd_269319 : Nat := 30731132530741560416429

theorem tailTrace_269319 : CollatzResearch.WordTrace tailWord_269319 prefixEnd_269319 30731132530741560416429 := by
  unfold tailWord_269319
  simp only [CollatzResearch.WordTrace]
  refine ⟨9822870911310733868379011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6548580607540489245586007 9822870911310733868379011)
  ·
    refine ⟨14734306366966100802568517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9822870911310733868379011 14734306366966100802568517)
    ·
      refine ⟨2762682443806143900481597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14734306366966100802568517 2762682443806143900481597)
      ·
        refine ⟨1036005916427303962680599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2762682443806143900481597 1036005916427303962680599)
        ·
          refine ⟨1554008874640955944020899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036005916427303962680599 1554008874640955944020899)
          ·
            refine ⟨2331013311961433916031349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554008874640955944020899 2331013311961433916031349)
            ·
              refine ⟨218532497996384429627939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2331013311961433916031349 218532497996384429627939)
              ·
                refine ⟨327798746994576644441909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218532497996384429627939 327798746994576644441909)
                ·
                  refine ⟨30731132530741560416429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 327798746994576644441909 30731132530741560416429)
                  ·
                    rfl

theorem cell22_269319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 5].length) (baseStart_269319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269319 prefixEnd_269319 := by exact prefixLift 269319
  have htrace : WordTrace (prefixWord ++ tailWord_269319) baseStart_269319 baseEnd_269319 := by
    simpa [prefixWord, tailWord_269319, baseEnd_269319] using wordTrace_append hprefix tailTrace_269319
  have hstable : (prefixWord ++ tailWord_269319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269319).length < 2 ^ (prefixWord ++ tailWord_269319).sum := by decide
  have hdescent : baseEnd_269319 < baseStart_269319 := by decide
  rcases family_descends (prefixWord ++ tailWord_269319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269340 : List Nat := [2, 2, 3, 1, 5, 1, 1, 3, 1, 3]
def baseStart_269340 : Nat := 118140960795 + 269340 * 2 ^ 59
def prefixEnd_269340 : Nat := 4983230072969 + 3 ^ 40 * 269340 * 2
def baseEnd_269340 : Nat := 92200586321387626474223

theorem tailTrace_269340 : CollatzResearch.WordTrace tailWord_269340 prefixEnd_269340 92200586321387626474223 := by
  unfold tailWord_269340
  simp only [CollatzResearch.WordTrace]
  refine ⟨4911818422117327227446737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6549091229489769636595649 4911818422117327227446737)
  ·
    refine ⟨3683863816587995420585053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4911818422117327227446737 3683863816587995420585053)
    ·
      refine ⟨1381448931220498282719395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3683863816587995420585053 1381448931220498282719395)
      ·
        refine ⟨2072173396830747424079093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381448931220498282719395 2072173396830747424079093)
        ·
          refine ⟨194266255952882571007415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2072173396830747424079093 194266255952882571007415)
          ·
            refine ⟨291399383929323856511123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194266255952882571007415 291399383929323856511123)
            ·
              refine ⟨437099075893985784766685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291399383929323856511123 437099075893985784766685)
              ·
                refine ⟨163912153460244669287507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 437099075893985784766685 163912153460244669287507)
                ·
                  refine ⟨245868230190367003931261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163912153460244669287507 245868230190367003931261)
                  ·
                    refine ⟨92200586321387626474223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245868230190367003931261 92200586321387626474223)
                    ·
                      rfl

theorem cell22_269340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_269340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269340 prefixEnd_269340 := by exact prefixLift 269340
  have htrace : WordTrace (prefixWord ++ tailWord_269340) baseStart_269340 baseEnd_269340 := by
    simpa [prefixWord, tailWord_269340, baseEnd_269340] using wordTrace_append hprefix tailTrace_269340
  have hstable : (prefixWord ++ tailWord_269340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269340).length < 2 ^ (prefixWord ++ tailWord_269340).sum := by decide
  have hdescent : baseEnd_269340 < baseStart_269340 := by decide
  rcases family_descends (prefixWord ++ tailWord_269340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269379 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 2, 3]
def baseStart_269379 : Nat := 118140960795 + 269379 * 2 ^ 59
def prefixEnd_269379 : Nat := 4983230072969 + 3 ^ 40 * 269379 * 2
def baseEnd_269379 : Nat := 92213936818404524749103

theorem tailTrace_269379 : CollatzResearch.WordTrace tailWord_269379 prefixEnd_269379 92213936818404524749103 := by
  unfold tailWord_269379
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825059291093364115563191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6550039527395576077042127 9825059291093364115563191)
  ·
    refine ⟨14737588936640046173344787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9825059291093364115563191 14737588936640046173344787)
    ·
      refine ⟨22106383404960069260017181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14737588936640046173344787 22106383404960069260017181)
      ·
        refine ⟨8289893776860025972506443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22106383404960069260017181 8289893776860025972506443)
        ·
          refine ⟨12434840665290038958759665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8289893776860025972506443 12434840665290038958759665)
          ·
            refine ⟨9326130498967529219069749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12434840665290038958759665 9326130498967529219069749)
            ·
              refine ⟨874324734278205864287789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9326130498967529219069749 874324734278205864287789)
              ·
                refine ⟨327871775354327199107921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 874324734278205864287789 327871775354327199107921)
                ·
                  refine ⟨245903831515745399330941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327871775354327199107921 245903831515745399330941)
                  ·
                    refine ⟨92213936818404524749103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245903831515745399330941 92213936818404524749103)
                    ·
                      rfl

theorem cell22_269379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 3].length) (baseStart_269379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269379 prefixEnd_269379 := by exact prefixLift 269379
  have htrace : WordTrace (prefixWord ++ tailWord_269379) baseStart_269379 baseEnd_269379 := by
    simpa [prefixWord, tailWord_269379, baseEnd_269379] using wordTrace_append hprefix tailTrace_269379
  have hstable : (prefixWord ++ tailWord_269379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269379).length < 2 ^ (prefixWord ++ tailWord_269379).sum := by decide
  have hdescent : baseEnd_269379 < baseStart_269379 := by decide
  rcases family_descends (prefixWord ++ tailWord_269379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269394 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_269394 : Nat := 118140960795 + 269394 * 2 ^ 59
def prefixEnd_269394 : Nat := 4983230072969 + 3 ^ 40 * 269394 * 2
def baseEnd_269394 : Nat := 92219071624949485624057

theorem tailTrace_269394 : CollatzResearch.WordTrace tailWord_269394 prefixEnd_269394 92219071624949485624057 := by
  unfold tailWord_269394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2456401596509755419339809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6550404257359347784906157 2456401596509755419339809)
  ·
    refine ⟨1842301197382316564504857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2456401596509755419339809 1842301197382316564504857)
    ·
      refine ⟨1381725898036737423378643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1842301197382316564504857 1381725898036737423378643)
      ·
        refine ⟨2072588847055106135067965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381725898036737423378643 2072588847055106135067965)
        ·
          refine ⟨777220817645664800650487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2072588847055106135067965 777220817645664800650487)
          ·
            refine ⟨1165831226468497200975731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777220817645664800650487 1165831226468497200975731)
            ·
              refine ⟨1748746839702745801463597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165831226468497200975731 1748746839702745801463597)
              ·
                refine ⟨655780064888529675548849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1748746839702745801463597 655780064888529675548849)
                ·
                  refine ⟨491835048666397256661637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655780064888529675548849 491835048666397256661637)
                  ·
                    refine ⟨92219071624949485624057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 491835048666397256661637 92219071624949485624057)
                    ·
                      rfl

theorem cell22_269394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_269394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269394 prefixEnd_269394 := by exact prefixLift 269394
  have htrace : WordTrace (prefixWord ++ tailWord_269394) baseStart_269394 baseEnd_269394 := by
    simpa [prefixWord, tailWord_269394, baseEnd_269394] using wordTrace_append hprefix tailTrace_269394
  have hstable : (prefixWord ++ tailWord_269394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269394).length < 2 ^ (prefixWord ++ tailWord_269394).sum := by decide
  have hdescent : baseEnd_269394 < baseStart_269394 := by decide
  rcases family_descends (prefixWord ++ tailWord_269394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269424 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 3, 3]
def baseStart_269424 : Nat := 118140960795 + 269424 * 2 ^ 59
def prefixEnd_269424 : Nat := 4983230072969 + 3 ^ 40 * 269424 * 2
def baseEnd_269424 : Nat := 92229341238039407373965

theorem tailTrace_269424 : CollatzResearch.WordTrace tailWord_269424 prefixEnd_269424 92229341238039407373965 := by
  unfold tailWord_269424
  simp only [CollatzResearch.WordTrace]
  refine ⟨4913350287965168400475663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6551133717286891200634217 4913350287965168400475663)
  ·
    refine ⟨7370025431947752600713495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4913350287965168400475663 7370025431947752600713495)
    ·
      refine ⟨11055038147921628901070243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7370025431947752600713495 11055038147921628901070243)
      ·
        refine ⟨16582557221882443351605365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11055038147921628901070243 16582557221882443351605365)
        ·
          refine ⟨1554614739551479064213003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16582557221882443351605365 1554614739551479064213003)
          ·
            refine ⟨2331922109327218596319505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554614739551479064213003 2331922109327218596319505)
            ·
              refine ⟨1748941581995413947239629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2331922109327218596319505 1748941581995413947239629)
              ·
                refine ⟨655853093248280230214861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1748941581995413947239629 655853093248280230214861)
                ·
                  refine ⟨245944909968105086330573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655853093248280230214861 245944909968105086330573)
                  ·
                    refine ⟨92229341238039407373965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245944909968105086330573 92229341238039407373965)
                    ·
                      rfl

theorem cell22_269424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3, 3].length) (baseStart_269424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269424 prefixEnd_269424 := by exact prefixLift 269424
  have htrace : WordTrace (prefixWord ++ tailWord_269424) baseStart_269424 baseEnd_269424 := by
    simpa [prefixWord, tailWord_269424, baseEnd_269424] using wordTrace_append hprefix tailTrace_269424
  have hstable : (prefixWord ++ tailWord_269424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269424).length < 2 ^ (prefixWord ++ tailWord_269424).sum := by decide
  have hdescent : baseEnd_269424 < baseStart_269424 := by decide
  rcases family_descends (prefixWord ++ tailWord_269424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269441 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 3, 3]
def baseStart_269441 : Nat := 118140960795 + 269441 * 2 ^ 59
def prefixEnd_269441 : Nat := 4983230072969 + 3 ^ 40 * 269441 * 2
def baseEnd_269441 : Nat := 92235160685457029698913

theorem tailTrace_269441 : CollatzResearch.WordTrace tailWord_269441 prefixEnd_269441 92235160685457029698913 := by
  unfold tailWord_269441
  simp only [CollatzResearch.WordTrace]
  refine ⟨9827320616868748704320177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6551547077912499136213451 9827320616868748704320177)
  ·
    refine ⟨7370490462651561528240133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9827320616868748704320177 7370490462651561528240133)
    ·
      refine ⟨1381966961747167786545025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7370490462651561528240133 1381966961747167786545025)
      ·
        refine ⟨1036475221310375839908769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1381966961747167786545025 1036475221310375839908769)
        ·
          refine ⟨777356415982781879931577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1036475221310375839908769 777356415982781879931577)
          ·
            refine ⟨583017311987086409948683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 777356415982781879931577 583017311987086409948683)
            ·
              refine ⟨874525967980629614923025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583017311987086409948683 874525967980629614923025)
              ·
                refine ⟨655894475985472211192269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874525967980629614923025 655894475985472211192269)
                ·
                  refine ⟨245960428494552079197101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655894475985472211192269 245960428494552079197101)
                  ·
                    refine ⟨92235160685457029698913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245960428494552079197101 92235160685457029698913)
                    ·
                      rfl

theorem cell22_269441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_269441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269441 prefixEnd_269441 := by exact prefixLift 269441
  have htrace : WordTrace (prefixWord ++ tailWord_269441) baseStart_269441 baseEnd_269441 := by
    simpa [prefixWord, tailWord_269441, baseEnd_269441] using wordTrace_append hprefix tailTrace_269441
  have hstable : (prefixWord ++ tailWord_269441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269441).length < 2 ^ (prefixWord ++ tailWord_269441).sum := by decide
  have hdescent : baseEnd_269441 < baseStart_269441 := by decide
  rcases family_descends (prefixWord ++ tailWord_269441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269458 : List Nat := [3, 2, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_269458 : Nat := 118140960795 + 269458 * 2 ^ 59
def prefixEnd_269458 : Nat := 4983230072969 + 3 ^ 40 * 269458 * 2
def baseEnd_269458 : Nat := 92240980132874652023861

theorem tailTrace_269458 : CollatzResearch.WordTrace tailWord_269458 prefixEnd_269458 92240980132874652023861 := by
  unfold tailWord_269458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2456985164451790151922257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6551960438538107071792685 2456985164451790151922257)
  ·
    refine ⟨1842738873338842613941693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2456985164451790151922257 1842738873338842613941693)
    ·
      refine ⟨691027077502065980228135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1842738873338842613941693 691027077502065980228135)
      ·
        refine ⟨1036540616253098970342203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691027077502065980228135 1036540616253098970342203)
        ·
          refine ⟨1554810924379648455513305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036540616253098970342203 1554810924379648455513305)
          ·
            refine ⟨1166108193284736341634979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1554810924379648455513305 1166108193284736341634979)
            ·
              refine ⟨1749162289927104512452469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166108193284736341634979 1749162289927104512452469)
              ·
                refine ⟨163983964680666048042419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1749162289927104512452469 163983964680666048042419)
                ·
                  refine ⟨245975947020999072063629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163983964680666048042419 245975947020999072063629)
                  ·
                    refine ⟨92240980132874652023861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245975947020999072063629 92240980132874652023861)
                    ·
                      rfl

theorem cell22_269458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_269458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269458 prefixEnd_269458 := by exact prefixLift 269458
  have htrace : WordTrace (prefixWord ++ tailWord_269458) baseStart_269458 baseEnd_269458 := by
    simpa [prefixWord, tailWord_269458, baseEnd_269458] using wordTrace_append hprefix tailTrace_269458
  have hstable : (prefixWord ++ tailWord_269458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269458).length < 2 ^ (prefixWord ++ tailWord_269458).sum := by decide
  have hdescent : baseEnd_269458 < baseStart_269458 := by decide
  rcases family_descends (prefixWord ++ tailWord_269458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269467 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 7, 4]
def baseStart_269467 : Nat := 118140960795 + 269467 * 2 ^ 59
def prefixEnd_269467 : Nat := 4983230072969 + 3 ^ 40 * 269467 * 2
def baseEnd_269467 : Nat := 92244061016801628548833

theorem tailTrace_269467 : CollatzResearch.WordTrace tailWord_269467 prefixEnd_269467 92244061016801628548833 := by
  unfold tailWord_269467
  simp only [CollatzResearch.WordTrace]
  refine ⟨9828268914774555144766655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6552179276516370096511103 9828268914774555144766655)
  ·
    refine ⟨14742403372161832717149983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9828268914774555144766655 14742403372161832717149983)
    ·
      refine ⟨22113605058242749075724975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14742403372161832717149983 22113605058242749075724975)
      ·
        refine ⟨33170407587364123613587463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22113605058242749075724975 33170407587364123613587463)
        ·
          refine ⟨49755611381046185420381195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33170407587364123613587463 49755611381046185420381195)
          ·
            refine ⟨74633417071569278130571793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49755611381046185420381195 74633417071569278130571793)
            ·
              refine ⟨55975062803676958597928845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74633417071569278130571793 55975062803676958597928845)
              ·
                refine ⟨20990648551378859474223317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55975062803676958597928845 20990648551378859474223317)
                ·
                  refine ⟨491968325422942018927109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20990648551378859474223317 491968325422942018927109)
                  ·
                    refine ⟨92244061016801628548833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 491968325422942018927109 92244061016801628548833)
                    ·
                      rfl

theorem cell22_269467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 4].length) (baseStart_269467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269467 prefixEnd_269467 := by exact prefixLift 269467
  have htrace : WordTrace (prefixWord ++ tailWord_269467) baseStart_269467 baseEnd_269467 := by
    simpa [prefixWord, tailWord_269467, baseEnd_269467] using wordTrace_append hprefix tailTrace_269467
  have hstable : (prefixWord ++ tailWord_269467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269467).length < 2 ^ (prefixWord ++ tailWord_269467).sum := by decide
  have hdescent : baseEnd_269467 < baseStart_269467 := by decide
  rcases family_descends (prefixWord ++ tailWord_269467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269527 : List Nat := [1, 1, 3, 2, 1, 2, 12]
def baseStart_269527 : Nat := 118140960795 + 269527 * 2 ^ 59
def prefixEnd_269527 : Nat := 4983230072969 + 3 ^ 40 * 269527 * 2
def baseEnd_269527 : Nat := 3417207416406721186987

theorem tailTrace_269527 : CollatzResearch.WordTrace tailWord_269527 prefixEnd_269527 3417207416406721186987 := by
  unfold tailWord_269527
  simp only [CollatzResearch.WordTrace]
  refine ⟨9830457294557185391950835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6553638196371456927967223 9830457294557185391950835)
  ·
    refine ⟨14745685941835778087926253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9830457294557185391950835 14745685941835778087926253)
    ·
      refine ⟨5529632228188416782972345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14745685941835778087926253 5529632228188416782972345)
      ·
        refine ⟨4147224171141312587229259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5529632228188416782972345 4147224171141312587229259)
        ·
          refine ⟨6220836256711968880843889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4147224171141312587229259 6220836256711968880843889)
          ·
            refine ⟨4665627192533976660632917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6220836256711968880843889 4665627192533976660632917)
            ·
              refine ⟨3417207416406721186987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 4665627192533976660632917 3417207416406721186987)
              ·
                rfl

theorem cell22_269527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 12].length) (baseStart_269527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269527 prefixEnd_269527 := by exact prefixLift 269527
  have htrace : WordTrace (prefixWord ++ tailWord_269527) baseStart_269527 baseEnd_269527 := by
    simpa [prefixWord, tailWord_269527, baseEnd_269527] using wordTrace_append hprefix tailTrace_269527
  have hstable : (prefixWord ++ tailWord_269527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269527).length < 2 ^ (prefixWord ++ tailWord_269527).sum := by decide
  have hdescent : baseEnd_269527 < baseStart_269527 := by decide
  rcases family_descends (prefixWord ++ tailWord_269527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269533 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 6]
def baseStart_269533 : Nat := 118140960795 + 269533 * 2 ^ 59
def prefixEnd_269533 : Nat := 4983230072969 + 3 ^ 40 * 269533 * 2
def baseEnd_269533 : Nat := 30755551388533152132877

theorem tailTrace_269533 : CollatzResearch.WordTrace tailWord_269533 prefixEnd_269533 30755551388533152132877 := by
  unfold tailWord_269533
  simp only [CollatzResearch.WordTrace]
  refine ⟨9830676132535448416669253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6553784088356965611112835 9830676132535448416669253)
  ·
    refine ⟨1843251774850396578125485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9830676132535448416669253 1843251774850396578125485)
    ·
      refine ⟨691219415568898716797057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1843251774850396578125485 691219415568898716797057)
      ·
        refine ⟨518414561676674037597793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 691219415568898716797057 518414561676674037597793)
        ·
          refine ⟨388810921257505528198345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 518414561676674037597793 388810921257505528198345)
          ·
            refine ⟨291608190943129146148759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388810921257505528198345 291608190943129146148759)
            ·
              refine ⟨437412286414693719223139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291608190943129146148759 437412286414693719223139)
              ·
                refine ⟨656118429622040578834709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437412286414693719223139 656118429622040578834709)
                ·
                  refine ⟨30755551388533152132877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 656118429622040578834709 30755551388533152132877)
                  ·
                    rfl

theorem cell22_269533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_269533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269533 prefixEnd_269533 := by exact prefixLift 269533
  have htrace : WordTrace (prefixWord ++ tailWord_269533) baseStart_269533 baseEnd_269533 := by
    simpa [prefixWord, tailWord_269533, baseEnd_269533] using wordTrace_append hprefix tailTrace_269533
  have hstable : (prefixWord ++ tailWord_269533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269533).length < 2 ^ (prefixWord ++ tailWord_269533).sum := by decide
  have hdescent : baseEnd_269533 < baseStart_269533 := by decide
  rcases family_descends (prefixWord ++ tailWord_269533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269544 : List Nat := [2, 1, 4, 1, 2, 1, 4, 7]
def baseStart_269544 : Nat := 118140960795 + 269544 * 2 ^ 59
def prefixEnd_269544 : Nat := 4983230072969 + 3 ^ 40 * 269544 * 2
def baseEnd_269544 : Nat := 10252268854488788263733

theorem tailTrace_269544 : CollatzResearch.WordTrace tailWord_269544 prefixEnd_269544 10252268854488788263733 := by
  unfold tailWord_269544
  simp only [CollatzResearch.WordTrace]
  refine ⟨4915538667747798647659843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6554051556997064863546457 4915538667747798647659843)
  ·
    refine ⟨7373308001621697971489765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4915538667747798647659843 7373308001621697971489765)
    ·
      refine ⟨1382495250304068369654331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7373308001621697971489765 1382495250304068369654331)
      ·
        refine ⟨2073742875456102554481497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1382495250304068369654331 2073742875456102554481497)
        ·
          refine ⟨1555307156592076915861123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2073742875456102554481497 1555307156592076915861123)
          ·
            refine ⟨2332960734888115373791685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555307156592076915861123 2332960734888115373791685)
            ·
              refine ⟨437430137791521632585941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2332960734888115373791685 437430137791521632585941)
              ·
                refine ⟨10252268854488788263733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 437430137791521632585941 10252268854488788263733)
                ·
                  rfl

theorem cell22_269544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 7].length) (baseStart_269544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269544 prefixEnd_269544 := by exact prefixLift 269544
  have htrace : WordTrace (prefixWord ++ tailWord_269544) baseStart_269544 baseEnd_269544 := by
    simpa [prefixWord, tailWord_269544, baseEnd_269544] using wordTrace_append hprefix tailTrace_269544
  have hstable : (prefixWord ++ tailWord_269544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269544).length < 2 ^ (prefixWord ++ tailWord_269544).sum := by decide
  have hdescent : baseEnd_269544 < baseStart_269544 := by decide
  rcases family_descends (prefixWord ++ tailWord_269544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269548 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 2, 3]
def baseStart_269548 : Nat := 118140960795 + 269548 * 2 ^ 59
def prefixEnd_269548 : Nat := 4983230072969 + 3 ^ 40 * 269548 * 2
def baseEnd_269548 : Nat := 92271788972144417273585

theorem tailTrace_269548 : CollatzResearch.WordTrace tailWord_269548 prefixEnd_269548 92271788972144417273585 := by
  unfold tailWord_269548
  simp only [CollatzResearch.WordTrace]
  refine ⟨4915611613740552989232649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6554148818320737318976865 4915611613740552989232649)
  ·
    refine ⟨3686708710305414741924487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4915611613740552989232649 3686708710305414741924487)
    ·
      refine ⟨5530063065458122112886731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3686708710305414741924487 5530063065458122112886731)
      ·
        refine ⟨8295094598187183169330097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5530063065458122112886731 8295094598187183169330097)
        ·
          refine ⟨6221320948640387376997573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8295094598187183169330097 6221320948640387376997573)
          ·
            refine ⟨1166497677870072633187045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6221320948640387376997573 1166497677870072633187045)
            ·
              refine ⟨218718314600638618722571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1166497677870072633187045 218718314600638618722571)
              ·
                refine ⟨328077471900957928083857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218718314600638618722571 328077471900957928083857)
                ·
                  refine ⟨246058103925718446062893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328077471900957928083857 246058103925718446062893)
                  ·
                    refine ⟨92271788972144417273585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246058103925718446062893 92271788972144417273585)
                    ·
                      rfl

theorem cell22_269548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_269548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269548 prefixEnd_269548 := by exact prefixLift 269548
  have htrace : WordTrace (prefixWord ++ tailWord_269548) baseStart_269548 baseEnd_269548 := by
    simpa [prefixWord, tailWord_269548, baseEnd_269548] using wordTrace_append hprefix tailTrace_269548
  have hstable : (prefixWord ++ tailWord_269548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269548).length < 2 ^ (prefixWord ++ tailWord_269548).sum := by decide
  have hdescent : baseEnd_269548 < baseStart_269548 := by decide
  rcases family_descends (prefixWord ++ tailWord_269548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269651 : List Nat := [1, 1, 1, 2, 1, 1, 5, 6, 4]
def baseStart_269651 : Nat := 118140960795 + 269651 * 2 ^ 59
def prefixEnd_269651 : Nat := 4983230072969 + 3 ^ 40 * 269651 * 2
def baseEnd_269651 : Nat := 30769015992362160649423

theorem tailTrace_269651 : CollatzResearch.WordTrace tailWord_269651 prefixEnd_269651 30769015992362160649423 := by
  unfold tailWord_269651
  simp only [CollatzResearch.WordTrace]
  refine ⟨9834979946107954569464807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6556653297405303046309871 9834979946107954569464807)
  ·
    refine ⟨14752469919161931854197211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9834979946107954569464807 14752469919161931854197211)
    ·
      refine ⟨22128704878742897781295817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14752469919161931854197211 22128704878742897781295817)
      ·
        refine ⟨16596528659057173335971863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22128704878742897781295817 16596528659057173335971863)
        ·
          refine ⟨24894792988585760003957795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16596528659057173335971863 24894792988585760003957795)
          ·
            refine ⟨37342189482878640005936693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24894792988585760003957795 37342189482878640005936693)
            ·
              refine ⟨3500830264019872500556565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37342189482878640005936693 3500830264019872500556565)
              ·
                refine ⟨164101418625931523463589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3500830264019872500556565 164101418625931523463589)
                ·
                  refine ⟨30769015992362160649423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164101418625931523463589 30769015992362160649423)
                  ·
                    rfl

theorem cell22_269651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 4].length) (baseStart_269651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269651 prefixEnd_269651 := by exact prefixLift 269651
  have htrace : WordTrace (prefixWord ++ tailWord_269651) baseStart_269651 baseEnd_269651 := by
    simpa [prefixWord, tailWord_269651, baseEnd_269651] using wordTrace_append hprefix tailTrace_269651
  have hstable : (prefixWord ++ tailWord_269651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269651).length < 2 ^ (prefixWord ++ tailWord_269651).sum := by decide
  have hdescent : baseEnd_269651 < baseStart_269651 := by decide
  rcases family_descends (prefixWord ++ tailWord_269651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269679 : List Nat := [1, 1, 2, 1, 3, 1, 5, 8]
def baseStart_269679 : Nat := 118140960795 + 269679 * 2 ^ 59
def prefixEnd_269679 : Nat := 4983230072969 + 3 ^ 40 * 269679 * 2
def baseEnd_269679 : Nat := 10257403661033749138687

theorem tailTrace_269679 : CollatzResearch.WordTrace tailWord_269679 prefixEnd_269679 10257403661033749138687 := by
  unfold tailWord_269679
  simp only [CollatzResearch.WordTrace]
  refine ⟨9836001190006515351484091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6557334126671010234322727 9836001190006515351484091)
  ·
    refine ⟨14754001785009773027226137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9836001190006515351484091 14754001785009773027226137)
    ·
      refine ⟨11065501338757329770419603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14754001785009773027226137 11065501338757329770419603)
      ·
        refine ⟨16598252008135994655629405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11065501338757329770419603 16598252008135994655629405)
        ·
          refine ⟨6224344503050997995861027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16598252008135994655629405 6224344503050997995861027)
          ·
            refine ⟨9336516754576496993791541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6224344503050997995861027 9336516754576496993791541)
            ·
              refine ⟨875298445741546593167957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9336516754576496993791541 875298445741546593167957)
              ·
                refine ⟨10257403661033749138687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 875298445741546593167957 10257403661033749138687)
                ·
                  rfl

theorem cell22_269679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 8].length) (baseStart_269679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269679 prefixEnd_269679 := by exact prefixLift 269679
  have htrace : WordTrace (prefixWord ++ tailWord_269679) baseStart_269679 baseEnd_269679 := by
    simpa [prefixWord, tailWord_269679, baseEnd_269679] using wordTrace_append hprefix tailTrace_269679
  have hstable : (prefixWord ++ tailWord_269679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269679).length < 2 ^ (prefixWord ++ tailWord_269679).sum := by decide
  have hdescent : baseEnd_269679 < baseStart_269679 := by decide
  rcases family_descends (prefixWord ++ tailWord_269679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269745 : List Nat := [1, 2, 2, 4, 1, 1, 2, 5, 1, 3]
def baseStart_269745 : Nat := 118140960795 + 269745 * 2 ^ 59
def prefixEnd_269745 : Nat := 4983230072969 + 3 ^ 40 * 269745 * 2
def baseEnd_269745 : Nat := 92339226098101570097981

theorem tailTrace_269745 : CollatzResearch.WordTrace tailWord_269745 prefixEnd_269745 92339226098101570097981 := by
  unfold tailWord_269745
  simp only [CollatzResearch.WordTrace]
  refine ⟨9838408407767408623386689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6558938938511605748924459 9838408407767408623386689)
  ·
    refine ⟨7378806305825556467540017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9838408407767408623386689 7378806305825556467540017)
    ·
      refine ⟨5534104729369167350655013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7378806305825556467540017 5534104729369167350655013)
      ·
        refine ⟨1037644636756718878247815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5534104729369167350655013 1037644636756718878247815)
        ·
          refine ⟨1556466955135078317371723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037644636756718878247815 1556466955135078317371723)
          ·
            refine ⟨2334700432702617476057585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556466955135078317371723 2334700432702617476057585)
            ·
              refine ⟨1751025324526963107043189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2334700432702617476057585 1751025324526963107043189)
              ·
                refine ⟨164158624174402791285299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1751025324526963107043189 164158624174402791285299)
                ·
                  refine ⟨246237936261604186927949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164158624174402791285299 246237936261604186927949)
                  ·
                    refine ⟨92339226098101570097981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246237936261604186927949 92339226098101570097981)
                    ·
                      rfl

theorem cell22_269745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_269745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269745 prefixEnd_269745 := by exact prefixLift 269745
  have htrace : WordTrace (prefixWord ++ tailWord_269745) baseStart_269745 baseEnd_269745 := by
    simpa [prefixWord, tailWord_269745, baseEnd_269745] using wordTrace_append hprefix tailTrace_269745
  have hstable : (prefixWord ++ tailWord_269745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269745).length < 2 ^ (prefixWord ++ tailWord_269745).sum := by decide
  have hdescent : baseEnd_269745 < baseStart_269745 := by decide
  rcases family_descends (prefixWord ++ tailWord_269745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269771 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 3, 4]
def baseStart_269771 : Nat := 118140960795 + 269771 * 2 ^ 59
def prefixEnd_269771 : Nat := 4983230072969 + 3 ^ 40 * 269771 * 2
def baseEnd_269771 : Nat := 92348126429446168947901

theorem tailTrace_269771 : CollatzResearch.WordTrace tailWord_269771 prefixEnd_269771 92348126429446168947901 := by
  unfold tailWord_269771
  simp only [CollatzResearch.WordTrace]
  refine ⟨9839356705673215063833167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6559571137115476709222111 9839356705673215063833167)
  ·
    refine ⟨14759035058509822595749751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9839356705673215063833167 14759035058509822595749751)
    ·
      refine ⟨22138552587764733893624627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14759035058509822595749751 22138552587764733893624627)
      ·
        refine ⟨33207828881647100840436941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22138552587764733893624627 33207828881647100840436941)
        ·
          refine ⟨12452935830617662815163853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33207828881647100840436941 12452935830617662815163853)
          ·
            refine ⟨4669850936481623555686445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12452935830617662815163853 4669850936481623555686445)
            ·
              refine ⟨1751194101180608833382417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4669850936481623555686445 1751194101180608833382417)
              ·
                refine ⟨1313395575885456625036813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1751194101180608833382417 1313395575885456625036813)
                ·
                  refine ⟨492523340957046234388805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1313395575885456625036813 492523340957046234388805)
                  ·
                    refine ⟨92348126429446168947901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 492523340957046234388805 92348126429446168947901)
                    ·
                      rfl

theorem cell22_269771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 4].length) (baseStart_269771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269771 prefixEnd_269771 := by exact prefixLift 269771
  have htrace : WordTrace (prefixWord ++ tailWord_269771) baseStart_269771 baseEnd_269771 := by
    simpa [prefixWord, tailWord_269771, baseEnd_269771] using wordTrace_append hprefix tailTrace_269771
  have hstable : (prefixWord ++ tailWord_269771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269771).length < 2 ^ (prefixWord ++ tailWord_269771).sum := by decide
  have hdescent : baseEnd_269771 < baseStart_269771 := by decide
  rcases family_descends (prefixWord ++ tailWord_269771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269786 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_269786 : Nat := 118140960795 + 269786 * 2 ^ 59
def prefixEnd_269786 : Nat := 4983230072969 + 3 ^ 40 * 269786 * 2
def baseEnd_269786 : Nat := 30784420411997043274285

theorem tailTrace_269786 : CollatzResearch.WordTrace tailWord_269786 prefixEnd_269786 30784420411997043274285 := by
  unfold tailWord_269786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2459975950154718156407303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6559935867079248417086141 2459975950154718156407303)
  ·
    refine ⟨3689963925232077234610955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2459975950154718156407303 3689963925232077234610955)
    ·
      refine ⟨5534945887848115851916433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3689963925232077234610955 5534945887848115851916433)
      ·
        refine ⟨4151209415886086888937325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5534945887848115851916433 4151209415886086888937325)
        ·
          refine ⟨1556703530957282583351497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4151209415886086888937325 1556703530957282583351497)
          ·
            refine ⟨1167527648217961937513623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1556703530957282583351497 1167527648217961937513623)
            ·
              refine ⟨1751291472326942906270435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167527648217961937513623 1751291472326942906270435)
              ·
                refine ⟨2626937208490414359405653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751291472326942906270435 2626937208490414359405653)
                ·
                  refine ⟨30784420411997043274285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2626937208490414359405653 30784420411997043274285)
                  ·
                    rfl

theorem cell22_269786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_269786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269786 prefixEnd_269786 := by exact prefixLift 269786
  have htrace : WordTrace (prefixWord ++ tailWord_269786) baseStart_269786 baseEnd_269786 := by
    simpa [prefixWord, tailWord_269786, baseEnd_269786] using wordTrace_append hprefix tailTrace_269786
  have hstable : (prefixWord ++ tailWord_269786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269786).length < 2 ^ (prefixWord ++ tailWord_269786).sum := by decide
  have hdescent : baseEnd_269786 < baseStart_269786 := by decide
  rcases family_descends (prefixWord ++ tailWord_269786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269818 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 4, 3]
def baseStart_269818 : Nat := 118140960795 + 269818 * 2 ^ 59
def prefixEnd_269818 : Nat := 4983230072969 + 3 ^ 40 * 269818 * 2
def baseEnd_269818 : Nat := 92364215489953713022757

theorem tailTrace_269818 : CollatzResearch.WordTrace tailWord_269818 prefixEnd_269818 92364215489953713022757 := by
  unfold tailWord_269818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460267734125735522698527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6560713957668628060529405 2460267734125735522698527)
  ·
    refine ⟨3690401601188603284047791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2460267734125735522698527 3690401601188603284047791)
    ·
      refine ⟨5535602401782904926071687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3690401601188603284047791 5535602401782904926071687)
      ·
        refine ⟨8303403602674357389107531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5535602401782904926071687 8303403602674357389107531)
        ·
          refine ⟨12455105404011536083661297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8303403602674357389107531 12455105404011536083661297)
          ·
            refine ⟨9341329053008652062745973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12455105404011536083661297 9341329053008652062745973)
            ·
              refine ⟨875749598719561130882435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9341329053008652062745973 875749598719561130882435)
              ·
                refine ⟨1313624398079341696323653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875749598719561130882435 1313624398079341696323653)
                ·
                  refine ⟨246304574639876568060685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313624398079341696323653 246304574639876568060685)
                  ·
                    refine ⟨92364215489953713022757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246304574639876568060685 92364215489953713022757)
                    ·
                      rfl

theorem cell22_269818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_269818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269818 prefixEnd_269818 := by exact prefixLift 269818
  have htrace : WordTrace (prefixWord ++ tailWord_269818) baseStart_269818 baseEnd_269818 := by
    simpa [prefixWord, tailWord_269818, baseEnd_269818] using wordTrace_append hprefix tailTrace_269818
  have hstable : (prefixWord ++ tailWord_269818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269818).length < 2 ^ (prefixWord ++ tailWord_269818).sum := by decide
  have hdescent : baseEnd_269818 < baseStart_269818 := by decide
  rcases family_descends (prefixWord ++ tailWord_269818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269835 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 1, 5]
def baseStart_269835 : Nat := 118140960795 + 269835 * 2 ^ 59
def prefixEnd_269835 : Nat := 4983230072969 + 3 ^ 40 * 269835 * 2
def baseEnd_269835 : Nat := 92370034937371335347705

theorem tailTrace_269835 : CollatzResearch.WordTrace tailWord_269835 prefixEnd_269835 92370034937371335347705 := by
  unfold tailWord_269835
  simp only [CollatzResearch.WordTrace]
  refine ⟨9841690977441353994162959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6561127318294235996108639 9841690977441353994162959)
  ·
    refine ⟨14762536466162030991244439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9841690977441353994162959 14762536466162030991244439)
    ·
      refine ⟨22143804699243046486866659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14762536466162030991244439 22143804699243046486866659)
      ·
        refine ⟨33215707048864569730299989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22143804699243046486866659 33215707048864569730299989)
        ·
          refine ⟨389246566978881676526953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 33215707048864569730299989 389246566978881676526953)
          ·
            refine ⟨291934925234161257395215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389246566978881676526953 291934925234161257395215)
            ·
              refine ⟨437902387851241886092823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291934925234161257395215 437902387851241886092823)
              ·
                refine ⟨656853581776862829139235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437902387851241886092823 656853581776862829139235)
                ·
                  refine ⟨985280372665294243708853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656853581776862829139235 985280372665294243708853)
                  ·
                    refine ⟨92370034937371335347705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 985280372665294243708853 92370034937371335347705)
                    ·
                      rfl

theorem cell22_269835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 5].length) (baseStart_269835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269835 prefixEnd_269835 := by exact prefixLift 269835
  have htrace : WordTrace (prefixWord ++ tailWord_269835) baseStart_269835 baseEnd_269835 := by
    simpa [prefixWord, tailWord_269835, baseEnd_269835] using wordTrace_append hprefix tailTrace_269835
  have hstable : (prefixWord ++ tailWord_269835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269835).length < 2 ^ (prefixWord ++ tailWord_269835).sum := by decide
  have hdescent : baseEnd_269835 < baseStart_269835 := by decide
  rcases family_descends (prefixWord ++ tailWord_269835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269848 : List Nat := [2, 1, 2, 3, 4, 1, 1, 8]
def baseStart_269848 : Nat := 118140960795 + 269848 * 2 ^ 59
def prefixEnd_269848 : Nat := 4983230072969 + 3 ^ 40 * 269848 * 2
def baseEnd_269848 : Nat := 10263831678115959419185

theorem tailTrace_269848 : CollatzResearch.WordTrace tailWord_269848 prefixEnd_269848 10263831678115959419185 := by
  unfold tailWord_269848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921082563197128607193099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6561443417596171476257465 4921082563197128607193099)
  ·
    refine ⟨7381623844795692910789649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4921082563197128607193099 7381623844795692910789649)
    ·
      refine ⟨5536217883596769683092237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7381623844795692910789649 5536217883596769683092237)
      ·
        refine ⟨2076081706348788631159589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5536217883596769683092237 2076081706348788631159589)
        ·
          refine ⟨389265319940397868342423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2076081706348788631159589 389265319940397868342423)
          ·
            refine ⟨583897979910596802513635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389265319940397868342423 583897979910596802513635)
            ·
              refine ⟨875846969865895203770453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583897979910596802513635 875846969865895203770453)
              ·
                refine ⟨10263831678115959419185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 875846969865895203770453 10263831678115959419185)
                ·
                  rfl

theorem cell22_269848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 8].length) (baseStart_269848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269848 prefixEnd_269848 := by exact prefixLift 269848
  have htrace : WordTrace (prefixWord ++ tailWord_269848) baseStart_269848 baseEnd_269848 := by
    simpa [prefixWord, tailWord_269848, baseEnd_269848] using wordTrace_append hprefix tailTrace_269848
  have hstable : (prefixWord ++ tailWord_269848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269848).length < 2 ^ (prefixWord ++ tailWord_269848).sum := by decide
  have hdescent : baseEnd_269848 < baseStart_269848 := by decide
  rcases family_descends (prefixWord ++ tailWord_269848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269861 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_269861 : Nat := 118140960795 + 269861 * 2 ^ 59
def prefixEnd_269861 : Nat := 4983230072969 + 3 ^ 40 * 269861 * 2
def baseEnd_269861 : Nat := 92378935268715934197625

theorem tailTrace_269861 : CollatzResearch.WordTrace tailWord_269861 prefixEnd_269861 92378935268715934197625 := by
  unfold tailWord_269861
  simp only [CollatzResearch.WordTrace]
  refine ⟨9842639275347160434609437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6561759516898106956406291 9842639275347160434609437)
  ·
    refine ⟨3690989728255185162978539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9842639275347160434609437 3690989728255185162978539)
    ·
      refine ⟨5536484592382777744467809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3690989728255185162978539 5536484592382777744467809)
      ·
        refine ⟨4152363444287083308350857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5536484592382777744467809 4152363444287083308350857)
        ·
          refine ⟨3114272583215312481263143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4152363444287083308350857 3114272583215312481263143)
          ·
            refine ⟨4671408874822968721894715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114272583215312481263143 4671408874822968721894715)
            ·
              refine ⟨7007113312234453082842073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4671408874822968721894715 7007113312234453082842073)
              ·
                refine ⟨5255334984175839812131555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7007113312234453082842073 5255334984175839812131555)
                ·
                  refine ⟨7883002476263759718197333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255334984175839812131555 7883002476263759718197333)
                  ·
                    refine ⟨92378935268715934197625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7883002476263759718197333 92378935268715934197625)
                    ·
                      rfl

theorem cell22_269861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_269861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269861 prefixEnd_269861 := by exact prefixLift 269861
  have htrace : WordTrace (prefixWord ++ tailWord_269861) baseStart_269861 baseEnd_269861 := by
    simpa [prefixWord, tailWord_269861, baseEnd_269861] using wordTrace_append hprefix tailTrace_269861
  have hstable : (prefixWord ++ tailWord_269861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269861).length < 2 ^ (prefixWord ++ tailWord_269861).sum := by decide
  have hdescent : baseEnd_269861 < baseStart_269861 := by decide
  rcases family_descends (prefixWord ++ tailWord_269861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269880 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 3, 3]
def baseStart_269880 : Nat := 118140960795 + 269880 * 2 ^ 59
def prefixEnd_269880 : Nat := 4983230072969 + 3 ^ 40 * 269880 * 2
def baseEnd_269880 : Nat := 92385439357006217972567

theorem tailTrace_269880 : CollatzResearch.WordTrace tailWord_269880 prefixEnd_269880 92385439357006217972567 := by
  unfold tailWord_269880
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921666131139163339775547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6562221508185551119700729 4921666131139163339775547)
  ·
    refine ⟨7382499196708745009663321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4921666131139163339775547 7382499196708745009663321)
    ·
      refine ⟨5536874397531558757247491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7382499196708745009663321 5536874397531558757247491)
      ·
        refine ⟨8305311596297338135871237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5536874397531558757247491 8305311596297338135871237)
        ·
          refine ⟨1557245924305750900475857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8305311596297338135871237 1557245924305750900475857)
          ·
            refine ⟨1167934443229313175356893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1557245924305750900475857 1167934443229313175356893)
            ·
              refine ⟨437975416210992440758835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167934443229313175356893 437975416210992440758835)
              ·
                refine ⟨656963124316488661138253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437975416210992440758835 656963124316488661138253)
                ·
                  refine ⟨246361171618683247926845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656963124316488661138253 246361171618683247926845)
                  ·
                    refine ⟨92385439357006217972567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246361171618683247926845 92385439357006217972567)
                    ·
                      rfl

theorem cell22_269880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_269880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269880 prefixEnd_269880 := by exact prefixLift 269880
  have htrace : WordTrace (prefixWord ++ tailWord_269880) baseStart_269880 baseEnd_269880 := by
    simpa [prefixWord, tailWord_269880, baseEnd_269880] using wordTrace_append hprefix tailTrace_269880
  have hstable : (prefixWord ++ tailWord_269880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269880).length < 2 ^ (prefixWord ++ tailWord_269880).sum := by decide
  have hdescent : baseEnd_269880 < baseStart_269880 := by decide
  rcases family_descends (prefixWord ++ tailWord_269880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269893 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 5]
def baseStart_269893 : Nat := 118140960795 + 269893 * 2 ^ 59
def prefixEnd_269893 : Nat := 4983230072969 + 3 ^ 40 * 269893 * 2
def baseEnd_269893 : Nat := 30796629840892839132509

theorem tailTrace_269893 : CollatzResearch.WordTrace tailWord_269893 prefixEnd_269893 30796629840892839132509 := by
  unfold tailWord_269893
  simp only [CollatzResearch.WordTrace]
  refine ⟨9843806411231229899774333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6562537607487486599849555 9843806411231229899774333)
  ·
    refine ⟨3691427404211711212415375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9843806411231229899774333 3691427404211711212415375)
    ·
      refine ⟨5537141106317566818623063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3691427404211711212415375 5537141106317566818623063)
      ·
        refine ⟨8305711659476350227934595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5537141106317566818623063 8305711659476350227934595)
        ·
          refine ⟨12458567489214525341901893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8305711659476350227934595 12458567489214525341901893)
          ·
            refine ⟨2335981404227723501606605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12458567489214525341901893 2335981404227723501606605)
            ·
              refine ⟨875993026585396313102477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2335981404227723501606605 875993026585396313102477)
              ·
                refine ⟨328497384969523617413429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 875993026585396313102477 328497384969523617413429)
                ·
                  refine ⟨30796629840892839132509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 328497384969523617413429 30796629840892839132509)
                  ·
                    rfl

theorem cell22_269893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_269893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_269893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_269893 prefixEnd_269893 := by exact prefixLift 269893
  have htrace : WordTrace (prefixWord ++ tailWord_269893) baseStart_269893 baseEnd_269893 := by
    simpa [prefixWord, tailWord_269893, baseEnd_269893] using wordTrace_append hprefix tailTrace_269893
  have hstable : (prefixWord ++ tailWord_269893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269893).length < 2 ^ (prefixWord ++ tailWord_269893).sum := by decide
  have hdescent : baseEnd_269893 < baseStart_269893 := by decide
  rcases family_descends (prefixWord ++ tailWord_269893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270015 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 3, 3]
def baseStart_270015 : Nat := 118140960795 + 270015 * 2 ^ 59
def prefixEnd_270015 : Nat := 4983230072969 + 3 ^ 40 * 270015 * 2
def baseEnd_270015 : Nat := 92431652615910865847153

theorem tailTrace_270015 : CollatzResearch.WordTrace tailWord_270015 prefixEnd_270015 92431652615910865847153 := by
  unfold tailWord_270015
  simp only [CollatzResearch.WordTrace]
  refine ⟨9848256116789244735715499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6565504077859496490476999 9848256116789244735715499)
  ·
    refine ⟨14772384175183867103573249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9848256116789244735715499 14772384175183867103573249)
    ·
      refine ⟨11079288131387900327679937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14772384175183867103573249 11079288131387900327679937)
      ·
        refine ⟨8309466098540925245759953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11079288131387900327679937 8309466098540925245759953)
        ·
          refine ⟨6232099573905693934319965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8309466098540925245759953 6232099573905693934319965)
          ·
            refine ⟨2337037340214635225369987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6232099573905693934319965 2337037340214635225369987)
            ·
              refine ⟨3505556010321952838054981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337037340214635225369987 3505556010321952838054981)
              ·
                refine ⟨657291751935366157135309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3505556010321952838054981 657291751935366157135309)
                ·
                  refine ⟨246484406975762308925741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657291751935366157135309 246484406975762308925741)
                  ·
                    refine ⟨92431652615910865847153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246484406975762308925741 92431652615910865847153)
                    ·
                      rfl

theorem cell22_270015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 3].length) (baseStart_270015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270015 prefixEnd_270015 := by exact prefixLift 270015
  have htrace : WordTrace (prefixWord ++ tailWord_270015) baseStart_270015 baseEnd_270015 := by
    simpa [prefixWord, tailWord_270015, baseEnd_270015] using wordTrace_append hprefix tailTrace_270015
  have hstable : (prefixWord ++ tailWord_270015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270015).length < 2 ^ (prefixWord ++ tailWord_270015).sum := by decide
  have hdescent : baseEnd_270015 < baseStart_270015 := by decide
  rcases family_descends (prefixWord ++ tailWord_270015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270032 : List Nat := [2, 1, 1, 1, 1, 2, 1, 9, 1, 3]
def baseStart_270032 : Nat := 118140960795 + 270032 * 2 ^ 59
def prefixEnd_270032 : Nat := 4983230072969 + 3 ^ 40 * 270032 * 2
def baseEnd_270032 : Nat := 92437472063328488172101

theorem tailTrace_270032 : CollatzResearch.WordTrace tailWord_270032 prefixEnd_270032 92437472063328488172101 := by
  unfold tailWord_270032
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924438078863828319542175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6565917438485104426056233 4924438078863828319542175)
  ·
    refine ⟨7386657118295742479313263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4924438078863828319542175 7386657118295742479313263)
    ·
      refine ⟨11079985677443613718969895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7386657118295742479313263 11079985677443613718969895)
      ·
        refine ⟨16619978516165420578454843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11079985677443613718969895 16619978516165420578454843)
        ·
          refine ⟨24929967774248130867682265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16619978516165420578454843 24929967774248130867682265)
          ·
            refine ⟨18697475830686098150761699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24929967774248130867682265 18697475830686098150761699)
            ·
              refine ⟨28046213746029147226142549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18697475830686098150761699 28046213746029147226142549)
              ·
                refine ⟨164333283668139534528179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 28046213746029147226142549 164333283668139534528179)
                ·
                  refine ⟨246499925502209301792269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164333283668139534528179 246499925502209301792269)
                  ·
                    refine ⟨92437472063328488172101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246499925502209301792269 92437472063328488172101)
                    ·
                      rfl

theorem cell22_270032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 1, 3].length) (baseStart_270032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270032 prefixEnd_270032 := by exact prefixLift 270032
  have htrace : WordTrace (prefixWord ++ tailWord_270032) baseStart_270032 baseEnd_270032 := by
    simpa [prefixWord, tailWord_270032, baseEnd_270032] using wordTrace_append hprefix tailTrace_270032
  have hstable : (prefixWord ++ tailWord_270032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270032).length < 2 ^ (prefixWord ++ tailWord_270032).sum := by decide
  have hdescent : baseEnd_270032 < baseStart_270032 := by decide
  rcases family_descends (prefixWord ++ tailWord_270032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270049 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 3, 3]
def baseStart_270049 : Nat := 118140960795 + 270049 * 2 ^ 59
def prefixEnd_270049 : Nat := 4983230072969 + 3 ^ 40 * 270049 * 2
def baseEnd_270049 : Nat := 92443291510746110497049

theorem tailTrace_270049 : CollatzResearch.WordTrace tailWord_270049 prefixEnd_270049 92443291510746110497049 := by
  unfold tailWord_270049
  simp only [CollatzResearch.WordTrace]
  refine ⟨9849496198666068542453201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6566330799110712361635467 9849496198666068542453201)
  ·
    refine ⟨7387122148999551406839901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9849496198666068542453201 7387122148999551406839901)
    ·
      refine ⟨2770170805874831777564963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7387122148999551406839901 2770170805874831777564963)
      ·
        refine ⟨4155256208812247666347445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2770170805874831777564963 4155256208812247666347445)
        ·
          refine ⟨389555269576148218720073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4155256208812247666347445 389555269576148218720073)
          ·
            refine ⟨292166452182111164040055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389555269576148218720073 292166452182111164040055)
            ·
              refine ⟨438249678273166746060083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292166452182111164040055 438249678273166746060083)
              ·
                refine ⟨657374517409750119090125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438249678273166746060083 657374517409750119090125)
                ·
                  refine ⟨246515444028656294658797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657374517409750119090125 246515444028656294658797)
                  ·
                    refine ⟨92443291510746110497049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246515444028656294658797 92443291510746110497049)
                    ·
                      rfl

theorem cell22_270049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_270049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270049 prefixEnd_270049 := by exact prefixLift 270049
  have htrace : WordTrace (prefixWord ++ tailWord_270049) baseStart_270049 baseEnd_270049 := by
    simpa [prefixWord, tailWord_270049, baseEnd_270049] using wordTrace_append hprefix tailTrace_270049
  have hstable : (prefixWord ++ tailWord_270049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270049).length < 2 ^ (prefixWord ++ tailWord_270049).sum := by decide
  have hdescent : baseEnd_270049 < baseStart_270049 := by decide
  rcases family_descends (prefixWord ++ tailWord_270049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270075 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 1, 4]
def baseStart_270075 : Nat := 118140960795 + 270075 * 2 ^ 59
def prefixEnd_270075 : Nat := 4983230072969 + 3 ^ 40 * 270075 * 2
def baseEnd_270075 : Nat := 92452191842090709346969

theorem tailTrace_270075 : CollatzResearch.WordTrace tailWord_270075 prefixEnd_270075 92452191842090709346969 := by
  unfold tailWord_270075
  simp only [CollatzResearch.WordTrace]
  refine ⟨9850444496571874982899679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6566962997714583321933119 9850444496571874982899679)
  ·
    refine ⟨14775666744857812474349519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9850444496571874982899679 14775666744857812474349519)
    ·
      refine ⟨22163500117286718711524279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14775666744857812474349519 22163500117286718711524279)
      ·
        refine ⟨33245250175930078067286419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22163500117286718711524279 33245250175930078067286419)
        ·
          refine ⟨49867875263895117100929629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33245250175930078067286419 49867875263895117100929629)
          ·
            refine ⟨18700453223960668912848611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49867875263895117100929629 18700453223960668912848611)
            ·
              refine ⟨28050679835941003369272917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18700453223960668912848611 28050679835941003369272917)
              ·
                refine ⟨328718904327433633233667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28050679835941003369272917 328718904327433633233667)
                ·
                  refine ⟨493078356491150449850501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328718904327433633233667 493078356491150449850501)
                  ·
                    refine ⟨92452191842090709346969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 493078356491150449850501 92452191842090709346969)
                    ·
                      rfl

theorem cell22_270075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 4].length) (baseStart_270075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270075 prefixEnd_270075 := by exact prefixLift 270075
  have htrace : WordTrace (prefixWord ++ tailWord_270075) baseStart_270075 baseEnd_270075 := by
    simpa [prefixWord, tailWord_270075, baseEnd_270075] using wordTrace_append hprefix tailTrace_270075
  have hstable : (prefixWord ++ tailWord_270075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270075).length < 2 ^ (prefixWord ++ tailWord_270075).sum := by decide
  have hdescent : baseEnd_270075 < baseStart_270075 := by decide
  rcases family_descends (prefixWord ++ tailWord_270075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270100 : List Nat := [2, 4, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_270100 : Nat := 118140960795 + 270100 * 2 ^ 59
def prefixEnd_270100 : Nat := 4983230072969 + 3 ^ 40 * 270100 * 2
def baseEnd_270100 : Nat := 92460749852998977471893

theorem tailTrace_270100 : CollatzResearch.WordTrace tailWord_270100 prefixEnd_270100 92460749852998977471893 := by
  unfold tailWord_270100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4925678160740652126279877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6567570880987536168373169 4925678160740652126279877)
  ·
    refine ⟨923564655138872273677477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4925678160740652126279877 923564655138872273677477)
    ·
      refine ⟨173168372838538551314527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 923564655138872273677477 173168372838538551314527)
      ·
        refine ⟨259752559257807826971791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173168372838538551314527 259752559257807826971791)
        ·
          refine ⟨389628838886711740457687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259752559257807826971791 389628838886711740457687)
          ·
            refine ⟨584443258330067610686531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389628838886711740457687 584443258330067610686531)
            ·
              refine ⟨876664887495101416029797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584443258330067610686531 876664887495101416029797)
              ·
                refine ⟨164374666405331515505587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 876664887495101416029797 164374666405331515505587)
                ·
                  refine ⟨246561999607997273258381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164374666405331515505587 246561999607997273258381)
                  ·
                    refine ⟨92460749852998977471893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246561999607997273258381 92460749852998977471893)
                    ·
                      rfl

theorem cell22_270100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_270100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270100 prefixEnd_270100 := by exact prefixLift 270100
  have htrace : WordTrace (prefixWord ++ tailWord_270100) baseStart_270100 baseEnd_270100 := by
    simpa [prefixWord, tailWord_270100, baseEnd_270100] using wordTrace_append hprefix tailTrace_270100
  have hstable : (prefixWord ++ tailWord_270100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270100).length < 2 ^ (prefixWord ++ tailWord_270100).sum := by decide
  have hdescent : baseEnd_270100 < baseStart_270100 := by decide
  rcases family_descends (prefixWord ++ tailWord_270100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270105 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 8, 3]
def baseStart_270105 : Nat := 118140960795 + 270105 * 2 ^ 59
def prefixEnd_270105 : Nat := 4983230072969 + 3 ^ 40 * 270105 * 2
def baseEnd_270105 : Nat := 92462461455180631096877

theorem tailTrace_270105 : CollatzResearch.WordTrace tailWord_270105 prefixEnd_270105 92462461455180631096877 := by
  unfold tailWord_270105
  simp only [CollatzResearch.WordTrace]
  refine ⟨9851538686463190106491769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6567692457642126737661179 9851538686463190106491769)
  ·
    refine ⟨7388654014847392579868827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9851538686463190106491769 7388654014847392579868827)
    ·
      refine ⟨11082981022271088869803241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7388654014847392579868827 11082981022271088869803241)
      ·
        refine ⟨8312235766703316652352431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11082981022271088869803241 8312235766703316652352431)
        ·
          refine ⟨12468353650054974978528647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8312235766703316652352431 12468353650054974978528647)
          ·
            refine ⟨18702530475082462467792971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12468353650054974978528647 18702530475082462467792971)
            ·
              refine ⟨28053795712623693701689457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18702530475082462467792971 28053795712623693701689457)
              ·
                refine ⟨21040346784467770276267093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28053795712623693701689457 21040346784467770276267093)
                ·
                  refine ⟨246566563880481682925005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21040346784467770276267093 246566563880481682925005)
                  ·
                    refine ⟨92462461455180631096877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246566563880481682925005 92462461455180631096877)
                    ·
                      rfl

theorem cell22_270105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 3].length) (baseStart_270105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270105 prefixEnd_270105 := by exact prefixLift 270105
  have htrace : WordTrace (prefixWord ++ tailWord_270105) baseStart_270105 baseEnd_270105 := by
    simpa [prefixWord, tailWord_270105, baseEnd_270105] using wordTrace_append hprefix tailTrace_270105
  have hstable : (prefixWord ++ tailWord_270105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270105).length < 2 ^ (prefixWord ++ tailWord_270105).sum := by decide
  have hdescent : baseEnd_270105 < baseStart_270105 := by decide
  rcases family_descends (prefixWord ++ tailWord_270105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270156 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 2, 3]
def baseStart_270156 : Nat := 118140960795 + 270156 * 2 ^ 59
def prefixEnd_270156 : Nat := 4983230072969 + 3 ^ 40 * 270156 * 2
def baseEnd_270156 : Nat := 92479919797433498071721

theorem tailTrace_270156 : CollatzResearch.WordTrace tailWord_270156 prefixEnd_270156 92479919797433498071721 := by
  unfold tailWord_270156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4926699404639212908299161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6568932539518950544398881 4926699404639212908299161)
  ·
    refine ⟨3695024553479409681224371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4926699404639212908299161 3695024553479409681224371)
    ·
      refine ⟨5542536830219114521836557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3695024553479409681224371 5542536830219114521836557)
      ·
        refine ⟨2078451311332167945688709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5542536830219114521836557 2078451311332167945688709)
        ·
          refine ⟨389709620874781489816633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2078451311332167945688709 389709620874781489816633)
          ·
            refine ⟨292282215656086117362475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389709620874781489816633 292282215656086117362475)
            ·
              refine ⟨438423323484129176043713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292282215656086117362475 438423323484129176043713)
              ·
                refine ⟨328817492613096882032785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438423323484129176043713 328817492613096882032785)
                ·
                  refine ⟨246613119459822661524589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328817492613096882032785 246613119459822661524589)
                  ·
                    refine ⟨92479919797433498071721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246613119459822661524589 92479919797433498071721)
                    ·
                      rfl

theorem cell22_270156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_270156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270156 prefixEnd_270156 := by exact prefixLift 270156
  have htrace : WordTrace (prefixWord ++ tailWord_270156) baseStart_270156 baseEnd_270156 := by
    simpa [prefixWord, tailWord_270156, baseEnd_270156] using wordTrace_append hprefix tailTrace_270156
  have hstable : (prefixWord ++ tailWord_270156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270156).length < 2 ^ (prefixWord ++ tailWord_270156).sum := by decide
  have hdescent : baseEnd_270156 < baseStart_270156 := by decide
  rcases family_descends (prefixWord ++ tailWord_270156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270186 : List Nat := [3, 1, 3, 4, 1, 2, 2, 6]
def baseStart_270186 : Nat := 118140960795 + 270186 * 2 ^ 59
def prefixEnd_270186 : Nat := 4983230072969 + 3 ^ 40 * 270186 * 2
def baseEnd_270186 : Nat := 10276687712280379980181

theorem tailTrace_270186 : CollatzResearch.WordTrace tailWord_270186 prefixEnd_270186 10276687712280379980181 := by
  unfold tailWord_270186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2463623249792435235047603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6569661999446493960126941 2463623249792435235047603)
  ·
    refine ⟨3695434874688652852571405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2463623249792435235047603 3695434874688652852571405)
    ·
      refine ⟨1385788078008244819714277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3695434874688652852571405 1385788078008244819714277)
      ·
        refine ⟨259835264626545903696427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1385788078008244819714277 259835264626545903696427)
        ·
          refine ⟨389752896939818855544641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259835264626545903696427 389752896939818855544641)
          ·
            refine ⟨292314672704864141658481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389752896939818855544641 292314672704864141658481)
            ·
              refine ⟨219236004528648106243861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292314672704864141658481 219236004528648106243861)
              ·
                refine ⟨10276687712280379980181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 219236004528648106243861 10276687712280379980181)
                ·
                  rfl

theorem cell22_270186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_270186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270186 prefixEnd_270186 := by exact prefixLift 270186
  have htrace : WordTrace (prefixWord ++ tailWord_270186) baseStart_270186 baseEnd_270186 := by
    simpa [prefixWord, tailWord_270186, baseEnd_270186] using wordTrace_append hprefix tailTrace_270186
  have hstable : (prefixWord ++ tailWord_270186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270186).length < 2 ^ (prefixWord ++ tailWord_270186).sum := by decide
  have hdescent : baseEnd_270186 < baseStart_270186 := by decide
  rcases family_descends (prefixWord ++ tailWord_270186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270218 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 3, 3]
def baseStart_270218 : Nat := 118140960795 + 270218 * 2 ^ 59
def prefixEnd_270218 : Nat := 4983230072969 + 3 ^ 40 * 270218 * 2
def baseEnd_270218 : Nat := 92501143664486003021531

theorem tailTrace_270218 : CollatzResearch.WordTrace tailWord_270218 prefixEnd_270218 92501143664486003021531 := by
  unfold tailWord_270218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2463915033763452601338827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6570440090035873603570205 2463915033763452601338827)
  ·
    refine ⟨3695872550645178902008241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2463915033763452601338827 3695872550645178902008241)
    ·
      refine ⟨2771904412983884176506181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3695872550645178902008241 2771904412983884176506181)
      ·
        refine ⟨519732077434478283094909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2771904412983884176506181 519732077434478283094909)
        ·
          refine ⟨194899529037929356160591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 519732077434478283094909 194899529037929356160591)
          ·
            refine ⟨292349293556894034240887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194899529037929356160591 292349293556894034240887)
            ·
              refine ⟨438523940335341051361331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292349293556894034240887 438523940335341051361331)
              ·
                refine ⟨657785910503011577041997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438523940335341051361331 657785910503011577041997)
                ·
                  refine ⟨246669716438629341390749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657785910503011577041997 246669716438629341390749)
                  ·
                    refine ⟨92501143664486003021531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246669716438629341390749 92501143664486003021531)
                    ·
                      rfl

theorem cell22_270218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_270218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270218 prefixEnd_270218 := by exact prefixLift 270218
  have htrace : WordTrace (prefixWord ++ tailWord_270218) baseStart_270218 baseEnd_270218 := by
    simpa [prefixWord, tailWord_270218, baseEnd_270218] using wordTrace_append hprefix tailTrace_270218
  have hstable : (prefixWord ++ tailWord_270218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270218).length < 2 ^ (prefixWord ++ tailWord_270218).sum := by decide
  have hdescent : baseEnd_270218 < baseStart_270218 := by decide
  rcases family_descends (prefixWord ++ tailWord_270218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270244 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_270244 : Nat := 118140960795 + 270244 * 2 ^ 59
def prefixEnd_270244 : Nat := 4983230072969 + 3 ^ 40 * 270244 * 2
def baseEnd_270244 : Nat := 92510043995830601871451

theorem tailTrace_270244 : CollatzResearch.WordTrace tailWord_270244 prefixEnd_270244 92510043995830601871451 := by
  unfold tailWord_270244
  simp only [CollatzResearch.WordTrace]
  refine ⟨4928304216479808422900893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6571072288639744563867857 4928304216479808422900893)
  ·
    refine ⟨1848114081179928158587835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4928304216479808422900893 1848114081179928158587835)
    ·
      refine ⟨2772171121769892237881753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848114081179928158587835 2772171121769892237881753)
      ·
        refine ⟨2079128341327419178411315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2772171121769892237881753 2079128341327419178411315)
        ·
          refine ⟨3118692511991128767616973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079128341327419178411315 3118692511991128767616973)
          ·
            refine ⟨1169509691996673287856365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3118692511991128767616973 1169509691996673287856365)
            ·
              refine ⟨438566134498752482946137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1169509691996673287856365 438566134498752482946137)
              ·
                refine ⟨328924600874064362209603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438566134498752482946137 328924600874064362209603)
                ·
                  refine ⟨493386901311096543314405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328924600874064362209603 493386901311096543314405)
                  ·
                    refine ⟨92510043995830601871451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 493386901311096543314405 92510043995830601871451)
                    ·
                      rfl

theorem cell22_270244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_270244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270244 prefixEnd_270244 := by exact prefixLift 270244
  have htrace : WordTrace (prefixWord ++ tailWord_270244) baseStart_270244 baseEnd_270244 := by
    simpa [prefixWord, tailWord_270244, baseEnd_270244] using wordTrace_append hprefix tailTrace_270244
  have hstable : (prefixWord ++ tailWord_270244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270244).length < 2 ^ (prefixWord ++ tailWord_270244).sum := by decide
  have hdescent : baseEnd_270244 < baseStart_270244 := by decide
  rcases family_descends (prefixWord ++ tailWord_270244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270257 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_270257 : Nat := 118140960795 + 270257 * 2 ^ 59
def prefixEnd_270257 : Nat := 4983230072969 + 3 ^ 40 * 270257 * 2
def baseEnd_270257 : Nat := 92514494161502901296411

theorem tailTrace_270257 : CollatzResearch.WordTrace tailWord_270257 prefixEnd_270257 92514494161502901296411 := by
  unfold tailWord_270257
  simp only [CollatzResearch.WordTrace]
  refine ⟨9857082581912520066025025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6571388387941680044016683 9857082581912520066025025)
  ·
    refine ⟨7392811936434390049518769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9857082581912520066025025 7392811936434390049518769)
    ·
      refine ⟨5544608952325792537139077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7392811936434390049518769 5544608952325792537139077)
      ·
        refine ⟨1039614178561086100713577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5544608952325792537139077 1039614178561086100713577)
        ·
          refine ⟨779710633920814575535183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1039614178561086100713577 779710633920814575535183)
          ·
            refine ⟨1169565950881221863302775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779710633920814575535183 1169565950881221863302775)
            ·
              refine ⟨1754348926321832794954163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169565950881221863302775 1754348926321832794954163)
              ·
                refine ⟨2631523389482749192431245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754348926321832794954163 2631523389482749192431245)
                ·
                  refine ⟨986821271056030947161717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2631523389482749192431245 986821271056030947161717)
                  ·
                    refine ⟨92514494161502901296411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 986821271056030947161717 92514494161502901296411)
                    ·
                      rfl

theorem cell22_270257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_270257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270257 prefixEnd_270257 := by exact prefixLift 270257
  have htrace : WordTrace (prefixWord ++ tailWord_270257) baseStart_270257 baseEnd_270257 := by
    simpa [prefixWord, tailWord_270257, baseEnd_270257] using wordTrace_append hprefix tailTrace_270257
  have hstable : (prefixWord ++ tailWord_270257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270257).length < 2 ^ (prefixWord ++ tailWord_270257).sum := by decide
  have hdescent : baseEnd_270257 < baseStart_270257 := by decide
  rcases family_descends (prefixWord ++ tailWord_270257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270261 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 1, 4]
def baseStart_270261 : Nat := 118140960795 + 270261 * 2 ^ 59
def prefixEnd_270261 : Nat := 4983230072969 + 3 ^ 40 * 270261 * 2
def baseEnd_270261 : Nat := 92515863443248224196399

theorem tailTrace_270261 : CollatzResearch.WordTrace tailWord_270261 prefixEnd_270261 92515863443248224196399 := by
  unfold tailWord_270261
  simp only [CollatzResearch.WordTrace]
  refine ⟨9857228473898028749170637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6571485649265352499447091 9857228473898028749170637)
  ·
    refine ⟨3696460677711760780938989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9857228473898028749170637 3696460677711760780938989)
    ·
      refine ⟨1386172754141910292852121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3696460677711760780938989 1386172754141910292852121)
      ·
        refine ⟨1039629565606432719639091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1386172754141910292852121 1039629565606432719639091)
        ·
          refine ⟨1559444348409649079458637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039629565606432719639091 1559444348409649079458637)
          ·
            refine ⟨584791630653618404796989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1559444348409649079458637 584791630653618404796989)
            ·
              refine ⟨219296861495106901798871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 584791630653618404796989 219296861495106901798871)
              ·
                refine ⟨328945292242660352698307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219296861495106901798871 328945292242660352698307)
                ·
                  refine ⟨493417938363990529047461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328945292242660352698307 493417938363990529047461)
                  ·
                    refine ⟨92515863443248224196399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 493417938363990529047461 92515863443248224196399)
                    ·
                      rfl

theorem cell22_270261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_270261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270261 prefixEnd_270261 := by exact prefixLift 270261
  have htrace : WordTrace (prefixWord ++ tailWord_270261) baseStart_270261 baseEnd_270261 := by
    simpa [prefixWord, tailWord_270261, baseEnd_270261] using wordTrace_append hprefix tailTrace_270261
  have hstable : (prefixWord ++ tailWord_270261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270261).length < 2 ^ (prefixWord ++ tailWord_270261).sum := by decide
  have hdescent : baseEnd_270261 < baseStart_270261 := by decide
  rcases family_descends (prefixWord ++ tailWord_270261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270272 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_270272 : Nat := 118140960795 + 270272 * 2 ^ 59
def prefixEnd_270272 : Nat := 4983230072969 + 3 ^ 40 * 270272 * 2
def baseEnd_270272 : Nat := 92519628968047862171365

theorem tailTrace_270272 : CollatzResearch.WordTrace tailWord_270272 prefixEnd_270272 92519628968047862171365 := by
  unfold tailWord_270272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4928814838429088813910535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6571753117905451751880713 4928814838429088813910535)
  ·
    refine ⟨7393222257643633220865803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4928814838429088813910535 7393222257643633220865803)
    ·
      refine ⟨11089833386465449831298705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7393222257643633220865803 11089833386465449831298705)
      ·
        refine ⟨8317375039849087373474029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11089833386465449831298705 8317375039849087373474029)
        ·
          refine ⟨3119015639943407765052761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8317375039849087373474029 3119015639943407765052761)
          ·
            refine ⟨2339261729957555823789571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3119015639943407765052761 2339261729957555823789571)
            ·
              refine ⟨3508892594936333735684357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339261729957555823789571 3508892594936333735684357)
              ·
                refine ⟨657917361550562575440817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3508892594936333735684357 657917361550562575440817)
                ·
                  refine ⟨493438021162921931580613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 657917361550562575440817 493438021162921931580613)
                  ·
                    refine ⟨92519628968047862171365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 493438021162921931580613 92519628968047862171365)
                    ·
                      rfl

theorem cell22_270272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_270272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270272 prefixEnd_270272 := by exact prefixLift 270272
  have htrace : WordTrace (prefixWord ++ tailWord_270272) baseStart_270272 baseEnd_270272 := by
    simpa [prefixWord, tailWord_270272, baseEnd_270272] using wordTrace_append hprefix tailTrace_270272
  have hstable : (prefixWord ++ tailWord_270272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270272).length < 2 ^ (prefixWord ++ tailWord_270272).sum := by decide
  have hdescent : baseEnd_270272 < baseStart_270272 := by decide
  rcases family_descends (prefixWord ++ tailWord_270272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270306 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_270306 : Nat := 118140960795 + 270306 * 2 ^ 59
def prefixEnd_270306 : Nat := 4983230072969 + 3 ^ 40 * 270306 * 2
def baseEnd_270306 : Nat := 92531267862883106821261

theorem tailTrace_270306 : CollatzResearch.WordTrace tailWord_270306 prefixEnd_270306 92531267862883106821261 := by
  unfold tailWord_270306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2464717439683750358639693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6572579839156667623039181 2464717439683750358639693)
  ·
    refine ⟨924269039881406384489885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2464717439683750358639693 924269039881406384489885)
    ·
      refine ⟨346600889955527394183707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 924269039881406384489885 346600889955527394183707)
      ·
        refine ⟨519901334933291091275561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346600889955527394183707 519901334933291091275561)
        ·
          refine ⟨389926001199968318456671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519901334933291091275561 389926001199968318456671)
          ·
            refine ⟨584889001799952477685007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389926001199968318456671 584889001799952477685007)
            ·
              refine ⟨877333502699928716527511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584889001799952477685007 877333502699928716527511)
              ·
                refine ⟨1316000254049893074791267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877333502699928716527511 1316000254049893074791267)
                ·
                  refine ⟨1974000381074839612186901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316000254049893074791267 1974000381074839612186901)
                  ·
                    refine ⟨92531267862883106821261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1974000381074839612186901 92531267862883106821261)
                    ·
                      rfl

theorem cell22_270306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_270306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270306 prefixEnd_270306 := by exact prefixLift 270306
  have htrace : WordTrace (prefixWord ++ tailWord_270306) baseStart_270306 baseEnd_270306 := by
    simpa [prefixWord, tailWord_270306, baseEnd_270306] using wordTrace_append hprefix tailTrace_270306
  have hstable : (prefixWord ++ tailWord_270306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270306).length < 2 ^ (prefixWord ++ tailWord_270306).sum := by decide
  have hdescent : baseEnd_270306 < baseStart_270306 := by decide
  rcases family_descends (prefixWord ++ tailWord_270306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270332 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 7]
def baseStart_270332 : Nat := 118140960795 + 270332 * 2 ^ 59
def prefixEnd_270332 : Nat := 4983230072969 + 3 ^ 40 * 270332 * 2
def baseEnd_270332 : Nat := 30846722731409235223727

theorem tailTrace_270332 : CollatzResearch.WordTrace tailWord_270332 prefixEnd_270332 30846722731409235223727 := by
  unfold tailWord_270332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4929909028320403937502625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6573212037760538583336833 4929909028320403937502625)
  ·
    refine ⟨3697431771240302953126969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4929909028320403937502625 3697431771240302953126969)
    ·
      refine ⟨2773073828430227214845227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3697431771240302953126969 2773073828430227214845227)
      ·
        refine ⟨4159610742645340822267841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2773073828430227214845227 4159610742645340822267841)
        ·
          refine ⟨3119708056984005616700881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4159610742645340822267841 3119708056984005616700881)
          ·
            refine ⟨2339781042738004212525661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3119708056984005616700881 2339781042738004212525661)
            ·
              refine ⟨877417891026751579697123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2339781042738004212525661 877417891026751579697123)
              ·
                refine ⟨1316126836540127369545685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877417891026751579697123 1316126836540127369545685)
                ·
                  refine ⟨30846722731409235223727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1316126836540127369545685 30846722731409235223727)
                  ·
                    rfl

theorem cell22_270332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_270332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270332 prefixEnd_270332 := by exact prefixLift 270332
  have htrace : WordTrace (prefixWord ++ tailWord_270332) baseStart_270332 baseEnd_270332 := by
    simpa [prefixWord, tailWord_270332, baseEnd_270332] using wordTrace_append hprefix tailTrace_270332
  have hstable : (prefixWord ++ tailWord_270332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270332).length < 2 ^ (prefixWord ++ tailWord_270332).sum := by decide
  have hdescent : baseEnd_270332 < baseStart_270332 := by decide
  rcases family_descends (prefixWord ++ tailWord_270332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270342 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_270342 : Nat := 118140960795 + 270342 * 2 ^ 59
def prefixEnd_270342 : Nat := 4983230072969 + 3 ^ 40 * 270342 * 2
def baseEnd_270342 : Nat := 92543591398591012921151

theorem tailTrace_270342 : CollatzResearch.WordTrace tailWord_270342 prefixEnd_270342 92543591398591012921151 := by
  unfold tailWord_270342
  simp only [CollatzResearch.WordTrace]
  refine ⟨308130712081393111964665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6573455191069719721912853 308130712081393111964665)
  ·
    refine ⟨231098034061044833973499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 308130712081393111964665 231098034061044833973499)
    ·
      refine ⟨346647051091567250960249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231098034061044833973499 346647051091567250960249)
      ·
        refine ⟨259985288318675438220187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346647051091567250960249 259985288318675438220187)
        ·
          refine ⟨389977932478013157330281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259985288318675438220187 389977932478013157330281)
          ·
            refine ⟨292483449358509867997711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389977932478013157330281 292483449358509867997711)
            ·
              refine ⟨438725174037764801996567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292483449358509867997711 438725174037764801996567)
              ·
                refine ⟨658087761056647202994851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438725174037764801996567 658087761056647202994851)
                ·
                  refine ⟨987131641584970804492277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658087761056647202994851 987131641584970804492277)
                  ·
                    refine ⟨92543591398591012921151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 987131641584970804492277 92543591398591012921151)
                    ·
                      rfl

theorem cell22_270342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_270342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270342 prefixEnd_270342 := by exact prefixLift 270342
  have htrace : WordTrace (prefixWord ++ tailWord_270342) baseStart_270342 baseEnd_270342 := by
    simpa [prefixWord, tailWord_270342, baseEnd_270342] using wordTrace_append hprefix tailTrace_270342
  have hstable : (prefixWord ++ tailWord_270342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270342).length < 2 ^ (prefixWord ++ tailWord_270342).sum := by decide
  have hdescent : baseEnd_270342 < baseStart_270342 := by decide
  rcases family_descends (prefixWord ++ tailWord_270342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270347 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 2, 5]
def baseStart_270347 : Nat := 118140960795 + 270347 * 2 ^ 59
def prefixEnd_270347 : Nat := 4983230072969 + 3 ^ 40 * 270347 * 2
def baseEnd_270347 : Nat := 92545303000772666546135

theorem tailTrace_270347 : CollatzResearch.WordTrace tailWord_270347 prefixEnd_270347 92545303000772666546135 := by
  unfold tailWord_270347
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860365151586465436801295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6573576767724310291200863 9860365151586465436801295)
  ·
    refine ⟨14790547727379698155201943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9860365151586465436801295 14790547727379698155201943)
    ·
      refine ⟨22185821591069547232802915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14790547727379698155201943 22185821591069547232802915)
      ·
        refine ⟨33278732386604320849204373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22185821591069547232802915 33278732386604320849204373)
        ·
          refine ⟨1559940580622077539806455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33278732386604320849204373 1559940580622077539806455)
          ·
            refine ⟨2339910870933116309709683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559940580622077539806455 2339910870933116309709683)
            ·
              refine ⟨3509866306399674464564525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339910870933116309709683 3509866306399674464564525)
              ·
                refine ⟨1316199864899877924211697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3509866306399674464564525 1316199864899877924211697)
                ·
                  refine ⟨987149898674908443158773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1316199864899877924211697 987149898674908443158773)
                  ·
                    refine ⟨92545303000772666546135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 987149898674908443158773 92545303000772666546135)
                    ·
                      rfl

theorem cell22_270347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_270347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270347 prefixEnd_270347 := by exact prefixLift 270347
  have htrace : WordTrace (prefixWord ++ tailWord_270347) baseStart_270347 baseEnd_270347 := by
    simpa [prefixWord, tailWord_270347, baseEnd_270347] using wordTrace_append hprefix tailTrace_270347
  have hstable : (prefixWord ++ tailWord_270347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270347).length < 2 ^ (prefixWord ++ tailWord_270347).sum := by decide
  have hdescent : baseEnd_270347 < baseStart_270347 := by decide
  rcases family_descends (prefixWord ++ tailWord_270347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270424 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_270424 : Nat := 118140960795 + 270424 * 2 ^ 59
def prefixEnd_270424 : Nat := 4983230072969 + 3 ^ 40 * 270424 * 2
def baseEnd_270424 : Nat := 92571661674370132370899

theorem tailTrace_270424 : CollatzResearch.WordTrace tailWord_270424 prefixEnd_270424 92571661674370132370899 := by
  unfold tailWord_270424
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931586786153753793677163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6575449048205005058236217 4931586786153753793677163)
  ·
    refine ⟨7397380179230630690515745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4931586786153753793677163 7397380179230630690515745)
    ·
      refine ⟨5548035134422973017886809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7397380179230630690515745 5548035134422973017886809)
      ·
        refine ⟨4161026350817229763415107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5548035134422973017886809 4161026350817229763415107)
        ·
          refine ⟨6241539526225844645122661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4161026350817229763415107 6241539526225844645122661)
          ·
            refine ⟨1170288661167345870960499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6241539526225844645122661 1170288661167345870960499)
            ·
              refine ⟨1755432991751018806440749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170288661167345870960499 1755432991751018806440749)
              ·
                refine ⟨658287371906632052415281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1755432991751018806440749 658287371906632052415281)
                ·
                  refine ⟨493715528929974039311461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 658287371906632052415281 493715528929974039311461)
                  ·
                    refine ⟨92571661674370132370899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 493715528929974039311461 92571661674370132370899)
                    ·
                      rfl

theorem cell22_270424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_270424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270424 prefixEnd_270424 := by exact prefixLift 270424
  have htrace : WordTrace (prefixWord ++ tailWord_270424) baseStart_270424 baseEnd_270424 := by
    simpa [prefixWord, tailWord_270424, baseEnd_270424] using wordTrace_append hprefix tailTrace_270424
  have hstable : (prefixWord ++ tailWord_270424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270424).length < 2 ^ (prefixWord ++ tailWord_270424).sum := by decide
  have hdescent : baseEnd_270424 < baseStart_270424 := by decide
  rcases family_descends (prefixWord ++ tailWord_270424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270561 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 4, 3]
def baseStart_270561 : Nat := 118140960795 + 270561 * 2 ^ 59
def prefixEnd_270561 : Nat := 4983230072969 + 3 ^ 40 * 270561 * 2
def baseEnd_270561 : Nat := 92618559574147441695479

theorem tailTrace_270561 : CollatzResearch.WordTrace tailWord_270561 prefixEnd_270561 92618559574147441695479 := by
  unfold tailWord_270561
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868170372811179985091537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6578780248540786656727691 9868170372811179985091537)
  ·
    refine ⟨7401127779608384988818653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9868170372811179985091537 7401127779608384988818653)
    ·
      refine ⟨2775422917353144370806995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7401127779608384988818653 2775422917353144370806995)
      ·
        refine ⟨4163134376029716556210493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775422917353144370806995 4163134376029716556210493)
        ·
          refine ⟨1561175391011143708578935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4163134376029716556210493 1561175391011143708578935)
          ·
            refine ⟨2341763086516715562868403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561175391011143708578935 2341763086516715562868403)
            ·
              refine ⟨3512644629775073344302605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341763086516715562868403 3512644629775073344302605)
              ·
                refine ⟨1317241736165652504113477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3512644629775073344302605 1317241736165652504113477)
                ·
                  refine ⟨246982825531059844521277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317241736165652504113477 246982825531059844521277)
                  ·
                    refine ⟨92618559574147441695479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246982825531059844521277 92618559574147441695479)
                    ·
                      rfl

theorem cell22_270561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_270561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270561 prefixEnd_270561 := by exact prefixLift 270561
  have htrace : WordTrace (prefixWord ++ tailWord_270561) baseStart_270561 baseEnd_270561 := by
    simpa [prefixWord, tailWord_270561, baseEnd_270561] using wordTrace_append hprefix tailTrace_270561
  have hstable : (prefixWord ++ tailWord_270561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270561).length < 2 ^ (prefixWord ++ tailWord_270561).sum := by decide
  have hdescent : baseEnd_270561 < baseStart_270561 := by decide
  rcases family_descends (prefixWord ++ tailWord_270561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270589 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_270589 : Nat := 118140960795 + 270589 * 2 ^ 59
def prefixEnd_270589 : Nat := 4983230072969 + 3 ^ 40 * 270589 * 2
def baseEnd_270589 : Nat := 92628144546364701995393

theorem tailTrace_270589 : CollatzResearch.WordTrace tailWord_270589 prefixEnd_270589 92628144546364701995393 := by
  unfold tailWord_270589
  simp only [CollatzResearch.WordTrace]
  refine ⟨9869191616709740767110821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6579461077806493844740547 9869191616709740767110821)
  ·
    refine ⟨1850473428133076393833279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9869191616709740767110821 1850473428133076393833279)
    ·
      refine ⟨2775710142199614590749919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1850473428133076393833279 2775710142199614590749919)
      ·
        refine ⟨4163565213299421886124879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775710142199614590749919 4163565213299421886124879)
        ·
          refine ⟨6245347819949132829187319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4163565213299421886124879 6245347819949132829187319)
          ·
            refine ⟨9368021729923699243780979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6245347819949132829187319 9368021729923699243780979)
            ·
              refine ⟨14052032594885548865671469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9368021729923699243780979 14052032594885548865671469)
              ·
                refine ⟨5269512223082080824626801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14052032594885548865671469 5269512223082080824626801)
                ·
                  refine ⟨3952134167311560618470101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5269512223082080824626801 3952134167311560618470101)
                  ·
                    refine ⟨92628144546364701995393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3952134167311560618470101 92628144546364701995393)
                    ·
                      rfl

theorem cell22_270589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_270589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270589 prefixEnd_270589 := by exact prefixLift 270589
  have htrace : WordTrace (prefixWord ++ tailWord_270589) baseStart_270589 baseEnd_270589 := by
    simpa [prefixWord, tailWord_270589, baseEnd_270589] using wordTrace_append hprefix tailTrace_270589
  have hstable : (prefixWord ++ tailWord_270589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270589).length < 2 ^ (prefixWord ++ tailWord_270589).sum := by decide
  have hdescent : baseEnd_270589 < baseStart_270589 := by decide
  rcases family_descends (prefixWord ++ tailWord_270589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270619 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 7]
def baseStart_270619 : Nat := 118140960795 + 270619 * 2 ^ 59
def prefixEnd_270619 : Nat := 4983230072969 + 3 ^ 40 * 270619 * 2
def baseEnd_270619 : Nat := 30879471386484874581767

theorem tailTrace_270619 : CollatzResearch.WordTrace tailWord_270619 prefixEnd_270619 30879471386484874581767 := by
  unfold tailWord_270619
  simp only [CollatzResearch.WordTrace]
  refine ⟨9870285806601055890702911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6580190537734037260468607 9870285806601055890702911)
  ·
    refine ⟨14805428709901583836054367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9870285806601055890702911 14805428709901583836054367)
    ·
      refine ⟨22208143064852375754081551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14805428709901583836054367 22208143064852375754081551)
      ·
        refine ⟨33312214597278563631122327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22208143064852375754081551 33312214597278563631122327)
        ·
          refine ⟨49968321895917845446683491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33312214597278563631122327 49968321895917845446683491)
          ·
            refine ⟨74952482843876768170025237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49968321895917845446683491 74952482843876768170025237)
            ·
              refine ⟨3513397633306723507969933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74952482843876768170025237 3513397633306723507969933)
              ·
                refine ⟨1317524112490021315488725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3513397633306723507969933 1317524112490021315488725)
                ·
                  refine ⟨30879471386484874581767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1317524112490021315488725 30879471386484874581767)
                  ·
                    rfl

theorem cell22_270619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 7].length) (baseStart_270619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270619 prefixEnd_270619 := by exact prefixLift 270619
  have htrace : WordTrace (prefixWord ++ tailWord_270619) baseStart_270619 baseEnd_270619 := by
    simpa [prefixWord, tailWord_270619, baseEnd_270619] using wordTrace_append hprefix tailTrace_270619
  have hstable : (prefixWord ++ tailWord_270619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270619).length < 2 ^ (prefixWord ++ tailWord_270619).sum := by decide
  have hdescent : baseEnd_270619 < baseStart_270619 := by decide
  rcases family_descends (prefixWord ++ tailWord_270619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270636 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 5]
def baseStart_270636 : Nat := 118140960795 + 270636 * 2 ^ 59
def prefixEnd_270636 : Nat := 4983230072969 + 3 ^ 40 * 270636 * 2
def baseEnd_270636 : Nat := 30881411202290748690083

theorem tailTrace_270636 : CollatzResearch.WordTrace tailWord_270636 prefixEnd_270636 30881411202290748690083 := by
  unfold tailWord_270636
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935452923769733897035881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6580603898359645196047841 4935452923769733897035881)
  ·
    refine ⟨3701589692827300422776911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4935452923769733897035881 3701589692827300422776911)
    ·
      refine ⟨5552384539240950634165367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3701589692827300422776911 5552384539240950634165367)
      ·
        refine ⟨8328576808861425951248051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5552384539240950634165367 8328576808861425951248051)
        ·
          refine ⟨12492865213292138926872077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8328576808861425951248051 12492865213292138926872077)
          ·
            refine ⟨4684824454984552097577029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12492865213292138926872077 4684824454984552097577029)
            ·
              refine ⟨878404585309603518295693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4684824454984552097577029 878404585309603518295693)
              ·
                refine ⟨329401719491101319360885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 878404585309603518295693 329401719491101319360885)
                ·
                  refine ⟨30881411202290748690083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 329401719491101319360885 30881411202290748690083)
                  ·
                    rfl

theorem cell22_270636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_270636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270636 prefixEnd_270636 := by exact prefixLift 270636
  have htrace : WordTrace (prefixWord ++ tailWord_270636) baseStart_270636 baseEnd_270636 := by
    simpa [prefixWord, tailWord_270636, baseEnd_270636] using wordTrace_append hprefix tailTrace_270636
  have hstable : (prefixWord ++ tailWord_270636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270636).length < 2 ^ (prefixWord ++ tailWord_270636).sum := by decide
  have hdescent : baseEnd_270636 < baseStart_270636 := by decide
  rcases family_descends (prefixWord ++ tailWord_270636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270698 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_270698 : Nat := 118140960795 + 270698 * 2 ^ 59
def prefixEnd_270698 : Nat := 4983230072969 + 3 ^ 40 * 270698 * 2
def baseEnd_270698 : Nat := 30888485824641583673353

theorem tailTrace_270698 : CollatzResearch.WordTrace tailWord_270698 prefixEnd_270698 30888485824641583673353 := by
  unfold tailWord_270698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2468291793328713095707187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6582111448876568255219165 2468291793328713095707187)
  ·
    refine ⟨3702437689993069643560781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2468291793328713095707187 3702437689993069643560781)
    ·
      refine ⟨1388414133747401116335293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3702437689993069643560781 1388414133747401116335293)
      ·
        refine ⟨520655300155275418625735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1388414133747401116335293 520655300155275418625735)
        ·
          refine ⟨780982950232913127938603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520655300155275418625735 780982950232913127938603)
          ·
            refine ⟨1171474425349369691907905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780982950232913127938603 1171474425349369691907905)
            ·
              refine ⟨878605819012027268930929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1171474425349369691907905 878605819012027268930929)
              ·
                refine ⟨658954364259020451698197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878605819012027268930929 658954364259020451698197)
                ·
                  refine ⟨30888485824641583673353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 658954364259020451698197 30888485824641583673353)
                  ·
                    rfl

theorem cell22_270698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_270698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270698 prefixEnd_270698 := by exact prefixLift 270698
  have htrace : WordTrace (prefixWord ++ tailWord_270698) baseStart_270698 baseEnd_270698 := by
    simpa [prefixWord, tailWord_270698, baseEnd_270698] using wordTrace_append hprefix tailTrace_270698
  have hstable : (prefixWord ++ tailWord_270698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270698).length < 2 ^ (prefixWord ++ tailWord_270698).sum := by decide
  have hdescent : baseEnd_270698 < baseStart_270698 := by decide
  rcases family_descends (prefixWord ++ tailWord_270698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270700 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_270700 : Nat := 118140960795 + 270700 * 2 ^ 59
def prefixEnd_270700 : Nat := 4983230072969 + 3 ^ 40 * 270700 * 2
def baseEnd_270700 : Nat := 92666142114797412470053

theorem tailTrace_270700 : CollatzResearch.WordTrace tailWord_270700 prefixEnd_270700 92666142114797412470053 := by
  unfold tailWord_270700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936620059653803362200777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6582160079538404482934369 4936620059653803362200777)
  ·
    refine ⟨3702465044740352521650583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4936620059653803362200777 3702465044740352521650583)
    ·
      refine ⟨5553697567110528782475875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3702465044740352521650583 5553697567110528782475875)
      ·
        refine ⟨8330546350665793173713813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5553697567110528782475875 8330546350665793173713813)
        ·
          refine ⟨390494360187459055017835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8330546350665793173713813 390494360187459055017835)
          ·
            refine ⟨585741540281188582526753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390494360187459055017835 585741540281188582526753)
            ·
              refine ⟨439306155210891436895065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585741540281188582526753 439306155210891436895065)
              ·
                refine ⟨329479616408168577671299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439306155210891436895065 329479616408168577671299)
                ·
                  refine ⟨494219424612252866506949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329479616408168577671299 494219424612252866506949)
                  ·
                    refine ⟨92666142114797412470053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 494219424612252866506949 92666142114797412470053)
                    ·
                      rfl

theorem cell22_270700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_270700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270700 prefixEnd_270700 := by exact prefixLift 270700
  have htrace : WordTrace (prefixWord ++ tailWord_270700) baseStart_270700 baseEnd_270700 := by
    simpa [prefixWord, tailWord_270700, baseEnd_270700] using wordTrace_append hprefix tailTrace_270700
  have hstable : (prefixWord ++ tailWord_270700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270700).length < 2 ^ (prefixWord ++ tailWord_270700).sum := by decide
  have hdescent : baseEnd_270700 < baseStart_270700 := by decide
  rcases family_descends (prefixWord ++ tailWord_270700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270715 : List Nat := [1, 1, 1, 1, 1, 9, 1, 3, 4]
def baseStart_270715 : Nat := 118140960795 + 270715 * 2 ^ 59
def prefixEnd_270715 : Nat := 4983230072969 + 3 ^ 40 * 270715 * 2
def baseEnd_270715 : Nat := 30890425640447457781669

theorem tailTrace_270715 : CollatzResearch.WordTrace tailWord_270715 prefixEnd_270715 30890425640447457781669 := by
  unfold tailWord_270715
  simp only [CollatzResearch.WordTrace]
  refine ⟨9873787214253264286197599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6582524809502176190798399 9873787214253264286197599)
  ·
    refine ⟨14810680821379896429296399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9873787214253264286197599 14810680821379896429296399)
    ·
      refine ⟨22216021232069844643944599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14810680821379896429296399 22216021232069844643944599)
      ·
        refine ⟨33324031848104766965916899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22216021232069844643944599 33324031848104766965916899)
        ·
          refine ⟨49986047772157150448875349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33324031848104766965916899 49986047772157150448875349)
          ·
            refine ⟨292886998664983303411379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 49986047772157150448875349 292886998664983303411379)
            ·
              refine ⟨439330497997474955117069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292886998664983303411379 439330497997474955117069)
              ·
                refine ⟨164748936749053108168901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 439330497997474955117069 164748936749053108168901)
                ·
                  refine ⟨30890425640447457781669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164748936749053108168901 30890425640447457781669)
                  ·
                    rfl

theorem cell22_270715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 4].length) (baseStart_270715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270715 prefixEnd_270715 := by exact prefixLift 270715
  have htrace : WordTrace (prefixWord ++ tailWord_270715) baseStart_270715 baseEnd_270715 := by
    simpa [prefixWord, tailWord_270715, baseEnd_270715] using wordTrace_append hprefix tailTrace_270715
  have hstable : (prefixWord ++ tailWord_270715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270715).length < 2 ^ (prefixWord ++ tailWord_270715).sum := by decide
  have hdescent : baseEnd_270715 < baseStart_270715 := by decide
  rcases family_descends (prefixWord ++ tailWord_270715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270728 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_270728 : Nat := 118140960795 + 270728 * 2 ^ 59
def prefixEnd_270728 : Nat := 4983230072969 + 3 ^ 40 * 270728 * 2
def baseEnd_270728 : Nat := 92675727087014672769967

theorem tailTrace_270728 : CollatzResearch.WordTrace tailWord_270728 prefixEnd_270728 92675727087014672769967 := by
  unfold tailWord_270728
  simp only [CollatzResearch.WordTrace]
  refine ⟨4937130681603083753210419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6582840908804111670947225 4937130681603083753210419)
  ·
    refine ⟨7405696022404625629815629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4937130681603083753210419 7405696022404625629815629)
    ·
      refine ⟨2777136008401734611180861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7405696022404625629815629 2777136008401734611180861)
      ·
        refine ⟨1041426003150650479192823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2777136008401734611180861 1041426003150650479192823)
        ·
          refine ⟨1562139004725975718789235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041426003150650479192823 1562139004725975718789235)
          ·
            refine ⟨2343208507088963578183853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562139004725975718789235 2343208507088963578183853)
            ·
              refine ⟨878703190158361341818945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2343208507088963578183853 878703190158361341818945)
              ·
                refine ⟨659027392618771006364209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878703190158361341818945 659027392618771006364209)
                ·
                  refine ⟨494270544464078254773157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 659027392618771006364209 494270544464078254773157)
                  ·
                    refine ⟨92675727087014672769967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 494270544464078254773157 92675727087014672769967)
                    ·
                      rfl

theorem cell22_270728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_270728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270728 prefixEnd_270728 := by exact prefixLift 270728
  have htrace : WordTrace (prefixWord ++ tailWord_270728) baseStart_270728 baseEnd_270728 := by
    simpa [prefixWord, tailWord_270728, baseEnd_270728] using wordTrace_append hprefix tailTrace_270728
  have hstable : (prefixWord ++ tailWord_270728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270728).length < 2 ^ (prefixWord ++ tailWord_270728).sum := by decide
  have hdescent : baseEnd_270728 < baseStart_270728 := by decide
  rcases family_descends (prefixWord ++ tailWord_270728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270792 : List Nat := [2, 1, 3, 1, 3, 3, 1, 4, 1, 3]
def baseStart_270792 : Nat := 118140960795 + 270792 * 2 ^ 59
def prefixEnd_270792 : Nat := 4983230072969 + 3 ^ 40 * 270792 * 2
def baseEnd_270792 : Nat := 92697635594939839169771

theorem tailTrace_270792 : CollatzResearch.WordTrace tailWord_270792 prefixEnd_270792 92697635594939839169771 := by
  unfold tailWord_270792
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938297817487153218375315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6584397089982870957833753 4938297817487153218375315)
  ·
    refine ⟨7407446726230729827562973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4938297817487153218375315 7407446726230729827562973)
    ·
      refine ⟨2777792522336523685336115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7407446726230729827562973 2777792522336523685336115)
      ·
        refine ⟨4166688783504785528004173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2777792522336523685336115 4166688783504785528004173)
        ·
          refine ⟨1562508293814294573001565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4166688783504785528004173 1562508293814294573001565)
          ·
            refine ⟨585940610180360464875587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1562508293814294573001565 585940610180360464875587)
            ·
              refine ⟨878910915270540697313381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585940610180360464875587 878910915270540697313381)
              ·
                refine ⟨164795796613226380746259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 878910915270540697313381 164795796613226380746259)
                ·
                  refine ⟨247193694919839571119389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164795796613226380746259 247193694919839571119389)
                  ·
                    refine ⟨92697635594939839169771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 247193694919839571119389 92697635594939839169771)
                    ·
                      rfl

theorem cell22_270792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_270792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270792 prefixEnd_270792 := by exact prefixLift 270792
  have htrace : WordTrace (prefixWord ++ tailWord_270792) baseStart_270792 baseEnd_270792 := by
    simpa [prefixWord, tailWord_270792, baseEnd_270792] using wordTrace_append hprefix tailTrace_270792
  have hstable : (prefixWord ++ tailWord_270792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270792).length < 2 ^ (prefixWord ++ tailWord_270792).sum := by decide
  have hdescent : baseEnd_270792 < baseStart_270792 := by decide
  rcases family_descends (prefixWord ++ tailWord_270792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270854 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_270854 : Nat := 118140960795 + 270854 * 2 ^ 59
def prefixEnd_270854 : Nat := 4983230072969 + 3 ^ 40 * 270854 * 2
def baseEnd_270854 : Nat := 92718859461992344119581

theorem tailTrace_270854 : CollatzResearch.WordTrace tailWord_270854 prefixEnd_270854 92718859461992344119581 := by
  unfold tailWord_270854
  simp only [CollatzResearch.WordTrace]
  refine ⟨308714280023427844547113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6585904640499794017005077 308714280023427844547113)
  ·
    refine ⟨231535710017570883410335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 308714280023427844547113 231535710017570883410335)
    ·
      refine ⟨347303565026356325115503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231535710017570883410335 347303565026356325115503)
      ·
        refine ⟨520955347539534487673255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347303565026356325115503 520955347539534487673255)
        ·
          refine ⟨781433021309301731509883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520955347539534487673255 781433021309301731509883)
          ·
            refine ⟨1172149531963952597264825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781433021309301731509883 1172149531963952597264825)
            ·
              refine ⟨879112148972964447948619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172149531963952597264825 879112148972964447948619)
              ·
                refine ⟨1318668223459446671922929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879112148972964447948619 1318668223459446671922929)
                ·
                  refine ⟨989001167594585003942197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1318668223459446671922929 989001167594585003942197)
                  ·
                    refine ⟨92718859461992344119581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 989001167594585003942197 92718859461992344119581)
                    ·
                      rfl

theorem cell22_270854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_270854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270854 prefixEnd_270854 := by exact prefixLift 270854
  have htrace : WordTrace (prefixWord ++ tailWord_270854) baseStart_270854 baseEnd_270854 := by
    simpa [prefixWord, tailWord_270854, baseEnd_270854] using wordTrace_append hprefix tailTrace_270854
  have hstable : (prefixWord ++ tailWord_270854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270854).length < 2 ^ (prefixWord ++ tailWord_270854).sum := by decide
  have hdescent : baseEnd_270854 < baseStart_270854 := by decide
  rcases family_descends (prefixWord ++ tailWord_270854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270938 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_270938 : Nat := 118140960795 + 270938 * 2 ^ 59
def prefixEnd_270938 : Nat := 4983230072969 + 3 ^ 40 * 270938 * 2
def baseEnd_270938 : Nat := 92747614378644125019323

theorem tailTrace_270938 : CollatzResearch.WordTrace tailWord_270938 prefixEnd_270938 92747614378644125019323 := by
  unfold tailWord_270938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2470480173111343342891367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6587947128296915581043645 2470480173111343342891367)
  ·
    refine ⟨3705720259667015014337051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2470480173111343342891367 3705720259667015014337051)
    ·
      refine ⟨5558580389500522521505577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3705720259667015014337051 5558580389500522521505577)
      ·
        refine ⟨4168935292125391891129183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5558580389500522521505577 4168935292125391891129183)
        ·
          refine ⟨6253402938188087836693775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4168935292125391891129183 6253402938188087836693775)
          ·
            refine ⟨9380104407282131755040663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6253402938188087836693775 9380104407282131755040663)
            ·
              refine ⟨14070156610923197632560995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9380104407282131755040663 14070156610923197632560995)
              ·
                refine ⟨21105234916384796448841493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14070156610923197632560995 21105234916384796448841493)
                ·
                  refine ⟨989307886705537333539445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21105234916384796448841493 989307886705537333539445)
                  ·
                    refine ⟨92747614378644125019323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 989307886705537333539445 92747614378644125019323)
                    ·
                      rfl

theorem cell22_270938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_270938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270938 prefixEnd_270938 := by exact prefixLift 270938
  have htrace : WordTrace (prefixWord ++ tailWord_270938) baseStart_270938 baseEnd_270938 := by
    simpa [prefixWord, tailWord_270938, baseEnd_270938] using wordTrace_append hprefix tailTrace_270938
  have hstable : (prefixWord ++ tailWord_270938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270938).length < 2 ^ (prefixWord ++ tailWord_270938).sum := by decide
  have hdescent : baseEnd_270938 < baseStart_270938 := by decide
  rcases family_descends (prefixWord ++ tailWord_270938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270957 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 5]
def baseStart_270957 : Nat := 118140960795 + 270957 * 2 ^ 59
def prefixEnd_270957 : Nat := 4983230072969 + 3 ^ 40 * 270957 * 2
def baseEnd_270957 : Nat := 30918039488978136264755

theorem tailTrace_270957 : CollatzResearch.WordTrace tailWord_270957 prefixEnd_270957 30918039488978136264755 := by
  unfold tailWord_270957
  simp only [CollatzResearch.WordTrace]
  refine ⟨9882613679376539616507125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6588409119584359744338083 9882613679376539616507125)
  ·
    refine ⟨926495032441550589047543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9882613679376539616507125 926495032441550589047543)
    ·
      refine ⟨1389742548662325883571315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 926495032441550589047543 1389742548662325883571315)
      ·
        refine ⟨2084613822993488825356973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1389742548662325883571315 2084613822993488825356973)
        ·
          refine ⟨781730183622558309508865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2084613822993488825356973 781730183622558309508865)
          ·
            refine ⟨586297637716918732131649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 781730183622558309508865 586297637716918732131649)
            ·
              refine ⟨439723228287689049098737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586297637716918732131649 439723228287689049098737)
              ·
                refine ⟨329792421215766786824053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439723228287689049098737 329792421215766786824053)
                ·
                  refine ⟨30918039488978136264755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 329792421215766786824053 30918039488978136264755)
                  ·
                    rfl

theorem cell22_270957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_270957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270957 prefixEnd_270957 := by exact prefixLift 270957
  have htrace : WordTrace (prefixWord ++ tailWord_270957) baseStart_270957 baseEnd_270957 := by
    simpa [prefixWord, tailWord_270957, baseEnd_270957] using wordTrace_append hprefix tailTrace_270957
  have hstable : (prefixWord ++ tailWord_270957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270957).length < 2 ^ (prefixWord ++ tailWord_270957).sum := by decide
  have hdescent : baseEnd_270957 < baseStart_270957 := by decide
  rcases family_descends (prefixWord ++ tailWord_270957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270978 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_270978 : Nat := 118140960795 + 270978 * 2 ^ 59
def prefixEnd_270978 : Nat := 4983230072969 + 3 ^ 40 * 270978 * 2
def baseEnd_270978 : Nat := 92761307196097354019201

theorem tailTrace_270978 : CollatzResearch.WordTrace tailWord_270978 prefixEnd_270978 92761307196097354019201 := by
  unfold tailWord_270978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2470844903075115050755397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6588919741533640135347725 2470844903075115050755397)
  ·
    refine ⟨463283419326584072016637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2470844903075115050755397 463283419326584072016637)
    ·
      refine ⟨173731282247469027006239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 463283419326584072016637 173731282247469027006239)
      ·
        refine ⟨260596923371203540509359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173731282247469027006239 260596923371203540509359)
        ·
          refine ⟨390895385056805310764039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260596923371203540509359 390895385056805310764039)
          ·
            refine ⟨586343077585207966146059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390895385056805310764039 586343077585207966146059)
            ·
              refine ⟨879514616377811949219089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586343077585207966146059 879514616377811949219089)
              ·
                refine ⟨659635962283358961914317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879514616377811949219089 659635962283358961914317)
                ·
                  refine ⟨247363485856259610717869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659635962283358961914317 247363485856259610717869)
                  ·
                    refine ⟨92761307196097354019201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 247363485856259610717869 92761307196097354019201)
                    ·
                      rfl

theorem cell22_270978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_270978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_270978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_270978 prefixEnd_270978 := by exact prefixLift 270978
  have htrace : WordTrace (prefixWord ++ tailWord_270978) baseStart_270978 baseEnd_270978 := by
    simpa [prefixWord, tailWord_270978, baseEnd_270978] using wordTrace_append hprefix tailTrace_270978
  have hstable : (prefixWord ++ tailWord_270978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270978).length < 2 ^ (prefixWord ++ tailWord_270978).sum := by decide
  have hdescent : baseEnd_270978 < baseStart_270978 := by decide
  rcases family_descends (prefixWord ++ tailWord_270978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271000 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_271000 : Nat := 118140960795 + 271000 * 2 ^ 59
def prefixEnd_271000 : Nat := 4983230072969 + 3 ^ 40 * 271000 * 2
def baseEnd_271000 : Nat := 92768838245696629969133

theorem tailTrace_271000 : CollatzResearch.WordTrace tailWord_271000 prefixEnd_271000 92768838245696629969133 := by
  unfold tailWord_271000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4942091009110378980161227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6589454678813838640214969 4942091009110378980161227)
  ·
    refine ⟨7413136513665568470241841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4942091009110378980161227 7413136513665568470241841)
    ·
      refine ⟨5559852385249176352681381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7413136513665568470241841 5559852385249176352681381)
      ·
        refine ⟨1042472322234220566127759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5559852385249176352681381 1042472322234220566127759)
        ·
          refine ⟨1563708483351330849191639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042472322234220566127759 1563708483351330849191639)
          ·
            refine ⟨2345562725026996273787459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563708483351330849191639 2345562725026996273787459)
            ·
              refine ⟨3518344087540494410681189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345562725026996273787459 3518344087540494410681189)
              ·
                refine ⟨659689516413842702002723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3518344087540494410681189 659689516413842702002723)
                ·
                  refine ⟨989534274620764053004085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659689516413842702002723 989534274620764053004085)
                  ·
                    refine ⟨92768838245696629969133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 989534274620764053004085 92768838245696629969133)
                    ·
                      rfl

theorem cell22_271000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_271000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271000 prefixEnd_271000 := by exact prefixLift 271000
  have htrace : WordTrace (prefixWord ++ tailWord_271000) baseStart_271000 baseEnd_271000 := by
    simpa [prefixWord, tailWord_271000, baseEnd_271000] using wordTrace_append hprefix tailTrace_271000
  have hstable : (prefixWord ++ tailWord_271000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271000).length < 2 ^ (prefixWord ++ tailWord_271000).sum := by decide
  have hdescent : baseEnd_271000 < baseStart_271000 := by decide
  rcases family_descends (prefixWord ++ tailWord_271000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271004 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 1, 4]
def baseStart_271004 : Nat := 118140960795 + 271004 * 2 ^ 59
def prefixEnd_271004 : Nat := 4983230072969 + 3 ^ 40 * 271004 * 2
def baseEnd_271004 : Nat := 92770207527441952869121

theorem tailTrace_271004 : CollatzResearch.WordTrace tailWord_271004 prefixEnd_271004 92770207527441952869121 := by
  unfold tailWord_271004
  simp only [CollatzResearch.WordTrace]
  refine ⟨4942163955103133321734033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6589551940137511095645377 4942163955103133321734033)
  ·
    refine ⟨3706622966327349991300525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4942163955103133321734033 3706622966327349991300525)
    ·
      refine ⟨1389983612372756246737697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3706622966327349991300525 1389983612372756246737697)
      ·
        refine ⟨1042487709279567185053273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1389983612372756246737697 1042487709279567185053273)
        ·
          refine ⟨781865781959675388789955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042487709279567185053273 781865781959675388789955)
          ·
            refine ⟨1172798672939513083184933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781865781959675388789955 1172798672939513083184933)
            ·
              refine ⟨219899751176158703097175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1172798672939513083184933 219899751176158703097175)
              ·
                refine ⟨329849626764238054645763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219899751176158703097175 329849626764238054645763)
                ·
                  refine ⟨494774440146357081968645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329849626764238054645763 494774440146357081968645)
                  ·
                    refine ⟨92770207527441952869121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 494774440146357081968645 92770207527441952869121)
                    ·
                      rfl

theorem cell22_271004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_271004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271004 prefixEnd_271004 := by exact prefixLift 271004
  have htrace : WordTrace (prefixWord ++ tailWord_271004) baseStart_271004 baseEnd_271004 := by
    simpa [prefixWord, tailWord_271004, baseEnd_271004] using wordTrace_append hprefix tailTrace_271004
  have hstable : (prefixWord ++ tailWord_271004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271004).length < 2 ^ (prefixWord ++ tailWord_271004).sum := by decide
  have hdescent : baseEnd_271004 < baseStart_271004 := by decide
  rcases family_descends (prefixWord ++ tailWord_271004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271034 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 2, 3]
def baseStart_271034 : Nat := 118140960795 + 271034 * 2 ^ 59
def prefixEnd_271034 : Nat := 4983230072969 + 3 ^ 40 * 271034 * 2
def baseEnd_271034 : Nat := 92780477140531874619029

theorem tailTrace_271034 : CollatzResearch.WordTrace tailWord_271034 prefixEnd_271034 92780477140531874619029 := by
  unfold tailWord_271034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2471355525024395441765039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6590281400065054511373437 2471355525024395441765039)
  ·
    refine ⟨3707033287536593162647559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2471355525024395441765039 3707033287536593162647559)
    ·
      refine ⟨5560549931304889743971339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3707033287536593162647559 5560549931304889743971339)
      ·
        refine ⟨8340824896957334615957009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5560549931304889743971339 8340824896957334615957009)
        ·
          refine ⟨6255618672718000961967757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8340824896957334615957009 6255618672718000961967757)
          ·
            refine ⟨2345857002269250360737909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6255618672718000961967757 2345857002269250360737909)
            ·
              refine ⟨219924093962742221319179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2345857002269250360737909 219924093962742221319179)
              ·
                refine ⟨329886140944113331978769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219924093962742221319179 329886140944113331978769)
                ·
                  refine ⟨247414605708084998984077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329886140944113331978769 247414605708084998984077)
                  ·
                    refine ⟨92780477140531874619029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 247414605708084998984077 92780477140531874619029)
                    ·
                      rfl

theorem cell22_271034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_271034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271034 prefixEnd_271034 := by exact prefixLift 271034
  have htrace : WordTrace (prefixWord ++ tailWord_271034) baseStart_271034 baseEnd_271034 := by
    simpa [prefixWord, tailWord_271034, baseEnd_271034] using wordTrace_append hprefix tailTrace_271034
  have hstable : (prefixWord ++ tailWord_271034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271034).length < 2 ^ (prefixWord ++ tailWord_271034).sum := by decide
  have hdescent : baseEnd_271034 < baseStart_271034 := by decide
  rcases family_descends (prefixWord ++ tailWord_271034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271053 : List Nat := [1, 6, 2, 1, 2, 2, 1, 3, 4]
def baseStart_271053 : Nat := 118140960795 + 271053 * 2 ^ 59
def prefixEnd_271053 : Nat := 4983230072969 + 3 ^ 40 * 271053 * 2
def baseEnd_271053 : Nat := 30928993742940719464657

theorem tailTrace_271053 : CollatzResearch.WordTrace tailWord_271053 prefixEnd_271053 30928993742940719464657 := by
  unfold tailWord_271053
  simp only [CollatzResearch.WordTrace]
  refine ⟨9886115087028748012001813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6590743391352498674667875 9886115087028748012001813)
  ·
    refine ⟨463411644704472563062585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9886115087028748012001813 463411644704472563062585)
    ·
      refine ⟨347558733528354422296939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 463411644704472563062585 347558733528354422296939)
      ·
        refine ⟨521338100292531633445409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347558733528354422296939 521338100292531633445409)
        ·
          refine ⟨391003575219398725084057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 521338100292531633445409 391003575219398725084057)
          ·
            refine ⟨293252681414549043813043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391003575219398725084057 293252681414549043813043)
            ·
              refine ⟨439879022121823565719565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293252681414549043813043 439879022121823565719565)
              ·
                refine ⟨164954633295683837144837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 439879022121823565719565 164954633295683837144837)
                ·
                  refine ⟨30928993742940719464657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164954633295683837144837 30928993742940719464657)
                  ·
                    rfl

theorem cell22_271053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_271053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271053 prefixEnd_271053 := by exact prefixLift 271053
  have htrace : WordTrace (prefixWord ++ tailWord_271053) baseStart_271053 baseEnd_271053 := by
    simpa [prefixWord, tailWord_271053, baseEnd_271053] using wordTrace_append hprefix tailTrace_271053
  have hstable : (prefixWord ++ tailWord_271053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271053).length < 2 ^ (prefixWord ++ tailWord_271053).sum := by decide
  have hdescent : baseEnd_271053 < baseStart_271053 := by decide
  rcases family_descends (prefixWord ++ tailWord_271053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271167 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 1, 6]
def baseStart_271167 : Nat := 118140960795 + 271167 * 2 ^ 59
def prefixEnd_271167 : Nat := 4983230072969 + 3 ^ 40 * 271167 * 2
def baseEnd_271167 : Nat := 92826005758563861043621

theorem tailTrace_271167 : CollatzResearch.WordTrace tailWord_271167 prefixEnd_271167 92826005758563861043621 := by
  unfold tailWord_271167
  simp only [CollatzResearch.WordTrace]
  refine ⟨9890273008615745481651755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6593515339077163654434503 9890273008615745481651755)
  ·
    refine ⟨14835409512923618222477633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9890273008615745481651755 14835409512923618222477633)
    ·
      refine ⟨11126557134692713666858225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14835409512923618222477633 11126557134692713666858225)
      ·
        refine ⟨8344917851019535250143669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11126557134692713666858225 8344917851019535250143669)
        ·
          refine ⟨782336048533081429700969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8344917851019535250143669 782336048533081429700969)
          ·
            refine ⟨586752036399811072275727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782336048533081429700969 586752036399811072275727)
            ·
              refine ⟨880128054599716608413591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586752036399811072275727 880128054599716608413591)
              ·
                refine ⟨1320192081899574912620387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880128054599716608413591 1320192081899574912620387)
                ·
                  refine ⟨1980288122849362368930581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320192081899574912620387 1980288122849362368930581)
                  ·
                    refine ⟨92826005758563861043621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1980288122849362368930581 92826005758563861043621)
                    ·
                      rfl

theorem cell22_271167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_271167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271167 prefixEnd_271167 := by exact prefixLift 271167
  have htrace : WordTrace (prefixWord ++ tailWord_271167) baseStart_271167 baseEnd_271167 := by
    simpa [prefixWord, tailWord_271167, baseEnd_271167] using wordTrace_append hprefix tailTrace_271167
  have hstable : (prefixWord ++ tailWord_271167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271167).length < 2 ^ (prefixWord ++ tailWord_271167).sum := by decide
  have hdescent : baseEnd_271167 < baseStart_271167 := by decide
  rcases family_descends (prefixWord ++ tailWord_271167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271195 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 8, 6]
def baseStart_271195 : Nat := 118140960795 + 271195 * 2 ^ 59
def prefixEnd_271195 : Nat := 4983230072969 + 3 ^ 40 * 271195 * 2
def baseEnd_271195 : Nat := 92835590730781121343535

theorem tailTrace_271195 : CollatzResearch.WordTrace tailWord_271195 prefixEnd_271195 92835590730781121343535 := by
  unfold tailWord_271195
  simp only [CollatzResearch.WordTrace]
  refine ⟨9891294252514306263671039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6594196168342870842447359 9891294252514306263671039)
  ·
    refine ⟨14836941378771459395506559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9891294252514306263671039 14836941378771459395506559)
    ·
      refine ⟨22255412068157189093259839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14836941378771459395506559 22255412068157189093259839)
      ·
        refine ⟨33383118102235783639889759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22255412068157189093259839 33383118102235783639889759)
        ·
          refine ⟨50074677153353675459834639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33383118102235783639889759 50074677153353675459834639)
          ·
            refine ⟨75112015730030513189751959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50074677153353675459834639 75112015730030513189751959)
            ·
              refine ⟨112668023595045769784627939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75112015730030513189751959 112668023595045769784627939)
              ·
                refine ⟨169002035392568654676941909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112668023595045769784627939 169002035392568654676941909)
                ·
                  refine ⟨1980492602256663921995413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 169002035392568654676941909 1980492602256663921995413)
                  ·
                    refine ⟨92835590730781121343535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1980492602256663921995413 92835590730781121343535)
                    ·
                      rfl

theorem cell22_271195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_271195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271195 prefixEnd_271195 := by exact prefixLift 271195
  have htrace : WordTrace (prefixWord ++ tailWord_271195) baseStart_271195 baseEnd_271195 := by
    simpa [prefixWord, tailWord_271195, baseEnd_271195] using wordTrace_append hprefix tailTrace_271195
  have hstable : (prefixWord ++ tailWord_271195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271195).length < 2 ^ (prefixWord ++ tailWord_271195).sum := by decide
  have hdescent : baseEnd_271195 < baseStart_271195 := by decide
  rcases family_descends (prefixWord ++ tailWord_271195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271231 : List Nat := [1, 1, 2, 2, 1, 1, 7, 3, 1, 3]
def baseStart_271231 : Nat := 118140960795 + 271231 * 2 ^ 59
def prefixEnd_271231 : Nat := 4983230072969 + 3 ^ 40 * 271231 * 2
def baseEnd_271231 : Nat := 92847914266489027443425

theorem tailTrace_271231 : CollatzResearch.WordTrace tailWord_271231 prefixEnd_271231 92847914266489027443425 := by
  unfold tailWord_271231
  simp only [CollatzResearch.WordTrace]
  refine ⟨9892607280383884411981547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6595071520255922941321031 9892607280383884411981547)
  ·
    refine ⟨14838910920575826617972321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9892607280383884411981547 14838910920575826617972321)
    ·
      refine ⟨11129183190431869963479241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14838910920575826617972321 11129183190431869963479241)
      ·
        refine ⟨8346887392823902472609431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11129183190431869963479241 8346887392823902472609431)
        ·
          refine ⟨12520331089235853708914147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8346887392823902472609431 12520331089235853708914147)
          ·
            refine ⟨18780496633853780563371221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12520331089235853708914147 18780496633853780563371221)
            ·
              refine ⟨440167889855947981954013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18780496633853780563371221 440167889855947981954013)
              ·
                refine ⟨165062958695980493232755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 440167889855947981954013 165062958695980493232755)
                ·
                  refine ⟨247594438043970739849133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165062958695980493232755 247594438043970739849133)
                  ·
                    refine ⟨92847914266489027443425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 247594438043970739849133 92847914266489027443425)
                    ·
                      rfl

theorem cell22_271231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 1, 3].length) (baseStart_271231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271231 prefixEnd_271231 := by exact prefixLift 271231
  have htrace : WordTrace (prefixWord ++ tailWord_271231) baseStart_271231 baseEnd_271231 := by
    simpa [prefixWord, tailWord_271231, baseEnd_271231] using wordTrace_append hprefix tailTrace_271231
  have hstable : (prefixWord ++ tailWord_271231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271231).length < 2 ^ (prefixWord ++ tailWord_271231).sum := by decide
  have hdescent : baseEnd_271231 < baseStart_271231 := by decide
  rcases family_descends (prefixWord ++ tailWord_271231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271257 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_271257 : Nat := 118140960795 + 271257 * 2 ^ 59
def prefixEnd_271257 : Nat := 4983230072969 + 3 ^ 40 * 271257 * 2
def baseEnd_271257 : Nat := 92856814597833626293345

theorem tailTrace_271257 : CollatzResearch.WordTrace tailWord_271257 prefixEnd_271257 92856814597833626293345 := by
  unfold tailWord_271257
  simp only [CollatzResearch.WordTrace]
  refine ⟨9893555578289690852428025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6595703718859793901618683 9893555578289690852428025)
  ·
    refine ⟨7420166683717268139321019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9893555578289690852428025 7420166683717268139321019)
    ·
      refine ⟨11130250025575902208981529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7420166683717268139321019 11130250025575902208981529)
      ·
        refine ⟨8347687519181926656736147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11130250025575902208981529 8347687519181926656736147)
        ·
          refine ⟨12521531278772889985104221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8347687519181926656736147 12521531278772889985104221)
          ·
            refine ⟨4695574229539833744414083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12521531278772889985104221 4695574229539833744414083)
            ·
              refine ⟨7043361344309750616621125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4695574229539833744414083 7043361344309750616621125)
              ·
                refine ⟨1320630252058078240616461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7043361344309750616621125 1320630252058078240616461)
                ·
                  refine ⟨495236344521779340231173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1320630252058078240616461 495236344521779340231173)
                  ·
                    refine ⟨92856814597833626293345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 495236344521779340231173 92856814597833626293345)
                    ·
                      rfl

theorem cell22_271257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_271257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271257 prefixEnd_271257 := by exact prefixLift 271257
  have htrace : WordTrace (prefixWord ++ tailWord_271257) baseStart_271257 baseEnd_271257 := by
    simpa [prefixWord, tailWord_271257, baseEnd_271257] using wordTrace_append hprefix tailTrace_271257
  have hstable : (prefixWord ++ tailWord_271257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271257).length < 2 ^ (prefixWord ++ tailWord_271257).sum := by decide
  have hdescent : baseEnd_271257 < baseStart_271257 := by decide
  rcases family_descends (prefixWord ++ tailWord_271257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271287 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 3, 5]
def baseStart_271287 : Nat := 118140960795 + 271287 * 2 ^ 59
def prefixEnd_271287 : Nat := 4983230072969 + 3 ^ 40 * 271287 * 2
def baseEnd_271287 : Nat := 92867084210923548043253

theorem tailTrace_271287 : CollatzResearch.WordTrace tailWord_271287 prefixEnd_271287 92867084210923548043253 := by
  unfold tailWord_271287
  simp only [CollatzResearch.WordTrace]
  refine ⟨9894649768181005976020115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6596433178787337317346743 9894649768181005976020115)
  ·
    refine ⟨14841974652271508964030173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9894649768181005976020115 14841974652271508964030173)
    ·
      refine ⟨5565740494601815861511315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14841974652271508964030173 5565740494601815861511315)
      ·
        refine ⟨8348610741902723792266973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5565740494601815861511315 8348610741902723792266973)
        ·
          refine ⟨3130729028213521422100115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8348610741902723792266973 3130729028213521422100115)
          ·
            refine ⟨4696093542320282133150173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130729028213521422100115 4696093542320282133150173)
            ·
              refine ⟨1761035078370105799931315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4696093542320282133150173 1761035078370105799931315)
              ·
                refine ⟨2641552617555158699896973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761035078370105799931315 2641552617555158699896973)
                ·
                  refine ⟨990582231583184512461365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2641552617555158699896973 990582231583184512461365)
                  ·
                    refine ⟨92867084210923548043253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 990582231583184512461365 92867084210923548043253)
                    ·
                      rfl

theorem cell22_271287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_271287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271287 prefixEnd_271287 := by exact prefixLift 271287
  have htrace : WordTrace (prefixWord ++ tailWord_271287) baseStart_271287 baseEnd_271287 := by
    simpa [prefixWord, tailWord_271287, baseEnd_271287] using wordTrace_append hprefix tailTrace_271287
  have hstable : (prefixWord ++ tailWord_271287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271287).length < 2 ^ (prefixWord ++ tailWord_271287).sum := by decide
  have hdescent : baseEnd_271287 < baseStart_271287 := by decide
  rcases family_descends (prefixWord ++ tailWord_271287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271321 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 2, 3]
def baseStart_271321 : Nat := 118140960795 + 271321 * 2 ^ 59
def prefixEnd_271321 : Nat := 4983230072969 + 3 ^ 40 * 271321 * 2
def baseEnd_271321 : Nat := 92878723105758792693149

theorem tailTrace_271321 : CollatzResearch.WordTrace tailWord_271321 prefixEnd_271321 92878723105758792693149 := by
  unfold tailWord_271321
  simp only [CollatzResearch.WordTrace]
  refine ⟨9895889850057829782757817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6597259900038553188505211 9895889850057829782757817)
  ·
    refine ⟨7421917387543372337068363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9895889850057829782757817 7421917387543372337068363)
    ·
      refine ⟨11132876081315058505602545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7421917387543372337068363 11132876081315058505602545)
      ·
        refine ⟨8349657060986293879201909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11132876081315058505602545 8349657060986293879201909)
        ·
          refine ⟨782780349467465051175179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8349657060986293879201909 782780349467465051175179)
          ·
            refine ⟨1174170524201197576762769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782780349467465051175179 1174170524201197576762769)
            ·
              refine ⟨880627893150898182572077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174170524201197576762769 880627893150898182572077)
              ·
                refine ⟨330235459931586818464529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 880627893150898182572077 330235459931586818464529)
                ·
                  refine ⟨247676594948690113848397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330235459931586818464529 247676594948690113848397)
                  ·
                    refine ⟨92878723105758792693149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 247676594948690113848397 92878723105758792693149)
                    ·
                      rfl

theorem cell22_271321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 3].length) (baseStart_271321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271321 prefixEnd_271321 := by exact prefixLift 271321
  have htrace : WordTrace (prefixWord ++ tailWord_271321) baseStart_271321 baseEnd_271321 := by
    simpa [prefixWord, tailWord_271321, baseEnd_271321] using wordTrace_append hprefix tailTrace_271321
  have hstable : (prefixWord ++ tailWord_271321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271321).length < 2 ^ (prefixWord ++ tailWord_271321).sum := by decide
  have hdescent : baseEnd_271321 < baseStart_271321 := by decide
  rcases family_descends (prefixWord ++ tailWord_271321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271332 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_271332 : Nat := 118140960795 + 271332 * 2 ^ 59
def prefixEnd_271332 : Nat := 4983230072969 + 3 ^ 40 * 271332 * 2
def baseEnd_271332 : Nat := 92882488630558430668115

theorem tailTrace_271332 : CollatzResearch.WordTrace tailWord_271332 prefixEnd_271332 92882488630558430668115 := by
  unfold tailWord_271332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4948145526508989330704125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6597527368678652440938833 4948145526508989330704125)
  ·
    refine ⟨1855554572440870999014047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4948145526508989330704125 1855554572440870999014047)
    ·
      refine ⟨2783331858661306498521071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1855554572440870999014047 2783331858661306498521071)
      ·
        refine ⟨4174997787991959747781607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783331858661306498521071 4174997787991959747781607)
        ·
          refine ⟨6262496681987939621672411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4174997787991959747781607 6262496681987939621672411)
          ·
            refine ⟨9393745022981909432508617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6262496681987939621672411 9393745022981909432508617)
            ·
              refine ⟨7045308767236432074381463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9393745022981909432508617 7045308767236432074381463)
              ·
                refine ⟨10567963150854648111572195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7045308767236432074381463 10567963150854648111572195)
                ·
                  refine ⟨15851944726281972167358293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10567963150854648111572195 15851944726281972167358293)
                  ·
                    refine ⟨92882488630558430668115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15851944726281972167358293 92882488630558430668115)
                    ·
                      rfl

theorem cell22_271332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_271332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271332 prefixEnd_271332 := by exact prefixLift 271332
  have htrace : WordTrace (prefixWord ++ tailWord_271332) baseStart_271332 baseEnd_271332 := by
    simpa [prefixWord, tailWord_271332, baseEnd_271332] using wordTrace_append hprefix tailTrace_271332
  have hstable : (prefixWord ++ tailWord_271332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271332).length < 2 ^ (prefixWord ++ tailWord_271332).sum := by decide
  have hdescent : baseEnd_271332 < baseStart_271332 := by decide
  rcases family_descends (prefixWord ++ tailWord_271332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271430 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_271430 : Nat := 118140960795 + 271430 * 2 ^ 59
def prefixEnd_271430 : Nat := 4983230072969 + 3 ^ 40 * 271430 * 2
def baseEnd_271430 : Nat := 30972012011106280572605

theorem tailTrace_271430 : CollatzResearch.WordTrace tailWord_271430 prefixEnd_271430 30972012011106280572605 := by
  unfold tailWord_271430
  simp only [CollatzResearch.WordTrace]
  refine ⟨309370793958216918702367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6599910271108627598983829 309370793958216918702367)
  ·
    refine ⟨464056190937325378053551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 309370793958216918702367 464056190937325378053551)
    ·
      refine ⟨696084286405988067080327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464056190937325378053551 696084286405988067080327)
      ·
        refine ⟨1044126429608982100620491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696084286405988067080327 1044126429608982100620491)
        ·
          refine ⟨1566189644413473150930737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044126429608982100620491 1566189644413473150930737)
          ·
            refine ⟨1174642233310104863198053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566189644413473150930737 1174642233310104863198053)
            ·
              refine ⟨220245418745644661849635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1174642233310104863198053 220245418745644661849635)
              ·
                refine ⟨330368128118466992774453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220245418745644661849635 330368128118466992774453)
                ·
                  refine ⟨30972012011106280572605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 330368128118466992774453 30972012011106280572605)
                  ·
                    rfl

theorem cell22_271430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_271430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271430 prefixEnd_271430 := by exact prefixLift 271430
  have htrace : WordTrace (prefixWord ++ tailWord_271430) baseStart_271430 baseEnd_271430 := by
    simpa [prefixWord, tailWord_271430, baseEnd_271430] using wordTrace_append hprefix tailTrace_271430
  have hstable : (prefixWord ++ tailWord_271430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271430).length < 2 ^ (prefixWord ++ tailWord_271430).sum := by decide
  have hdescent : baseEnd_271430 < baseStart_271430 := by decide
  rcases family_descends (prefixWord ++ tailWord_271430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271469 : List Nat := [1, 5, 1, 1, 2, 12]
def baseStart_271469 : Nat := 118140960795 + 271469 * 2 ^ 59
def prefixEnd_271469 : Nat := 4983230072969 + 3 ^ 40 * 271469 * 2
def baseEnd_271469 : Nat := 1147276376917725185095

theorem tailTrace_271469 : CollatzResearch.WordTrace tailWord_271469 prefixEnd_271469 1147276376917725185095 := by
  unfold tailWord_271469
  simp only [CollatzResearch.WordTrace]
  refine ⟨9901287853521651059145461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6600858569014434039430307 9901287853521651059145461)
  ·
    refine ⟨928245736267654786794887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9901287853521651059145461 928245736267654786794887)
    ·
      refine ⟨1392368604401482180192331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928245736267654786794887 1392368604401482180192331)
      ·
        refine ⟨2088552906602223270288497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392368604401482180192331 2088552906602223270288497)
        ·
          refine ⟨1566414679951667452716373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2088552906602223270288497 1566414679951667452716373)
          ·
            refine ⟨1147276376917725185095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1566414679951667452716373 1147276376917725185095)
            ·
              rfl

theorem cell22_271469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 12].length) (baseStart_271469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271469 prefixEnd_271469 := by exact prefixLift 271469
  have htrace : WordTrace (prefixWord ++ tailWord_271469) baseStart_271469 baseEnd_271469 := by
    simpa [prefixWord, tailWord_271469, baseEnd_271469] using wordTrace_append hprefix tailTrace_271469
  have hstable : (prefixWord ++ tailWord_271469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271469).length < 2 ^ (prefixWord ++ tailWord_271469).sum := by decide
  have hdescent : baseEnd_271469 < baseStart_271469 := by decide
  rcases family_descends (prefixWord ++ tailWord_271469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271544 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_271544 : Nat := 118140960795 + 271544 * 2 ^ 59
def prefixEnd_271544 : Nat := 4983230072969 + 3 ^ 40 * 271544 * 2
def baseEnd_271544 : Nat := 92955060563060544367465

theorem tailTrace_271544 : CollatzResearch.WordTrace tailWord_271544 prefixEnd_271544 92955060563060544367465 := by
  unfold tailWord_271544
  simp only [CollatzResearch.WordTrace]
  refine ⟨4952011664124969434062843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6602682218833292578750457 4952011664124969434062843)
  ·
    refine ⟨7428017496187454151094265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4952011664124969434062843 7428017496187454151094265)
    ·
      refine ⟨5571013122140590613320699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7428017496187454151094265 5571013122140590613320699)
      ·
        refine ⟨8356519683210885919981049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5571013122140590613320699 8356519683210885919981049)
        ·
          refine ⟨6267389762408164439985787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8356519683210885919981049 6267389762408164439985787)
          ·
            refine ⟨9401084643612246659978681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6267389762408164439985787 9401084643612246659978681)
            ·
              refine ⟨7050813482709184994984011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9401084643612246659978681 7050813482709184994984011)
              ·
                refine ⟨10576220224063777492476017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7050813482709184994984011 10576220224063777492476017)
                ·
                  refine ⟨7932165168047833119357013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10576220224063777492476017 7932165168047833119357013)
                  ·
                    refine ⟨92955060563060544367465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7932165168047833119357013 92955060563060544367465)
                    ·
                      rfl

theorem cell22_271544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_271544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271544 prefixEnd_271544 := by exact prefixLift 271544
  have htrace : WordTrace (prefixWord ++ tailWord_271544) baseStart_271544 baseEnd_271544 := by
    simpa [prefixWord, tailWord_271544, baseEnd_271544] using wordTrace_append hprefix tailTrace_271544
  have hstable : (prefixWord ++ tailWord_271544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271544).length < 2 ^ (prefixWord ++ tailWord_271544).sum := by decide
  have hdescent : baseEnd_271544 < baseStart_271544 := by decide
  rcases family_descends (prefixWord ++ tailWord_271544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271554 : List Nat := [3, 5, 1, 1, 3, 1, 2, 6]
def baseStart_271554 : Nat := 118140960795 + 271554 * 2 ^ 59
def prefixEnd_271554 : Nat := 4983230072969 + 3 ^ 40 * 271554 * 2
def baseEnd_271554 : Nat := 10328720418602650179715

theorem tailTrace_271554 : CollatzResearch.WordTrace tailWord_271554 prefixEnd_271554 10328720418602650179715 := by
  unfold tailWord_271554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476097014553427643997429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6602925372142473717326477 2476097014553427643997429)
  ·
    refine ⟨232134095114383841624759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2476097014553427643997429 232134095114383841624759)
    ·
      refine ⟨348201142671575762437139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232134095114383841624759 348201142671575762437139)
      ·
        refine ⟨522301714007363643655709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348201142671575762437139 522301714007363643655709)
        ·
          refine ⟨195863142752761366370891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 522301714007363643655709 195863142752761366370891)
          ·
            refine ⟨293794714129142049556337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195863142752761366370891 293794714129142049556337)
            ·
              refine ⟨220346035596856537167253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293794714129142049556337 220346035596856537167253)
              ·
                refine ⟨10328720418602650179715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 220346035596856537167253 10328720418602650179715)
                ·
                  rfl

theorem cell22_271554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_271554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271554 prefixEnd_271554 := by exact prefixLift 271554
  have htrace : WordTrace (prefixWord ++ tailWord_271554) baseStart_271554 baseEnd_271554 := by
    simpa [prefixWord, tailWord_271554, baseEnd_271554] using wordTrace_append hprefix tailTrace_271554
  have hstable : (prefixWord ++ tailWord_271554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271554).length < 2 ^ (prefixWord ++ tailWord_271554).sum := by decide
  have hdescent : baseEnd_271554 < baseStart_271554 := by decide
  rcases family_descends (prefixWord ++ tailWord_271554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271612 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 1, 4]
def baseStart_271612 : Nat := 118140960795 + 271612 * 2 ^ 59
def prefixEnd_271612 : Nat := 4983230072969 + 3 ^ 40 * 271612 * 2
def baseEnd_271612 : Nat := 92978338352731033667257

theorem tailTrace_271612 : CollatzResearch.WordTrace tailWord_271612 prefixEnd_271612 92978338352731033667257 := by
  unfold tailWord_271612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953251746001793240800545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6604335661335724321067393 4953251746001793240800545)
  ·
    refine ⟨3714938809501344930600409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4953251746001793240800545 3714938809501344930600409)
    ·
      refine ⟨2786204107126008697950307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3714938809501344930600409 2786204107126008697950307)
      ·
        refine ⟨4179306160689013046925461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786204107126008697950307 4179306160689013046925461)
        ·
          refine ⟨195904976282297486574631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4179306160689013046925461 195904976282297486574631)
          ·
            refine ⟨293857464423446229861947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195904976282297486574631 293857464423446229861947)
            ·
              refine ⟨440786196635169344792921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293857464423446229861947 440786196635169344792921)
              ·
                refine ⟨330589647476377008594691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440786196635169344792921 330589647476377008594691)
                ·
                  refine ⟨495884471214565512892037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330589647476377008594691 495884471214565512892037)
                  ·
                    refine ⟨92978338352731033667257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 495884471214565512892037 92978338352731033667257)
                    ·
                      rfl

theorem cell22_271612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_271612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271612 prefixEnd_271612 := by exact prefixLift 271612
  have htrace : WordTrace (prefixWord ++ tailWord_271612) baseStart_271612 baseEnd_271612 := by
    simpa [prefixWord, tailWord_271612, baseEnd_271612] using wordTrace_append hprefix tailTrace_271612
  have hstable : (prefixWord ++ tailWord_271612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271612).length < 2 ^ (prefixWord ++ tailWord_271612).sum := by decide
  have hdescent : baseEnd_271612 < baseStart_271612 := by decide
  rcases family_descends (prefixWord ++ tailWord_271612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271651 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 2, 6]
def baseStart_271651 : Nat := 118140960795 + 271651 * 2 ^ 59
def prefixEnd_271651 : Nat := 4983230072969 + 3 ^ 40 * 271651 * 2
def baseEnd_271651 : Nat := 92991688849747931942137

theorem tailTrace_271651 : CollatzResearch.WordTrace tailWord_271651 prefixEnd_271651 92991688849747931942137 := by
  unfold tailWord_271651
  simp only [CollatzResearch.WordTrace]
  refine ⟨9907925938862296142270807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6605283959241530761513871 9907925938862296142270807)
  ·
    refine ⟨14861888908293444213406211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9907925938862296142270807 14861888908293444213406211)
    ·
      refine ⟨22292833362440166320109317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14861888908293444213406211 22292833362440166320109317)
      ·
        refine ⟨4179906255457531185020497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22292833362440166320109317 4179906255457531185020497)
        ·
          refine ⟨3134929691593148388765373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4179906255457531185020497 3134929691593148388765373)
          ·
            refine ⟨1175598634347430645787015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3134929691593148388765373 1175598634347430645787015)
            ·
              refine ⟨1763397951521145968680523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175598634347430645787015 1763397951521145968680523)
              ·
                refine ⟨2645096927281718953020785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763397951521145968680523 2645096927281718953020785)
                ·
                  refine ⟨1983822695461289214765589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2645096927281718953020785 1983822695461289214765589)
                  ·
                    refine ⟨92991688849747931942137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1983822695461289214765589 92991688849747931942137)
                    ·
                      rfl

theorem cell22_271651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_271651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271651 prefixEnd_271651 := by exact prefixLift 271651
  have htrace : WordTrace (prefixWord ++ tailWord_271651) baseStart_271651 baseEnd_271651 := by
    simpa [prefixWord, tailWord_271651, baseEnd_271651] using wordTrace_append hprefix tailTrace_271651
  have hstable : (prefixWord ++ tailWord_271651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271651).length < 2 ^ (prefixWord ++ tailWord_271651).sum := by decide
  have hdescent : baseEnd_271651 < baseStart_271651 := by decide
  rcases family_descends (prefixWord ++ tailWord_271651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271668 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_271668 : Nat := 118140960795 + 271668 * 2 ^ 59
def prefixEnd_271668 : Nat := 4983230072969 + 3 ^ 40 * 271668 * 2
def baseEnd_271668 : Nat := 92997508297165554267085

theorem tailTrace_271668 : CollatzResearch.WordTrace tailWord_271668 prefixEnd_271668 92997508297165554267085 := by
  unfold tailWord_271668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954272989900354022819829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6605697319867138697093105 4954272989900354022819829)
  ·
    refine ⟨464463092803158189639359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4954272989900354022819829 464463092803158189639359)
    ·
      refine ⟨696694639204737284459039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464463092803158189639359 696694639204737284459039)
      ·
        refine ⟨1045041958807105926688559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696694639204737284459039 1045041958807105926688559)
        ·
          refine ⟨1567562938210658890032839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045041958807105926688559 1567562938210658890032839)
          ·
            refine ⟨2351344407315988335049259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567562938210658890032839 2351344407315988335049259)
            ·
              refine ⟨3527016610973982502573889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351344407315988335049259 3527016610973982502573889)
              ·
                refine ⟨2645262458230486876930417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3527016610973982502573889 2645262458230486876930417)
                ·
                  refine ⟨1983946843672865157697813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2645262458230486876930417 1983946843672865157697813)
                  ·
                    refine ⟨92997508297165554267085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1983946843672865157697813 92997508297165554267085)
                    ·
                      rfl

theorem cell22_271668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_271668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271668 prefixEnd_271668 := by exact prefixLift 271668
  have htrace : WordTrace (prefixWord ++ tailWord_271668) baseStart_271668 baseEnd_271668 := by
    simpa [prefixWord, tailWord_271668, baseEnd_271668] using wordTrace_append hprefix tailTrace_271668
  have hstable : (prefixWord ++ tailWord_271668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271668).length < 2 ^ (prefixWord ++ tailWord_271668).sum := by decide
  have hdescent : baseEnd_271668 < baseStart_271668 := by decide
  rcases family_descends (prefixWord ++ tailWord_271668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271687 : List Nat := [1, 1, 4, 1, 2, 4, 2, 3, 1, 3]
def baseStart_271687 : Nat := 118140960795 + 271687 * 2 ^ 59
def prefixEnd_271687 : Nat := 4983230072969 + 3 ^ 40 * 271687 * 2
def baseEnd_271687 : Nat := 93004012385455838042027

theorem tailTrace_271687 : CollatzResearch.WordTrace tailWord_271687 prefixEnd_271687 93004012385455838042027 := by
  unfold tailWord_271687
  simp only [CollatzResearch.WordTrace]
  refine ⟨9909238966731874290581315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6606159311154582860387543 9909238966731874290581315)
  ·
    refine ⟨14863858450097811435871973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9909238966731874290581315 14863858450097811435871973)
    ·
      refine ⟨2786973459393339644225995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14863858450097811435871973 2786973459393339644225995)
      ·
        refine ⟨4180460189090009466338993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786973459393339644225995 4180460189090009466338993)
        ·
          refine ⟨3135345141817507099754245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4180460189090009466338993 3135345141817507099754245)
          ·
            refine ⟨587877214090782581203921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3135345141817507099754245 587877214090782581203921)
            ·
              refine ⟨440907910568086935902941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587877214090782581203921 440907910568086935902941)
              ·
                refine ⟨165340466463032600963603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 440907910568086935902941 165340466463032600963603)
                ·
                  refine ⟨248010699694548901445405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165340466463032600963603 248010699694548901445405)
                  ·
                    refine ⟨93004012385455838042027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 248010699694548901445405 93004012385455838042027)
                    ·
                      rfl

theorem cell22_271687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_271687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271687 prefixEnd_271687 := by exact prefixLift 271687
  have htrace : WordTrace (prefixWord ++ tailWord_271687) baseStart_271687 baseEnd_271687 := by
    simpa [prefixWord, tailWord_271687, baseEnd_271687] using wordTrace_append hprefix tailTrace_271687
  have hstable : (prefixWord ++ tailWord_271687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271687).length < 2 ^ (prefixWord ++ tailWord_271687).sum := by decide
  have hdescent : baseEnd_271687 < baseStart_271687 := by decide
  rcases family_descends (prefixWord ++ tailWord_271687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271730 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_271730 : Nat := 118140960795 + 271730 * 2 ^ 59
def prefixEnd_271730 : Nat := 4983230072969 + 3 ^ 40 * 271730 * 2
def baseEnd_271730 : Nat := 93018732164218059216895

theorem tailTrace_271730 : CollatzResearch.WordTrace tailWord_271730 prefixEnd_271730 93018732164218059216895 := by
  unfold tailWord_271730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477701826394023158599161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6607204870384061756264429 2477701826394023158599161)
  ·
    refine ⟨1858276369795517368949371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2477701826394023158599161 1858276369795517368949371)
    ·
      refine ⟨2787414554693276053424057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1858276369795517368949371 2787414554693276053424057)
      ·
        refine ⟨2090560916019957040068043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2787414554693276053424057 2090560916019957040068043)
        ·
          refine ⟨3135841374029935560102065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090560916019957040068043 3135841374029935560102065)
          ·
            refine ⟨2351881030522451670076549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3135841374029935560102065 2351881030522451670076549)
            ·
              refine ⟨440977693222959688139353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2351881030522451670076549 440977693222959688139353)
              ·
                refine ⟨330733269917219766104515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440977693222959688139353 330733269917219766104515)
                ·
                  refine ⟨496099904875829649156773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330733269917219766104515 496099904875829649156773)
                  ·
                    refine ⟨93018732164218059216895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 496099904875829649156773 93018732164218059216895)
                    ·
                      rfl

theorem cell22_271730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_271730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271730 prefixEnd_271730 := by exact prefixLift 271730
  have htrace : WordTrace (prefixWord ++ tailWord_271730) baseStart_271730 baseEnd_271730 := by
    simpa [prefixWord, tailWord_271730, baseEnd_271730] using wordTrace_append hprefix tailTrace_271730
  have hstable : (prefixWord ++ tailWord_271730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271730).length < 2 ^ (prefixWord ++ tailWord_271730).sum := by decide
  have hdescent : baseEnd_271730 < baseStart_271730 := by decide
  rcases family_descends (prefixWord ++ tailWord_271730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271773 : List Nat := [1, 4, 2, 1, 3, 1, 1, 9]
def baseStart_271773 : Nat := 118140960795 + 271773 * 2 ^ 59
def prefixEnd_271773 : Nat := 4983230072969 + 3 ^ 40 * 271773 * 2
def baseEnd_271773 : Nat := 10337050215886697821307

theorem tailTrace_271773 : CollatzResearch.WordTrace tailWord_271773 prefixEnd_271773 10337050215886697821307 := by
  unfold tailWord_271773
  simp only [CollatzResearch.WordTrace]
  refine ⟨9912375644420310978211973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6608250429613540652141315 9912375644420310978211973)
  ·
    refine ⟨1858570433328808308414745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9912375644420310978211973 1858570433328808308414745)
    ·
      refine ⟨1393927824996606231311059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1858570433328808308414745 1393927824996606231311059)
      ·
        refine ⟨2090891737494909346966589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393927824996606231311059 2090891737494909346966589)
        ·
          refine ⟨784084401560591005112471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2090891737494909346966589 784084401560591005112471)
          ·
            refine ⟨1176126602340886507668707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784084401560591005112471 1176126602340886507668707)
            ·
              refine ⟨1764189903511329761503061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176126602340886507668707 1764189903511329761503061)
              ·
                refine ⟨10337050215886697821307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1764189903511329761503061 10337050215886697821307)
                ·
                  rfl

theorem cell22_271773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 9].length) (baseStart_271773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271773 prefixEnd_271773 := by exact prefixLift 271773
  have htrace : WordTrace (prefixWord ++ tailWord_271773) baseStart_271773 baseEnd_271773 := by
    simpa [prefixWord, tailWord_271773, baseEnd_271773] using wordTrace_append hprefix tailTrace_271773
  have hstable : (prefixWord ++ tailWord_271773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271773).length < 2 ^ (prefixWord ++ tailWord_271773).sum := by decide
  have hdescent : baseEnd_271773 < baseStart_271773 := by decide
  rcases family_descends (prefixWord ++ tailWord_271773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271833 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_271833 : Nat := 118140960795 + 271833 * 2 ^ 59
def prefixEnd_271833 : Nat := 4983230072969 + 3 ^ 40 * 271833 * 2
def baseEnd_271833 : Nat := 93053991169160123891579

theorem tailTrace_271833 : CollatzResearch.WordTrace tailWord_271833 prefixEnd_271833 93053991169160123891579 := by
  unfold tailWord_271833
  simp only [CollatzResearch.WordTrace]
  refine ⟨9914564024202941225396153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6609709349468627483597435 9914564024202941225396153)
  ·
    refine ⟨7435923018152205919047115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9914564024202941225396153 7435923018152205919047115)
    ·
      refine ⟨11153884527228308878570673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7435923018152205919047115 11153884527228308878570673)
      ·
        refine ⟨8365413395421231658928005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11153884527228308878570673 8365413395421231658928005)
        ·
          refine ⟨1568515011641480936049001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8365413395421231658928005 1568515011641480936049001)
          ·
            refine ⟨1176386258731110702036751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1568515011641480936049001 1176386258731110702036751)
            ·
              refine ⟨1764579388096666053055127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176386258731110702036751 1764579388096666053055127)
              ·
                refine ⟨2646869082144999079582691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764579388096666053055127 2646869082144999079582691)
                ·
                  refine ⟨3970303623217498619374037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2646869082144999079582691 3970303623217498619374037)
                  ·
                    refine ⟨93053991169160123891579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3970303623217498619374037 93053991169160123891579)
                    ·
                      rfl

theorem cell22_271833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_271833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271833 prefixEnd_271833 := by exact prefixLift 271833
  have htrace : WordTrace (prefixWord ++ tailWord_271833) baseStart_271833 baseEnd_271833 := by
    simpa [prefixWord, tailWord_271833, baseEnd_271833] using wordTrace_append hprefix tailTrace_271833
  have hstable : (prefixWord ++ tailWord_271833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271833).length < 2 ^ (prefixWord ++ tailWord_271833).sum := by decide
  have hdescent : baseEnd_271833 < baseStart_271833 := by decide
  rcases family_descends (prefixWord ++ tailWord_271833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271925 : List Nat := [1, 3, 3, 1, 1, 5, 8]
def baseStart_271925 : Nat := 118140960795 + 271925 * 2 ^ 59
def prefixEnd_271925 : Nat := 4983230072969 + 3 ^ 40 * 271925 * 2
def baseEnd_271925 : Nat := 3447610542566761133011

theorem tailTrace_271925 : CollatzResearch.WordTrace tailWord_271925 prefixEnd_271925 3447610542566761133011 := by
  unfold tailWord_271925
  simp only [CollatzResearch.WordTrace]
  refine ⟨9917919539869640937745229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6611946359913093958496819 9917919539869640937745229)
  ·
    refine ⟨3719219827451115351654461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9917919539869640937745229 3719219827451115351654461)
    ·
      refine ⟨1394707435294168256870423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3719219827451115351654461 1394707435294168256870423)
      ·
        refine ⟨2092061152941252385305635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1394707435294168256870423 2092061152941252385305635)
        ·
          refine ⟨3138091729411878577958453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2092061152941252385305635 3138091729411878577958453)
          ·
            refine ⟨294196099632363616683605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3138091729411878577958453 294196099632363616683605)
            ·
              refine ⟨3447610542566761133011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 294196099632363616683605 3447610542566761133011)
              ·
                rfl

theorem cell22_271925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 8].length) (baseStart_271925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_271925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_271925 prefixEnd_271925 := by exact prefixLift 271925
  have htrace : WordTrace (prefixWord ++ tailWord_271925) baseStart_271925 baseEnd_271925 := by
    simpa [prefixWord, tailWord_271925, baseEnd_271925] using wordTrace_append hprefix tailTrace_271925
  have hstable : (prefixWord ++ tailWord_271925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271925).length < 2 ^ (prefixWord ++ tailWord_271925).sum := by decide
  have hdescent : baseEnd_271925 < baseStart_271925 := by decide
  rcases family_descends (prefixWord ++ tailWord_271925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272000 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_272000 : Nat := 118140960795 + 272000 * 2 ^ 59
def prefixEnd_272000 : Nat := 4983230072969 + 3 ^ 40 * 272000 * 2
def baseEnd_272000 : Nat := 93111158682027354966067

theorem tailTrace_272000 : CollatzResearch.WordTrace tailWord_272000 prefixEnd_272000 93111158682027354966067 := by
  unfold tailWord_272000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4960327507298964373362727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6613770009731952497816969 4960327507298964373362727)
  ·
    refine ⟨7440491260948446560044091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4960327507298964373362727 7440491260948446560044091)
    ·
      refine ⟨11160736891422669840066137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7440491260948446560044091 11160736891422669840066137)
      ·
        refine ⟨8370552668567002380049603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11160736891422669840066137 8370552668567002380049603)
        ·
          refine ⟨12555829002850503570074405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8370552668567002380049603 12555829002850503570074405)
          ·
            refine ⟨2354217938034469419388951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12555829002850503570074405 2354217938034469419388951)
            ·
              refine ⟨3531326907051704129083427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354217938034469419388951 3531326907051704129083427)
              ·
                refine ⟨5296990360577556193625141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531326907051704129083427 5296990360577556193625141)
                ·
                  refine ⟨496592846304145893152357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5296990360577556193625141 496592846304145893152357)
                  ·
                    refine ⟨93111158682027354966067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 496592846304145893152357 93111158682027354966067)
                    ·
                      rfl

theorem cell22_272000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_272000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272000 prefixEnd_272000 := by exact prefixLift 272000
  have htrace : WordTrace (prefixWord ++ tailWord_272000) baseStart_272000 baseEnd_272000 := by
    simpa [prefixWord, tailWord_272000, baseEnd_272000] using wordTrace_append hprefix tailTrace_272000
  have hstable : (prefixWord ++ tailWord_272000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272000).length < 2 ^ (prefixWord ++ tailWord_272000).sum := by decide
  have hdescent : baseEnd_272000 < baseStart_272000 := by decide
  rcases family_descends (prefixWord ++ tailWord_272000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272047 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 4, 3]
def baseStart_272047 : Nat := 118140960795 + 272047 * 2 ^ 59
def prefixEnd_272047 : Nat := 4983230072969 + 3 ^ 40 * 272047 * 2
def baseEnd_272047 : Nat := 93127247742534899040923

theorem tailTrace_272047 : CollatzResearch.WordTrace tailWord_272047 prefixEnd_272047 93127247742534899040923 := by
  unfold tailWord_272047
  simp only [CollatzResearch.WordTrace]
  refine ⟨9922369245427655773686395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6614912830285103849124263 9922369245427655773686395)
  ·
    refine ⟨14883553868141483660529593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9922369245427655773686395 14883553868141483660529593)
    ·
      refine ⟨11162665401106112745397195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14883553868141483660529593 11162665401106112745397195)
      ·
        refine ⟨16743998101659169118095793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11162665401106112745397195 16743998101659169118095793)
        ·
          refine ⟨12557998576244376838571845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16743998101659169118095793 12557998576244376838571845)
          ·
            refine ⟨2354624733045820657232221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12557998576244376838571845 2354624733045820657232221)
            ·
              refine ⟨882984274892182746462083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2354624733045820657232221 882984274892182746462083)
              ·
                refine ⟨1324476412338274119693125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882984274892182746462083 1324476412338274119693125)
                ·
                  refine ⟨248339327313426397442461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324476412338274119693125 248339327313426397442461)
                  ·
                    refine ⟨93127247742534899040923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 248339327313426397442461 93127247742534899040923)
                    ·
                      rfl

theorem cell22_272047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 3].length) (baseStart_272047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272047 prefixEnd_272047 := by exact prefixLift 272047
  have htrace : WordTrace (prefixWord ++ tailWord_272047) baseStart_272047 baseEnd_272047 := by
    simpa [prefixWord, tailWord_272047, baseEnd_272047] using wordTrace_append hprefix tailTrace_272047
  have hstable : (prefixWord ++ tailWord_272047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272047).length < 2 ^ (prefixWord ++ tailWord_272047).sum := by decide
  have hdescent : baseEnd_272047 < baseStart_272047 := by decide
  rcases family_descends (prefixWord ++ tailWord_272047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272062 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_272062 : Nat := 118140960795 + 272062 * 2 ^ 59
def prefixEnd_272062 : Nat := 4983230072969 + 3 ^ 40 * 272062 * 2
def baseEnd_272062 : Nat := 93132382549079859915877

theorem tailTrace_272062 : CollatzResearch.WordTrace tailWord_272062 prefixEnd_272062 93132382549079859915877 := by
  unfold tailWord_272062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240364542546664166935305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6615277560248875556988293 1240364542546664166935305)
  ·
    refine ⟨930273406909998125201479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1240364542546664166935305 930273406909998125201479)
    ·
      refine ⟨1395410110364997187802219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930273406909998125201479 1395410110364997187802219)
      ·
        refine ⟨2093115165547495781703329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395410110364997187802219 2093115165547495781703329)
        ·
          refine ⟨1569836374160621836277497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2093115165547495781703329 1569836374160621836277497)
          ·
            refine ⟨1177377280620466377208123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1569836374160621836277497 1177377280620466377208123)
            ·
              refine ⟨1766065920930699565812185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177377280620466377208123 1766065920930699565812185)
              ·
                refine ⟨1324549440698024674359139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1766065920930699565812185 1324549440698024674359139)
                ·
                  refine ⟨1986824161047037011538709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324549440698024674359139 1986824161047037011538709)
                  ·
                    refine ⟨93132382549079859915877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1986824161047037011538709 93132382549079859915877)
                    ·
                      rfl

theorem cell22_272062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_272062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272062 prefixEnd_272062 := by exact prefixLift 272062
  have htrace : WordTrace (prefixWord ++ tailWord_272062) baseStart_272062 baseEnd_272062 := by
    simpa [prefixWord, tailWord_272062, baseEnd_272062] using wordTrace_append hprefix tailTrace_272062
  have hstable : (prefixWord ++ tailWord_272062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272062).length < 2 ^ (prefixWord ++ tailWord_272062).sum := by decide
  have hdescent : baseEnd_272062 < baseStart_272062 := by decide
  rcases family_descends (prefixWord ++ tailWord_272062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272197 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_272197 : Nat := 118140960795 + 272197 * 2 ^ 59
def prefixEnd_272197 : Nat := 4983230072969 + 3 ^ 40 * 272197 * 2
def baseEnd_272197 : Nat := 93178595807984507790463

theorem tailTrace_272197 : CollatzResearch.WordTrace tailWord_272197 prefixEnd_272197 93178595807984507790463 := by
  unfold tailWord_272197
  simp only [CollatzResearch.WordTrace]
  refine ⟨9927840194884231391646845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6618560129922820927764563 9927840194884231391646845)
  ·
    refine ⟨3722940073081586771867567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9927840194884231391646845 3722940073081586771867567)
    ·
      refine ⟨5584410109622380157801351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3722940073081586771867567 5584410109622380157801351)
      ·
        refine ⟨8376615164433570236702027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5584410109622380157801351 8376615164433570236702027)
        ·
          refine ⟨12564922746650355355053041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8376615164433570236702027 12564922746650355355053041)
          ·
            refine ⟨9423692059987766516289781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12564922746650355355053041 9423692059987766516289781)
            ·
              refine ⟨883471130623853110902167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9423692059987766516289781 883471130623853110902167)
              ·
                refine ⟨1325206695935779666353251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883471130623853110902167 1325206695935779666353251)
                ·
                  refine ⟨1987810043903669499529877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325206695935779666353251 1987810043903669499529877)
                  ·
                    refine ⟨93178595807984507790463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1987810043903669499529877 93178595807984507790463)
                    ·
                      rfl

theorem cell22_272197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_272197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272197 prefixEnd_272197 := by exact prefixLift 272197
  have htrace : WordTrace (prefixWord ++ tailWord_272197) baseStart_272197 baseEnd_272197 := by
    simpa [prefixWord, tailWord_272197, baseEnd_272197] using wordTrace_append hprefix tailTrace_272197
  have hstable : (prefixWord ++ tailWord_272197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272197).length < 2 ^ (prefixWord ++ tailWord_272197).sum := by decide
  have hdescent : baseEnd_272197 < baseStart_272197 := by decide
  rcases family_descends (prefixWord ++ tailWord_272197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272246 : List Nat := [5, 1, 1, 3, 2, 1, 1, 8]
def baseStart_272246 : Nat := 118140960795 + 272246 * 2 ^ 59
def prefixEnd_272246 : Nat := 4983230072969 + 3 ^ 40 * 272246 * 2
def baseEnd_272246 : Nat := 10355041056596079257257

theorem tailTrace_272246 : CollatzResearch.WordTrace tailWord_272246 prefixEnd_272246 10355041056596079257257 := by
  unfold tailWord_272246
  simp only [CollatzResearch.WordTrace]
  refine ⟨620601710731669547511287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6619751581137808506787061 620601710731669547511287)
  ·
    refine ⟨930902566097504321266931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 620601710731669547511287 930902566097504321266931)
    ·
      refine ⟨1396353849146256481900397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930902566097504321266931 1396353849146256481900397)
      ·
        refine ⟨523632693429846180712649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1396353849146256481900397 523632693429846180712649)
        ·
          refine ⟨392724520072384635534487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523632693429846180712649 392724520072384635534487)
          ·
            refine ⟨589086780108576953301731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392724520072384635534487 589086780108576953301731)
            ·
              refine ⟨883630170162865429952597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589086780108576953301731 883630170162865429952597)
              ·
                refine ⟨10355041056596079257257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 883630170162865429952597 10355041056596079257257)
                ·
                  rfl

theorem cell22_272246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_272246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272246 prefixEnd_272246 := by exact prefixLift 272246
  have htrace : WordTrace (prefixWord ++ tailWord_272246) baseStart_272246 baseEnd_272246 := by
    simpa [prefixWord, tailWord_272246, baseEnd_272246] using wordTrace_append hprefix tailTrace_272246
  have hstable : (prefixWord ++ tailWord_272246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272246).length < 2 ^ (prefixWord ++ tailWord_272246).sum := by decide
  have hdescent : baseEnd_272246 < baseStart_272246 := by decide
  rcases family_descends (prefixWord ++ tailWord_272246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272334 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_272334 : Nat := 118140960795 + 272334 * 2 ^ 59
def prefixEnd_272334 : Nat := 4983230072969 + 3 ^ 40 * 272334 * 2
def baseEnd_272334 : Nat := 93225493707761817115043

theorem tailTrace_272334 : CollatzResearch.WordTrace tailWord_272334 prefixEnd_272334 93225493707761817115043 := by
  unfold tailWord_272334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241604624423487973673007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6621891330258602526256037 1241604624423487973673007)
  ·
    refine ⟨1862406936635231960509511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1241604624423487973673007 1862406936635231960509511)
    ·
      refine ⟨2793610404952847940764267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1862406936635231960509511 2793610404952847940764267)
      ·
        refine ⟨4190415607429271911146401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2793610404952847940764267 4190415607429271911146401)
        ·
          refine ⟨3142811705571953933359801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4190415607429271911146401 3142811705571953933359801)
          ·
            refine ⟨2357108779178965450019851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3142811705571953933359801 2357108779178965450019851)
            ·
              refine ⟨3535663168768448175029777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357108779178965450019851 3535663168768448175029777)
              ·
                refine ⟨2651747376576336131272333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535663168768448175029777 2651747376576336131272333)
                ·
                  refine ⟨994405266216126049227125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2651747376576336131272333 994405266216126049227125)
                  ·
                    refine ⟨93225493707761817115043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 994405266216126049227125 93225493707761817115043)
                    ·
                      rfl

theorem cell22_272334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_272334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272334 prefixEnd_272334 := by exact prefixLift 272334
  have htrace : WordTrace (prefixWord ++ tailWord_272334) baseStart_272334 baseEnd_272334 := by
    simpa [prefixWord, tailWord_272334, baseEnd_272334] using wordTrace_append hprefix tailTrace_272334
  have hstable : (prefixWord ++ tailWord_272334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272334).length < 2 ^ (prefixWord ++ tailWord_272334).sum := by decide
  have hdescent : baseEnd_272334 < baseStart_272334 := by decide
  rcases family_descends (prefixWord ++ tailWord_272334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272351 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 1, 5]
def baseStart_272351 : Nat := 118140960795 + 272351 * 2 ^ 59
def prefixEnd_272351 : Nat := 4983230072969 + 3 ^ 40 * 272351 * 2
def baseEnd_272351 : Nat := 93231313155179439439991

theorem tailTrace_272351 : CollatzResearch.WordTrace tailWord_272351 prefixEnd_272351 93231313155179439439991 := by
  unfold tailWord_272351
  simp only [CollatzResearch.WordTrace]
  refine ⟨9933457036326315692752907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6622304690884210461835271 9933457036326315692752907)
  ·
    refine ⟨14900185554489473539129361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9933457036326315692752907 14900185554489473539129361)
    ·
      refine ⟨11175139165867105154347021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14900185554489473539129361 11175139165867105154347021)
      ·
        refine ⟨4190677187200164432880133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11175139165867105154347021 4190677187200164432880133)
        ·
          refine ⟨785751972600030831165025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4190677187200164432880133 785751972600030831165025)
          ·
            refine ⟨589313979450023123373769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 785751972600030831165025 589313979450023123373769)
            ·
              refine ⟨441985484587517342530327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 589313979450023123373769 441985484587517342530327)
              ·
                refine ⟨662978226881276013795491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441985484587517342530327 662978226881276013795491)
                ·
                  refine ⟨994467340321914020693237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662978226881276013795491 994467340321914020693237)
                  ·
                    refine ⟨93231313155179439439991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 994467340321914020693237 93231313155179439439991)
                    ·
                      rfl

theorem cell22_272351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_272351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272351 prefixEnd_272351 := by exact prefixLift 272351
  have htrace : WordTrace (prefixWord ++ tailWord_272351) baseStart_272351 baseEnd_272351 := by
    simpa [prefixWord, tailWord_272351, baseEnd_272351] using wordTrace_append hprefix tailTrace_272351
  have hstable : (prefixWord ++ tailWord_272351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272351).length < 2 ^ (prefixWord ++ tailWord_272351).sum := by decide
  have hdescent : baseEnd_272351 < baseStart_272351 := by decide
  rcases family_descends (prefixWord ++ tailWord_272351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272366 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_272366 : Nat := 118140960795 + 272366 * 2 ^ 59
def prefixEnd_272366 : Nat := 4983230072969 + 3 ^ 40 * 272366 * 2
def baseEnd_272366 : Nat := 93236447961724400314945

theorem tailTrace_272366 : CollatzResearch.WordTrace tailWord_272366 prefixEnd_272366 93236447961724400314945 := by
  unfold tailWord_272366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241750516408996656818619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6622669420847982169699301 1241750516408996656818619)
  ·
    refine ⟨1862625774613494985227929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1241750516408996656818619 1862625774613494985227929)
    ·
      refine ⟨1396969330960121238920947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1862625774613494985227929 1396969330960121238920947)
      ·
        refine ⟨2095453996440181858381421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396969330960121238920947 2095453996440181858381421)
        ·
          refine ⟨785795248665068196893033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2095453996440181858381421 785795248665068196893033)
          ·
            refine ⟨589346436498801147669775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 785795248665068196893033 589346436498801147669775)
            ·
              refine ⟨884019654748201721504663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589346436498801147669775 884019654748201721504663)
              ·
                refine ⟨1326029482122302582256995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884019654748201721504663 1326029482122302582256995)
                ·
                  refine ⟨1989044223183453873385493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326029482122302582256995 1989044223183453873385493)
                  ·
                    refine ⟨93236447961724400314945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1989044223183453873385493 93236447961724400314945)
                    ·
                      rfl

theorem cell22_272366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_272366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272366 prefixEnd_272366 := by exact prefixLift 272366
  have htrace : WordTrace (prefixWord ++ tailWord_272366) baseStart_272366 baseEnd_272366 := by
    simpa [prefixWord, tailWord_272366, baseEnd_272366] using wordTrace_append hprefix tailTrace_272366
  have hstable : (prefixWord ++ tailWord_272366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272366).length < 2 ^ (prefixWord ++ tailWord_272366).sum := by decide
  have hdescent : baseEnd_272366 < baseStart_272366 := by decide
  rcases family_descends (prefixWord ++ tailWord_272366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272413 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_272413 : Nat := 118140960795 + 272413 * 2 ^ 59
def prefixEnd_272413 : Nat := 4983230072969 + 3 ^ 40 * 272413 * 2
def baseEnd_272413 : Nat := 93252537022231944389801

theorem tailTrace_272413 : CollatzResearch.WordTrace tailWord_272413 prefixEnd_272413 93252537022231944389801 := by
  unfold tailWord_272413
  simp only [CollatzResearch.WordTrace]
  refine ⟨9935718362101700281509893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6623812241401133521006595 9935718362101700281509893)
  ·
    refine ⟨1862947192894068802783105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9935718362101700281509893 1862947192894068802783105)
    ·
      refine ⟨1397210394670551602087329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1862947192894068802783105 1397210394670551602087329)
      ·
        refine ⟨1047907796002913701565497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1397210394670551602087329 1047907796002913701565497)
        ·
          refine ⟨785930847002185276174123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1047907796002913701565497 785930847002185276174123)
          ·
            refine ⟨1178896270503277914261185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785930847002185276174123 1178896270503277914261185)
            ·
              refine ⟨884172202877458435695889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1178896270503277914261185 884172202877458435695889)
              ·
                refine ⟨663129152158093826771917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884172202877458435695889 663129152158093826771917)
                ·
                  refine ⟨248673432059285185039469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663129152158093826771917 248673432059285185039469)
                  ·
                    refine ⟨93252537022231944389801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 248673432059285185039469 93252537022231944389801)
                    ·
                      rfl

theorem cell22_272413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_272413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272413 prefixEnd_272413 := by exact prefixLift 272413
  have htrace : WordTrace (prefixWord ++ tailWord_272413) baseStart_272413 baseEnd_272413 := by
    simpa [prefixWord, tailWord_272413, baseEnd_272413] using wordTrace_append hprefix tailTrace_272413
  have hstable : (prefixWord ++ tailWord_272413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272413).length < 2 ^ (prefixWord ++ tailWord_272413).sum := by decide
  have hdescent : baseEnd_272413 < baseStart_272413 := by decide
  rcases family_descends (prefixWord ++ tailWord_272413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272426 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_272426 : Nat := 118140960795 + 272426 * 2 ^ 59
def prefixEnd_272426 : Nat := 4983230072969 + 3 ^ 40 * 272426 * 2
def baseEnd_272426 : Nat := 31085662395968081271587

theorem tailTrace_272426 : CollatzResearch.WordTrace tailWord_272426 prefixEnd_272426 31085662395968081271587 := by
  unfold tailWord_272426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484048127763650875433283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6624128340703069001155421 2484048127763650875433283)
  ·
    refine ⟨3726072191645476313149925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2484048127763650875433283 3726072191645476313149925)
    ·
      refine ⟨698638535933526808715611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3726072191645476313149925 698638535933526808715611)
      ·
        refine ⟨1047957803900290213073417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 698638535933526808715611 1047957803900290213073417)
        ·
          refine ⟨785968352925217659805063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1047957803900290213073417 785968352925217659805063)
          ·
            refine ⟨1178952529387826489707595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785968352925217659805063 1178952529387826489707595)
            ·
              refine ⟨1768428794081739734561393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178952529387826489707595 1768428794081739734561393)
              ·
                refine ⟨1326321595561304800921045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1768428794081739734561393 1326321595561304800921045)
                ·
                  refine ⟨31085662395968081271587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1326321595561304800921045 31085662395968081271587)
                  ·
                    rfl

theorem cell22_272426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_272426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272426 prefixEnd_272426 := by exact prefixLift 272426
  have htrace : WordTrace (prefixWord ++ tailWord_272426) baseStart_272426 baseEnd_272426 := by
    simpa [prefixWord, tailWord_272426, baseEnd_272426] using wordTrace_append hprefix tailTrace_272426
  have hstable : (prefixWord ++ tailWord_272426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272426).length < 2 ^ (prefixWord ++ tailWord_272426).sum := by decide
  have hdescent : baseEnd_272426 < baseStart_272426 := by decide
  rcases family_descends (prefixWord ++ tailWord_272426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272503 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 2, 3]
def baseStart_272503 : Nat := 118140960795 + 272503 * 2 ^ 59
def prefixEnd_272503 : Nat := 4983230072969 + 3 ^ 40 * 272503 * 2
def baseEnd_272503 : Nat := 93283345861501709639525

theorem tailTrace_272503 : CollatzResearch.WordTrace tailWord_272503 prefixEnd_272503 93283345861501709639525 := by
  unfold tailWord_272503
  simp only [CollatzResearch.WordTrace]
  refine ⟨9939000931775645652286163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6626000621183763768190775 9939000931775645652286163)
  ·
    refine ⟨14908501397663468478429245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9939000931775645652286163 14908501397663468478429245)
    ·
      refine ⟨5590688024123800679410967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14908501397663468478429245 5590688024123800679410967)
      ·
        refine ⟨8386032036185701019116451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5590688024123800679410967 8386032036185701019116451)
        ·
          refine ⟨12579048054278551528674677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8386032036185701019116451 12579048054278551528674677)
          ·
            refine ⟨1179285755088614205813251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12579048054278551528674677 1179285755088614205813251)
            ·
              refine ⟨1768928632632921308719877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179285755088614205813251 1768928632632921308719877)
              ·
                refine ⟨331674118618672745384977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1768928632632921308719877 331674118618672745384977)
                ·
                  refine ⟨248755588964004559038733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331674118618672745384977 248755588964004559038733)
                  ·
                    refine ⟨93283345861501709639525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 248755588964004559038733 93283345861501709639525)
                    ·
                      rfl

theorem cell22_272503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_272503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272503 prefixEnd_272503 := by exact prefixLift 272503
  have htrace : WordTrace (prefixWord ++ tailWord_272503) baseStart_272503 baseEnd_272503 := by
    simpa [prefixWord, tailWord_272503, baseEnd_272503] using wordTrace_append hprefix tailTrace_272503
  have hstable : (prefixWord ++ tailWord_272503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272503).length < 2 ^ (prefixWord ++ tailWord_272503).sum := by decide
  have hdescent : baseEnd_272503 < baseStart_272503 := by decide
  rcases family_descends (prefixWord ++ tailWord_272503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272505 : List Nat := [1, 2, 1, 3, 4, 1, 4, 2, 4]
def baseStart_272505 : Nat := 118140960795 + 272505 * 2 ^ 59
def prefixEnd_272505 : Nat := 4983230072969 + 3 ^ 40 * 272505 * 2
def baseEnd_272505 : Nat := 31094676834124790363173

theorem tailTrace_272505 : CollatzResearch.WordTrace tailWord_272505 prefixEnd_272505 31094676834124790363173 := by
  unfold tailWord_272505
  simp only [CollatzResearch.WordTrace]
  refine ⟨9939073877768399993858969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6626049251845599995905979 9939073877768399993858969)
  ·
    refine ⟨7454305408326299995394227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9939073877768399993858969 7454305408326299995394227)
    ·
      refine ⟨11181458112489449993091341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7454305408326299995394227 11181458112489449993091341)
      ·
        refine ⟨4193046792183543747409253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11181458112489449993091341 4193046792183543747409253)
        ·
          refine ⟨786196273534414452639235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4193046792183543747409253 786196273534414452639235)
          ·
            refine ⟨1179294410301621678958853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786196273534414452639235 1179294410301621678958853)
            ·
              refine ⟨221117701931554064804785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1179294410301621678958853 221117701931554064804785)
              ·
                refine ⟨165838276448665548603589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221117701931554064804785 165838276448665548603589)
                ·
                  refine ⟨31094676834124790363173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165838276448665548603589 31094676834124790363173)
                  ·
                    rfl

theorem cell22_272505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 4].length) (baseStart_272505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272505 prefixEnd_272505 := by exact prefixLift 272505
  have htrace : WordTrace (prefixWord ++ tailWord_272505) baseStart_272505 baseEnd_272505 := by
    simpa [prefixWord, tailWord_272505, baseEnd_272505] using wordTrace_append hprefix tailTrace_272505
  have hstable : (prefixWord ++ tailWord_272505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272505).length < 2 ^ (prefixWord ++ tailWord_272505).sum := by decide
  have hdescent : baseEnd_272505 < baseStart_272505 := by decide
  rcases family_descends (prefixWord ++ tailWord_272505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272520 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 2, 3]
def baseStart_272520 : Nat := 118140960795 + 272520 * 2 ^ 59
def prefixEnd_272520 : Nat := 4983230072969 + 3 ^ 40 * 272520 * 2
def baseEnd_272520 : Nat := 93289165308919331964473

theorem tailTrace_272520 : CollatzResearch.WordTrace tailWord_272520 prefixEnd_272520 93289165308919331964473 := by
  unfold tailWord_272520
  simp only [CollatzResearch.WordTrace]
  refine ⟨4969810486357028777827507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6626413981809371703770009 4969810486357028777827507)
  ·
    refine ⟨7454715729535543166741261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4969810486357028777827507 7454715729535543166741261)
    ·
      refine ⟨2795518398575828687527973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7454715729535543166741261 2795518398575828687527973)
      ·
        refine ⟨524159699732967878911495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2795518398575828687527973 524159699732967878911495)
        ·
          refine ⟨786239549599451818367243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524159699732967878911495 786239549599451818367243)
          ·
            refine ⟨1179359324399177727550865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786239549599451818367243 1179359324399177727550865)
            ·
              refine ⟨884519493299383295663149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179359324399177727550865 884519493299383295663149)
              ·
                refine ⟨331694809987268735873681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 884519493299383295663149 331694809987268735873681)
                ·
                  refine ⟨248771107490451551905261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331694809987268735873681 248771107490451551905261)
                  ·
                    refine ⟨93289165308919331964473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 248771107490451551905261 93289165308919331964473)
                    ·
                      rfl

theorem cell22_272520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_272520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272520 prefixEnd_272520 := by exact prefixLift 272520
  have htrace : WordTrace (prefixWord ++ tailWord_272520) baseStart_272520 baseEnd_272520 := by
    simpa [prefixWord, tailWord_272520, baseEnd_272520] using wordTrace_append hprefix tailTrace_272520
  have hstable : (prefixWord ++ tailWord_272520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272520).length < 2 ^ (prefixWord ++ tailWord_272520).sum := by decide
  have hdescent : baseEnd_272520 < baseStart_272520 := by decide
  rcases family_descends (prefixWord ++ tailWord_272520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272535 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 2, 4]
def baseStart_272535 : Nat := 118140960795 + 272535 * 2 ^ 59
def prefixEnd_272535 : Nat := 4983230072969 + 3 ^ 40 * 272535 * 2
def baseEnd_272535 : Nat := 93294300115464292839427

theorem tailTrace_272535 : CollatzResearch.WordTrace tailWord_272535 prefixEnd_272535 93294300115464292839427 := by
  unfold tailWord_272535
  simp only [CollatzResearch.WordTrace]
  refine ⟨9940168067659715117451059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6626778711773143411634039 9940168067659715117451059)
  ·
    refine ⟨14910252101489572676176589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9940168067659715117451059 14910252101489572676176589)
    ·
      refine ⟨5591344538058589753566221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14910252101489572676176589 5591344538058589753566221)
      ·
        refine ⟨2096754201771971157587333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5591344538058589753566221 2096754201771971157587333)
        ·
          refine ⟨393141412832244592047625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2096754201771971157587333 393141412832244592047625)
          ·
            refine ⟨294856059624183444035719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393141412832244592047625 294856059624183444035719)
            ·
              refine ⟨442284089436275166053579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294856059624183444035719 442284089436275166053579)
              ·
                refine ⟨663426134154412749080369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442284089436275166053579 663426134154412749080369)
                ·
                  refine ⟨497569600615809561810277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 663426134154412749080369 497569600615809561810277)
                  ·
                    refine ⟨93294300115464292839427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 497569600615809561810277 93294300115464292839427)
                    ·
                      rfl

theorem cell22_272535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_272535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272535 prefixEnd_272535 := by exact prefixLift 272535
  have htrace : WordTrace (prefixWord ++ tailWord_272535) baseStart_272535 baseEnd_272535 := by
    simpa [prefixWord, tailWord_272535, baseEnd_272535] using wordTrace_append hprefix tailTrace_272535
  have hstable : (prefixWord ++ tailWord_272535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272535).length < 2 ^ (prefixWord ++ tailWord_272535).sum := by decide
  have hdescent : baseEnd_272535 < baseStart_272535 := by decide
  rcases family_descends (prefixWord ++ tailWord_272535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272554 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 2, 3]
def baseStart_272554 : Nat := 118140960795 + 272554 * 2 ^ 59
def prefixEnd_272554 : Nat := 4983230072969 + 3 ^ 40 * 272554 * 2
def baseEnd_272554 : Nat := 93300804203754576614369

theorem tailTrace_272554 : CollatzResearch.WordTrace tailWord_272554 prefixEnd_272554 93300804203754576614369 := by
  unfold tailWord_272554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2485215263647720340598179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6627240703060587574928477 2485215263647720340598179)
  ·
    refine ⟨3727822895471580510897269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2485215263647720340598179 3727822895471580510897269)
    ·
      refine ⟨349483396450460672896619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3727822895471580510897269 349483396450460672896619)
      ·
        refine ⟨524225094675691009344929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349483396450460672896619 524225094675691009344929)
        ·
          refine ⟨393168821006768257008697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524225094675691009344929 393168821006768257008697)
          ·
            refine ⟨294876615755076192756523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393168821006768257008697 294876615755076192756523)
            ·
              refine ⟨442314923632614289134785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294876615755076192756523 442314923632614289134785)
              ·
                refine ⟨331736192724460716851089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442314923632614289134785 331736192724460716851089)
                ·
                  refine ⟨248802144543345537638317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331736192724460716851089 248802144543345537638317)
                  ·
                    refine ⟨93300804203754576614369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 248802144543345537638317 93300804203754576614369)
                    ·
                      rfl

theorem cell22_272554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_272554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272554 prefixEnd_272554 := by exact prefixLift 272554
  have htrace : WordTrace (prefixWord ++ tailWord_272554) baseStart_272554 baseEnd_272554 := by
    simpa [prefixWord, tailWord_272554, baseEnd_272554] using wordTrace_append hprefix tailTrace_272554
  have hstable : (prefixWord ++ tailWord_272554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272554).length < 2 ^ (prefixWord ++ tailWord_272554).sum := by decide
  have hdescent : baseEnd_272554 < baseStart_272554 := by decide
  rcases family_descends (prefixWord ++ tailWord_272554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272608 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 1, 4]
def baseStart_272608 : Nat := 118140960795 + 272608 * 2 ^ 59
def prefixEnd_272608 : Nat := 4983230072969 + 3 ^ 40 * 272608 * 2
def baseEnd_272608 : Nat := 93319289507316435764203

theorem tailTrace_272608 : CollatzResearch.WordTrace tailWord_272608 prefixEnd_272608 93319289507316435764203 := by
  unfold tailWord_272608
  simp only [CollatzResearch.WordTrace]
  refine ⟨4971415298197624292429239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6628553730930165723238985 4971415298197624292429239)
  ·
    refine ⟨7457122947296436438643859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4971415298197624292429239 7457122947296436438643859)
    ·
      refine ⟨11185684420944654657965789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7457122947296436438643859 11185684420944654657965789)
      ·
        refine ⟨4194631657854245496737171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11185684420944654657965789 4194631657854245496737171)
        ·
          refine ⟨6291947486781368245105757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194631657854245496737171 6291947486781368245105757)
          ·
            refine ⟨2359480307543013091914659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6291947486781368245105757 2359480307543013091914659)
            ·
              refine ⟨3539220461314519637871989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359480307543013091914659 3539220461314519637871989)
              ·
                refine ⟨331801918248236216050499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3539220461314519637871989 331801918248236216050499)
                ·
                  refine ⟨497702877372354324075749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331801918248236216050499 497702877372354324075749)
                  ·
                    refine ⟨93319289507316435764203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 497702877372354324075749 93319289507316435764203)
                    ·
                      rfl

theorem cell22_272608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_272608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272608 prefixEnd_272608 := by exact prefixLift 272608
  have htrace : WordTrace (prefixWord ++ tailWord_272608) baseStart_272608 baseEnd_272608 := by
    simpa [prefixWord, tailWord_272608, baseEnd_272608] using wordTrace_append hprefix tailTrace_272608
  have hstable : (prefixWord ++ tailWord_272608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272608).length < 2 ^ (prefixWord ++ tailWord_272608).sum := by decide
  have hdescent : baseEnd_272608 < baseStart_272608 := by decide
  rcases family_descends (prefixWord ++ tailWord_272608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272623 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 6]
def baseStart_272623 : Nat := 118140960795 + 272623 * 2 ^ 59
def prefixEnd_272623 : Nat := 4983230072969 + 3 ^ 40 * 272623 * 2
def baseEnd_272623 : Nat := 31108141437953798879719

theorem tailTrace_272623 : CollatzResearch.WordTrace tailWord_272623 prefixEnd_272623 31108141437953798879719 := by
  unfold tailWord_272623
  simp only [CollatzResearch.WordTrace]
  refine ⟨9943377691340906146654523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6628918460893937431103015 9943377691340906146654523)
  ·
    refine ⟨14915066537011359219981785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9943377691340906146654523 14915066537011359219981785)
    ·
      refine ⟨11186299902758519414986339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14915066537011359219981785 11186299902758519414986339)
      ·
        refine ⟨16779449854137779122479509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11186299902758519414986339 16779449854137779122479509)
        ·
          refine ⟨786536711912708396366227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16779449854137779122479509 786536711912708396366227)
          ·
            refine ⟨1179805067869062594549341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786536711912708396366227 1179805067869062594549341)
            ·
              refine ⟨442426900450898472956003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1179805067869062594549341 442426900450898472956003)
              ·
                refine ⟨663640350676347709434005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442426900450898472956003 663640350676347709434005)
                ·
                  refine ⟨31108141437953798879719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 663640350676347709434005 31108141437953798879719)
                  ·
                    rfl

theorem cell22_272623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 6].length) (baseStart_272623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272623 prefixEnd_272623 := by exact prefixLift 272623
  have htrace : WordTrace (prefixWord ++ tailWord_272623) baseStart_272623 baseEnd_272623 := by
    simpa [prefixWord, tailWord_272623, baseEnd_272623] using wordTrace_append hprefix tailTrace_272623
  have hstable : (prefixWord ++ tailWord_272623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272623).length < 2 ^ (prefixWord ++ tailWord_272623).sum := by decide
  have hdescent : baseEnd_272623 < baseStart_272623 := by decide
  rcases family_descends (prefixWord ++ tailWord_272623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272642 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_272642 : Nat := 118140960795 + 272642 * 2 ^ 59
def prefixEnd_272642 : Nat := 4983230072969 + 3 ^ 40 * 272642 * 2
def baseEnd_272642 : Nat := 93330928402151680414099

theorem tailTrace_272642 : CollatzResearch.WordTrace tailWord_272642 prefixEnd_272642 93330928402151680414099 := by
  unfold tailWord_272642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486017669568018097899045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6629380452181381594397453 2486017669568018097899045)
  ·
    refine ⟨466128313044003393356071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2486017669568018097899045 466128313044003393356071)
    ·
      refine ⟨699192469566005090034107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466128313044003393356071 699192469566005090034107)
      ·
        refine ⟨1048788704349007635051161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699192469566005090034107 1048788704349007635051161)
        ·
          refine ⟨786591528261755726288371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1048788704349007635051161 786591528261755726288371)
          ·
            refine ⟨1179887292392633589432557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786591528261755726288371 1179887292392633589432557)
            ·
              refine ⟨442457734647237596037209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1179887292392633589432557 442457734647237596037209)
              ·
                refine ⟨331843300985428197027907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442457734647237596037209 331843300985428197027907)
                ·
                  refine ⟨497764951478142295541861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331843300985428197027907 497764951478142295541861)
                  ·
                    refine ⟨93330928402151680414099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 497764951478142295541861 93330928402151680414099)
                    ·
                      rfl

theorem cell22_272642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_272642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272642 prefixEnd_272642 := by exact prefixLift 272642
  have htrace : WordTrace (prefixWord ++ tailWord_272642) baseStart_272642 baseEnd_272642 := by
    simpa [prefixWord, tailWord_272642, baseEnd_272642] using wordTrace_append hprefix tailTrace_272642
  have hstable : (prefixWord ++ tailWord_272642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272642).length < 2 ^ (prefixWord ++ tailWord_272642).sum := by decide
  have hdescent : baseEnd_272642 < baseStart_272642 := by decide
  rcases family_descends (prefixWord ++ tailWord_272642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272651 : List Nat := [1, 1, 1, 1, 5, 2, 1, 10]
def baseStart_272651 : Nat := 118140960795 + 272651 * 2 ^ 59
def prefixEnd_272651 : Nat := 4983230072969 + 3 ^ 40 * 272651 * 2
def baseEnd_272651 : Nat := 10370445476230961882119

theorem tailTrace_272651 : CollatzResearch.WordTrace tailWord_272651 prefixEnd_272651 10370445476230961882119 := by
  unfold tailWord_272651
  simp only [CollatzResearch.WordTrace]
  refine ⟨9944398935239466928673807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6629599290159644619115871 9944398935239466928673807)
  ·
    refine ⟨14916598402859200393010711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9944398935239466928673807 14916598402859200393010711)
    ·
      refine ⟨22374897604288800589516067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14916598402859200393010711 22374897604288800589516067)
      ·
        refine ⟨33562346406433200884274101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22374897604288800589516067 33562346406433200884274101)
        ·
          refine ⟨3146469975603112582900697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33562346406433200884274101 3146469975603112582900697)
          ·
            refine ⟨2359852481702334437175523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3146469975603112582900697 2359852481702334437175523)
            ·
              refine ⟨3539778722553501655763285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359852481702334437175523 3539778722553501655763285)
              ·
                refine ⟨10370445476230961882119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3539778722553501655763285 10370445476230961882119)
                ·
                  rfl

theorem cell22_272651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 10].length) (baseStart_272651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272651 prefixEnd_272651 := by exact prefixLift 272651
  have htrace : WordTrace (prefixWord ++ tailWord_272651) baseStart_272651 baseEnd_272651 := by
    simpa [prefixWord, tailWord_272651, baseEnd_272651] using wordTrace_append hprefix tailTrace_272651
  have hstable : (prefixWord ++ tailWord_272651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272651).length < 2 ^ (prefixWord ++ tailWord_272651).sum := by decide
  have hdescent : baseEnd_272651 < baseStart_272651 := by decide
  rcases family_descends (prefixWord ++ tailWord_272651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272672 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 2, 3]
def baseStart_272672 : Nat := 118140960795 + 272672 * 2 ^ 59
def prefixEnd_272672 : Nat := 4983230072969 + 3 ^ 40 * 272672 * 2
def baseEnd_272672 : Nat := 93341198015241602164007

theorem tailTrace_272672 : CollatzResearch.WordTrace tailWord_272672 prefixEnd_272672 93341198015241602164007 := by
  unfold tailWord_272672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4972582434081693757594135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6630109912108925010125513 4972582434081693757594135)
  ·
    refine ⟨7458873651122540636391203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4972582434081693757594135 7458873651122540636391203)
    ·
      refine ⟨11188310476683810954586805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7458873651122540636391203 11188310476683810954586805)
      ·
        refine ⟨1048904107189107276992513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11188310476683810954586805 1048904107189107276992513)
        ·
          refine ⟨786678080391830457744385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1048904107189107276992513 786678080391830457744385)
          ·
            refine ⟨590008560293872843308289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786678080391830457744385 590008560293872843308289)
            ·
              refine ⟨442506420220404632481217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590008560293872843308289 442506420220404632481217)
              ·
                refine ⟨331879815165303474360913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442506420220404632481217 331879815165303474360913)
                ·
                  refine ⟨248909861373977605770685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331879815165303474360913 248909861373977605770685)
                  ·
                    refine ⟨93341198015241602164007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 248909861373977605770685 93341198015241602164007)
                    ·
                      rfl

theorem cell22_272672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2, 3].length) (baseStart_272672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272672 prefixEnd_272672 := by exact prefixLift 272672
  have htrace : WordTrace (prefixWord ++ tailWord_272672) baseStart_272672 baseEnd_272672 := by
    simpa [prefixWord, tailWord_272672, baseEnd_272672] using wordTrace_append hprefix tailTrace_272672
  have hstable : (prefixWord ++ tailWord_272672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272672).length < 2 ^ (prefixWord ++ tailWord_272672).sum := by decide
  have hdescent : baseEnd_272672 < baseStart_272672 := by decide
  rcases family_descends (prefixWord ++ tailWord_272672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272674 : List Nat := [3, 3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_272674 : Nat := 118140960795 + 272674 * 2 ^ 59
def prefixEnd_272674 : Nat := 4983230072969 + 3 ^ 40 * 272674 * 2
def baseEnd_272674 : Nat := 31113960885371421204667

theorem tailTrace_272674 : CollatzResearch.WordTrace tailWord_272674 prefixEnd_272674 31113960885371421204667 := by
  unfold tailWord_272674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486309453539035464190269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6630158542770761237840717 2486309453539035464190269)
  ·
    refine ⟨932366045077138299071351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2486309453539035464190269 932366045077138299071351)
    ·
      refine ⟨1398549067615707448607027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 932366045077138299071351 1398549067615707448607027)
      ·
        refine ⟨2097823601423561172910541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398549067615707448607027 2097823601423561172910541)
        ·
          refine ⟨786683850533835439841453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2097823601423561172910541 786683850533835439841453)
          ·
            refine ⟨295006443950188289940545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 786683850533835439841453 295006443950188289940545)
            ·
              refine ⟨221254832962641217455409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295006443950188289940545 221254832962641217455409)
              ·
                refine ⟨165941124721980913091557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221254832962641217455409 165941124721980913091557)
                ·
                  refine ⟨31113960885371421204667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165941124721980913091557 31113960885371421204667)
                  ·
                    rfl

theorem cell22_272674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_272674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272674 prefixEnd_272674 := by exact prefixLift 272674
  have htrace : WordTrace (prefixWord ++ tailWord_272674) baseStart_272674 baseEnd_272674 := by
    simpa [prefixWord, tailWord_272674, baseEnd_272674] using wordTrace_append hprefix tailTrace_272674
  have hstable : (prefixWord ++ tailWord_272674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272674).length < 2 ^ (prefixWord ++ tailWord_272674).sum := by decide
  have hdescent : baseEnd_272674 < baseStart_272674 := by decide
  rcases family_descends (prefixWord ++ tailWord_272674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272700 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 3, 3]
def baseStart_272700 : Nat := 118140960795 + 272700 * 2 ^ 59
def prefixEnd_272700 : Nat := 4983230072969 + 3 ^ 40 * 272700 * 2
def baseEnd_272700 : Nat := 93350782987458862463921

theorem tailTrace_272700 : CollatzResearch.WordTrace tailWord_272700 prefixEnd_272700 93350782987458862463921 := by
  unfold tailWord_272700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4973093056030974148603777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6630790741374632198138369 4973093056030974148603777)
  ·
    refine ⟨3729819792023230611452833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4973093056030974148603777 3729819792023230611452833)
    ·
      refine ⟨2797364844017422958589625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3729819792023230611452833 2797364844017422958589625)
      ·
        refine ⟨2098023633013067218942219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2797364844017422958589625 2098023633013067218942219)
        ·
          refine ⟨3147035449519600828413329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098023633013067218942219 3147035449519600828413329)
          ·
            refine ⟨2360276587139700621309997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3147035449519600828413329 2360276587139700621309997)
            ·
              refine ⟨885103720177387732991249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2360276587139700621309997 885103720177387732991249)
              ·
                refine ⟨663827790133040799743437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885103720177387732991249 663827790133040799743437)
                ·
                  refine ⟨248935421299890299903789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 663827790133040799743437 248935421299890299903789)
                  ·
                    refine ⟨93350782987458862463921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 248935421299890299903789 93350782987458862463921)
                    ·
                      rfl

theorem cell22_272700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_272700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272700 prefixEnd_272700 := by exact prefixLift 272700
  have htrace : WordTrace (prefixWord ++ tailWord_272700) baseStart_272700 baseEnd_272700 := by
    simpa [prefixWord, tailWord_272700, baseEnd_272700] using wordTrace_append hprefix tailTrace_272700
  have hstable : (prefixWord ++ tailWord_272700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272700).length < 2 ^ (prefixWord ++ tailWord_272700).sum := by decide
  have hdescent : baseEnd_272700 < baseStart_272700 := by decide
  rcases family_descends (prefixWord ++ tailWord_272700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272773 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_272773 : Nat := 118140960795 + 272773 * 2 ^ 59
def prefixEnd_272773 : Nat := 4983230072969 + 3 ^ 40 * 272773 * 2
def baseEnd_272773 : Nat := 93375772379311005388697

theorem tailTrace_272773 : CollatzResearch.WordTrace tailWord_272773 prefixEnd_272773 93375772379311005388697 := by
  unfold tailWord_272773
  simp only [CollatzResearch.WordTrace]
  refine ⟨9948848640797481764614973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6632565760531654509743315 9948848640797481764614973)
  ·
    refine ⟨3730818240299055661730615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9948848640797481764614973 3730818240299055661730615)
    ·
      refine ⟨5596227360448583492595923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3730818240299055661730615 5596227360448583492595923)
      ·
        refine ⟨8394341040672875238893885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5596227360448583492595923 8394341040672875238893885)
        ·
          refine ⟨3147877890252328214585207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8394341040672875238893885 3147877890252328214585207)
          ·
            refine ⟨4721816835378492321877811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3147877890252328214585207 4721816835378492321877811)
            ·
              refine ⟨7082725253067738482816717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4721816835378492321877811 7082725253067738482816717)
              ·
                refine ⟨2656021969900401931056269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7082725253067738482816717 2656021969900401931056269)
                ·
                  refine ⟨996008238712650724146101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2656021969900401931056269 996008238712650724146101)
                  ·
                    refine ⟨93375772379311005388697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 996008238712650724146101 93375772379311005388697)
                    ·
                      rfl

theorem cell22_272773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_272773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272773 prefixEnd_272773 := by exact prefixLift 272773
  have htrace : WordTrace (prefixWord ++ tailWord_272773) baseStart_272773 baseEnd_272773 := by
    simpa [prefixWord, tailWord_272773, baseEnd_272773] using wordTrace_append hprefix tailTrace_272773
  have hstable : (prefixWord ++ tailWord_272773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272773).length < 2 ^ (prefixWord ++ tailWord_272773).sum := by decide
  have hdescent : baseEnd_272773 < baseStart_272773 := by decide
  rcases family_descends (prefixWord ++ tailWord_272773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272792 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 6]
def baseStart_272792 : Nat := 118140960795 + 272792 * 2 ^ 59
def prefixEnd_272792 : Nat := 4983230072969 + 3 ^ 40 * 272792 * 2
def baseEnd_272792 : Nat := 31127425489200429721213

theorem tailTrace_272792 : CollatzResearch.WordTrace tailWord_272792 prefixEnd_272792 31127425489200429721213 := by
  unfold tailWord_272792
  simp only [CollatzResearch.WordTrace]
  refine ⟨4974770813864324004778315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6633027751819098673037753 4974770813864324004778315)
  ·
    refine ⟨7462156220796486007167473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4974770813864324004778315 7462156220796486007167473)
    ·
      refine ⟨5596617165597364505375605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7462156220796486007167473 5596617165597364505375605)
      ·
        refine ⟨524682859274752922378963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5596617165597364505375605 524682859274752922378963)
        ·
          refine ⟨787024288912129383568445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524682859274752922378963 787024288912129383568445)
          ·
            refine ⟨295134108342048518838167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 787024288912129383568445 295134108342048518838167)
            ·
              refine ⟨442701162513072778257251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295134108342048518838167 442701162513072778257251)
              ·
                refine ⟨664051743769609167385877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442701162513072778257251 664051743769609167385877)
                ·
                  refine ⟨31127425489200429721213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 664051743769609167385877 31127425489200429721213)
                  ·
                    rfl

theorem cell22_272792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 6].length) (baseStart_272792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272792 prefixEnd_272792 := by exact prefixLift 272792
  have htrace : WordTrace (prefixWord ++ tailWord_272792) baseStart_272792 baseEnd_272792 := by
    simpa [prefixWord, tailWord_272792, baseEnd_272792] using wordTrace_append hprefix tailTrace_272792
  have hstable : (prefixWord ++ tailWord_272792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272792).length < 2 ^ (prefixWord ++ tailWord_272792).sum := by decide
  have hdescent : baseEnd_272792 < baseStart_272792 := by decide
  rcases family_descends (prefixWord ++ tailWord_272792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272803 : List Nat := [1, 1, 1, 4, 1, 4, 1, 9]
def baseStart_272803 : Nat := 118140960795 + 272803 * 2 ^ 59
def prefixEnd_272803 : Nat := 4983230072969 + 3 ^ 40 * 272803 * 2
def baseEnd_272803 : Nat := 10376226888044547459845

theorem tailTrace_272803 : CollatzResearch.WordTrace tailWord_272803 prefixEnd_272803 10376226888044547459845 := by
  unfold tailWord_272803
  simp only [CollatzResearch.WordTrace]
  refine ⟨9949942830688796888207063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6633295220459197925471375 9949942830688796888207063)
  ·
    refine ⟨14924914246033195332310595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9949942830688796888207063 14924914246033195332310595)
    ·
      refine ⟨22387371369049792998465893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14924914246033195332310595 22387371369049792998465893)
      ·
        refine ⟨4197632131696836187212355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22387371369049792998465893 4197632131696836187212355)
        ·
          refine ⟨6296448197545254280818533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4197632131696836187212355 6296448197545254280818533)
          ·
            refine ⟨1180584037039735177653475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6296448197545254280818533 1180584037039735177653475)
            ·
              refine ⟨1770876055559602766480213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180584037039735177653475 1770876055559602766480213)
              ·
                refine ⟨10376226888044547459845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1770876055559602766480213 10376226888044547459845)
                ·
                  rfl

theorem cell22_272803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 9].length) (baseStart_272803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272803 prefixEnd_272803 := by exact prefixLift 272803
  have htrace : WordTrace (prefixWord ++ tailWord_272803) baseStart_272803 baseEnd_272803 := by
    simpa [prefixWord, tailWord_272803, baseEnd_272803] using wordTrace_append hprefix tailTrace_272803
  have hstable : (prefixWord ++ tailWord_272803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272803).length < 2 ^ (prefixWord ++ tailWord_272803).sum := by decide
  have hdescent : baseEnd_272803 < baseStart_272803 := by decide
  rcases family_descends (prefixWord ++ tailWord_272803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272865 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 5]
def baseStart_272865 : Nat := 118140960795 + 272865 * 2 ^ 59
def prefixEnd_272865 : Nat := 4983230072969 + 3 ^ 40 * 272865 * 2
def baseEnd_272865 : Nat := 31135755286484477362805

theorem tailTrace_272865 : CollatzResearch.WordTrace tailWord_272865 prefixEnd_272865 31135755286484477362805 := by
  unfold tailWord_272865
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952204156464181476964049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6634802770976120984642699 9952204156464181476964049)
  ·
    refine ⟨7464153117348136107723037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9952204156464181476964049 7464153117348136107723037)
    ·
      refine ⟨2799057419005551040396139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7464153117348136107723037 2799057419005551040396139)
      ·
        refine ⟨4198586128508326560594209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2799057419005551040396139 4198586128508326560594209)
        ·
          refine ⟨3148939596381244920445657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4198586128508326560594209 3148939596381244920445657)
          ·
            refine ⟨2361704697285933690334243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3148939596381244920445657 2361704697285933690334243)
            ·
              refine ⟨3542557045928900535501365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361704697285933690334243 3542557045928900535501365)
              ·
                refine ⟨332114723055834425203253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3542557045928900535501365 332114723055834425203253)
                ·
                  refine ⟨31135755286484477362805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 332114723055834425203253 31135755286484477362805)
                  ·
                    rfl

theorem cell22_272865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_272865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272865 prefixEnd_272865 := by exact prefixLift 272865
  have htrace : WordTrace (prefixWord ++ tailWord_272865) baseStart_272865 baseEnd_272865 := by
    simpa [prefixWord, tailWord_272865, baseEnd_272865] using wordTrace_append hprefix tailTrace_272865
  have hstable : (prefixWord ++ tailWord_272865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272865).length < 2 ^ (prefixWord ++ tailWord_272865).sum := by decide
  have hdescent : baseEnd_272865 < baseStart_272865 := by decide
  rcases family_descends (prefixWord ++ tailWord_272865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272869 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 3, 3]
def baseStart_272869 : Nat := 118140960795 + 272869 * 2 ^ 59
def prefixEnd_272869 : Nat := 4983230072969 + 3 ^ 40 * 272869 * 2
def baseEnd_272869 : Nat := 93408635141198754988403

theorem tailTrace_272869 : CollatzResearch.WordTrace tailWord_272869 prefixEnd_272869 93408635141198754988403 := by
  unfold tailWord_272869
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952350048449690160109661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6634900032299793440073107 9952350048449690160109661)
  ·
    refine ⟨3732131268168633810041123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9952350048449690160109661 3732131268168633810041123)
    ·
      refine ⟨5598196902252950715061685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3732131268168633810041123 5598196902252950715061685)
      ·
        refine ⟨524830959586214129537033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5598196902252950715061685 524830959586214129537033)
        ·
          refine ⟨393623219689660597152775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524830959586214129537033 393623219689660597152775)
          ·
            refine ⟨590434829534490895729163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393623219689660597152775 590434829534490895729163)
            ·
              refine ⟨885652244301736343593745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590434829534490895729163 885652244301736343593745)
              ·
                refine ⟨664239183226302257695309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885652244301736343593745 664239183226302257695309)
                ·
                  refine ⟨249089693709863346635741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664239183226302257695309 249089693709863346635741)
                  ·
                    refine ⟨93408635141198754988403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 249089693709863346635741 93408635141198754988403)
                    ·
                      rfl

theorem cell22_272869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_272869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272869 prefixEnd_272869 := by exact prefixLift 272869
  have htrace : WordTrace (prefixWord ++ tailWord_272869) baseStart_272869 baseEnd_272869 := by
    simpa [prefixWord, tailWord_272869, baseEnd_272869] using wordTrace_append hprefix tailTrace_272869
  have hstable : (prefixWord ++ tailWord_272869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272869).length < 2 ^ (prefixWord ++ tailWord_272869).sum := by decide
  have hdescent : baseEnd_272869 < baseStart_272869 := by decide
  rcases family_descends (prefixWord ++ tailWord_272869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272886 : List Nat := [5, 1, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_272886 : Nat := 118140960795 + 272886 * 2 ^ 59
def prefixEnd_272886 : Nat := 4983230072969 + 3 ^ 40 * 272886 * 2
def baseEnd_272886 : Nat := 93414454588616377313351

theorem tailTrace_272886 : CollatzResearch.WordTrace tailWord_272886 prefixEnd_272886 93414454588616377313351 := by
  unfold tailWord_272886
  simp only [CollatzResearch.WordTrace]
  refine ⟨622060630586756378967407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6635313392925401375652341 622060630586756378967407)
  ·
    refine ⟨933090945880134568451111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 622060630586756378967407 933090945880134568451111)
    ·
      refine ⟨1399636418820201852676667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 933090945880134568451111 1399636418820201852676667)
      ·
        refine ⟨2099454628230302779015001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1399636418820201852676667 2099454628230302779015001)
        ·
          refine ⟨1574590971172727084261251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2099454628230302779015001 1574590971172727084261251)
          ·
            refine ⟨2361886456759090626391877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574590971172727084261251 2361886456759090626391877)
            ·
              refine ⟨442853710642329492448477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2361886456759090626391877 442853710642329492448477)
              ·
                refine ⟨166070141490873559668179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 442853710642329492448477 166070141490873559668179)
                ·
                  refine ⟨249105212236310339502269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166070141490873559668179 249105212236310339502269)
                  ·
                    refine ⟨93414454588616377313351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 249105212236310339502269 93414454588616377313351)
                    ·
                      rfl

theorem cell22_272886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_272886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272886 prefixEnd_272886 := by exact prefixLift 272886
  have htrace : WordTrace (prefixWord ++ tailWord_272886) baseStart_272886 baseEnd_272886 := by
    simpa [prefixWord, tailWord_272886, baseEnd_272886] using wordTrace_append hprefix tailTrace_272886
  have hstable : (prefixWord ++ tailWord_272886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272886).length < 2 ^ (prefixWord ++ tailWord_272886).sum := by decide
  have hdescent : baseEnd_272886 < baseStart_272886 := by decide
  rcases family_descends (prefixWord ++ tailWord_272886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272916 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 5]
def baseStart_272916 : Nat := 118140960795 + 272916 * 2 ^ 59
def prefixEnd_272916 : Nat := 4983230072969 + 3 ^ 40 * 272916 * 2
def baseEnd_272916 : Nat := 31141574733902099687753

theorem tailTrace_272916 : CollatzResearch.WordTrace tailWord_272916 prefixEnd_272916 31141574733902099687753 := by
  unfold tailWord_272916
  simp only [CollatzResearch.WordTrace]
  refine ⟨4977032139639708593535301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6636042852852944791380401 4977032139639708593535301)
  ·
    refine ⟨933193526182445361287869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4977032139639708593535301 933193526182445361287869)
    ·
      refine ⟨349947572318417010482951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 933193526182445361287869 349947572318417010482951)
      ·
        refine ⟨524921358477625515724427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349947572318417010482951 524921358477625515724427)
        ·
          refine ⟨787382037716438273586641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524921358477625515724427 787382037716438273586641)
          ·
            refine ⟨590536528287328705189981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787382037716438273586641 590536528287328705189981)
            ·
              refine ⟨221451198107748264446243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 590536528287328705189981 221451198107748264446243)
              ·
                refine ⟨332176797161622396669365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221451198107748264446243 332176797161622396669365)
                ·
                  refine ⟨31141574733902099687753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 332176797161622396669365 31141574733902099687753)
                  ·
                    rfl

theorem cell22_272916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_272916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272916 prefixEnd_272916 := by exact prefixLift 272916
  have htrace : WordTrace (prefixWord ++ tailWord_272916) baseStart_272916 baseEnd_272916 := by
    simpa [prefixWord, tailWord_272916, baseEnd_272916] using wordTrace_append hprefix tailTrace_272916
  have hstable : (prefixWord ++ tailWord_272916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272916).length < 2 ^ (prefixWord ++ tailWord_272916).sum := by decide
  have hdescent : baseEnd_272916 < baseStart_272916 := by decide
  rcases family_descends (prefixWord ++ tailWord_272916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272940 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_272940 : Nat := 118140960795 + 272940 * 2 ^ 59
def prefixEnd_272940 : Nat := 4983230072969 + 3 ^ 40 * 272940 * 2
def baseEnd_272940 : Nat := 93432939892178236463185

theorem tailTrace_272940 : CollatzResearch.WordTrace tailWord_272940 prefixEnd_272940 93432939892178236463185 := by
  unfold tailWord_272940
  simp only [CollatzResearch.WordTrace]
  refine ⟨4977469815596234642972137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6636626420794979523962849 4977469815596234642972137)
  ·
    refine ⟨3733102361697175982229103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4977469815596234642972137 3733102361697175982229103)
    ·
      refine ⟨5599653542545763973343655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3733102361697175982229103 5599653542545763973343655)
      ·
        refine ⟨8399480313818645960015483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5599653542545763973343655 8399480313818645960015483)
        ·
          refine ⟨12599220470727968940023225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8399480313818645960015483 12599220470727968940023225)
          ·
            refine ⟨9449415353045976705017419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12599220470727968940023225 9449415353045976705017419)
            ·
              refine ⟨14174123029568965057526129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9449415353045976705017419 14174123029568965057526129)
              ·
                refine ⟨10630592272176723793144597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14174123029568965057526129 10630592272176723793144597)
                ·
                  refine ⟨498309012758283927803653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10630592272176723793144597 498309012758283927803653)
                  ·
                    refine ⟨93432939892178236463185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 498309012758283927803653 93432939892178236463185)
                    ·
                      rfl

theorem cell22_272940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_272940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272940 prefixEnd_272940 := by exact prefixLift 272940
  have htrace : WordTrace (prefixWord ++ tailWord_272940) baseStart_272940 baseEnd_272940 := by
    simpa [prefixWord, tailWord_272940, baseEnd_272940] using wordTrace_append hprefix tailTrace_272940
  have hstable : (prefixWord ++ tailWord_272940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272940).length < 2 ^ (prefixWord ++ tailWord_272940).sum := by decide
  have hdescent : baseEnd_272940 < baseStart_272940 := by decide
  rcases family_descends (prefixWord ++ tailWord_272940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272957 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_272957 : Nat := 118140960795 + 272957 * 2 ^ 59
def prefixEnd_272957 : Nat := 4983230072969 + 3 ^ 40 * 272957 * 2
def baseEnd_272957 : Nat := 93438759339595858788133

theorem tailTrace_272957 : CollatzResearch.WordTrace tailWord_272957 prefixEnd_272957 93438759339595858788133 := by
  unfold tailWord_272957
  simp only [CollatzResearch.WordTrace]
  refine ⟨9955559672130881189313125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6637039781420587459542083 9955559672130881189313125)
  ·
    refine ⟨1866667438524540222996211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9955559672130881189313125 1866667438524540222996211)
    ·
      refine ⟨2800001157786810334494317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866667438524540222996211 2800001157786810334494317)
      ·
        refine ⟨1050000434170053875435369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2800001157786810334494317 1050000434170053875435369)
        ·
          refine ⟨787500325627540406576527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1050000434170053875435369 787500325627540406576527)
          ·
            refine ⟨1181250488441310609864791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787500325627540406576527 1181250488441310609864791)
            ·
              refine ⟨1771875732661965914797187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181250488441310609864791 1771875732661965914797187)
              ·
                refine ⟨2657813598992948872195781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771875732661965914797187 2657813598992948872195781)
                ·
                  refine ⟨498340049811177913536709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2657813598992948872195781 498340049811177913536709)
                  ·
                    refine ⟨93438759339595858788133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 498340049811177913536709 93438759339595858788133)
                    ·
                      rfl

theorem cell22_272957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_272957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272957 prefixEnd_272957 := by exact prefixLift 272957
  have htrace : WordTrace (prefixWord ++ tailWord_272957) baseStart_272957 baseEnd_272957 := by
    simpa [prefixWord, tailWord_272957, baseEnd_272957] using wordTrace_append hprefix tailTrace_272957
  have hstable : (prefixWord ++ tailWord_272957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272957).length < 2 ^ (prefixWord ++ tailWord_272957).sum := by decide
  have hdescent : baseEnd_272957 < baseStart_272957 := by decide
  rcases family_descends (prefixWord ++ tailWord_272957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272961 : List Nat := [1, 2, 5, 1, 1, 3, 3, 2, 4]
def baseStart_272961 : Nat := 118140960795 + 272961 * 2 ^ 59
def prefixEnd_272961 : Nat := 4983230072969 + 3 ^ 40 * 272961 * 2
def baseEnd_272961 : Nat := 31146709540447060562707

theorem tailTrace_272961 : CollatzResearch.WordTrace tailWord_272961 prefixEnd_272961 31146709540447060562707 := by
  unfold tailWord_272961
  simp only [CollatzResearch.WordTrace]
  refine ⟨9955705564116389872458737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6637137042744259914972491 9955705564116389872458737)
  ·
    refine ⟨7466779173087292404344053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9955705564116389872458737 7466779173087292404344053)
    ·
      refine ⟨700010547476933662907255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7466779173087292404344053 700010547476933662907255)
      ·
        refine ⟨1050015821215400494360883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700010547476933662907255 1050015821215400494360883)
        ·
          refine ⟨1575023731823100741541325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050015821215400494360883 1575023731823100741541325)
          ·
            refine ⟨590633899433662778077997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1575023731823100741541325 590633899433662778077997)
            ·
              refine ⟨221487712287623541779249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 590633899433662778077997 221487712287623541779249)
              ·
                refine ⟨166115784215717656334437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221487712287623541779249 166115784215717656334437)
                ·
                  refine ⟨31146709540447060562707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166115784215717656334437 31146709540447060562707)
                  ·
                    rfl

theorem cell22_272961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 4].length) (baseStart_272961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_272961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_272961 prefixEnd_272961 := by exact prefixLift 272961
  have htrace : WordTrace (prefixWord ++ tailWord_272961) baseStart_272961 baseEnd_272961 := by
    simpa [prefixWord, tailWord_272961, baseEnd_272961] using wordTrace_append hprefix tailTrace_272961
  have hstable : (prefixWord ++ tailWord_272961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272961).length < 2 ^ (prefixWord ++ tailWord_272961).sum := by decide
  have hdescent : baseEnd_272961 < baseStart_272961 := by decide
  rcases family_descends (prefixWord ++ tailWord_272961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273017 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 5]
def baseStart_273017 : Nat := 118140960795 + 273017 * 2 ^ 59
def prefixEnd_273017 : Nat := 4983230072969 + 3 ^ 40 * 273017 * 2
def baseEnd_273017 : Nat := 31153099521925234095983

theorem tailTrace_273017 : CollatzResearch.WordTrace tailWord_273017 prefixEnd_273017 31153099521925234095983 := by
  unfold tailWord_273017
  simp only [CollatzResearch.WordTrace]
  refine ⟨9957748051913511436497305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6638498701275674290998203 9957748051913511436497305)
  ·
    refine ⟨7468311038935133577372979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9957748051913511436497305 7468311038935133577372979)
    ·
      refine ⟨11202466558402700366059469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7468311038935133577372979 11202466558402700366059469)
      ·
        refine ⟨4200924959401012637272301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11202466558402700366059469 4200924959401012637272301)
        ·
          refine ⟨1575346859775379738977113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4200924959401012637272301 1575346859775379738977113)
          ·
            refine ⟨1181510144831534804232835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1575346859775379738977113 1181510144831534804232835)
            ·
              refine ⟨1772265217247302206349253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181510144831534804232835 1772265217247302206349253)
              ·
                refine ⟨332299728233869163690485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1772265217247302206349253 332299728233869163690485)
                ·
                  refine ⟨31153099521925234095983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 332299728233869163690485 31153099521925234095983)
                  ·
                    rfl

theorem cell22_273017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_273017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273017 prefixEnd_273017 := by exact prefixLift 273017
  have htrace : WordTrace (prefixWord ++ tailWord_273017) baseStart_273017 baseEnd_273017 := by
    simpa [prefixWord, tailWord_273017, baseEnd_273017] using wordTrace_append hprefix tailTrace_273017
  have hstable : (prefixWord ++ tailWord_273017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273017).length < 2 ^ (prefixWord ++ tailWord_273017).sum := by decide
  have hdescent : baseEnd_273017 < baseStart_273017 := by decide
  rcases family_descends (prefixWord ++ tailWord_273017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273047 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 3, 4]
def baseStart_273047 : Nat := 118140960795 + 273047 * 2 ^ 59
def prefixEnd_273047 : Nat := 4983230072969 + 3 ^ 40 * 273047 * 2
def baseEnd_273047 : Nat := 93469568178865624037857

theorem tailTrace_273047 : CollatzResearch.WordTrace tailWord_273047 prefixEnd_273047 93469568178865624037857 := by
  unfold tailWord_273047
  simp only [CollatzResearch.WordTrace]
  refine ⟨9958842241804826560089395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6639228161203217706726263 9958842241804826560089395)
  ·
    refine ⟨14938263362707239840134093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9958842241804826560089395 14938263362707239840134093)
    ·
      refine ⟨5601848761015214940050285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14938263362707239840134093 5601848761015214940050285)
      ·
        refine ⟨2100693285380705602518857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5601848761015214940050285 2100693285380705602518857)
        ·
          refine ⟨1575519964035529201889143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2100693285380705602518857 1575519964035529201889143)
          ·
            refine ⟨2363279946053293802833715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575519964035529201889143 2363279946053293802833715)
            ·
              refine ⟨3544919919079940704250573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363279946053293802833715 3544919919079940704250573)
              ·
                refine ⟨1329344969654977764093965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3544919919079940704250573 1329344969654977764093965)
                ·
                  refine ⟨498504363620616661535237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1329344969654977764093965 498504363620616661535237)
                  ·
                    refine ⟨93469568178865624037857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 498504363620616661535237 93469568178865624037857)
                    ·
                      rfl

theorem cell22_273047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_273047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273047 prefixEnd_273047 := by exact prefixLift 273047
  have htrace : WordTrace (prefixWord ++ tailWord_273047) baseStart_273047 baseEnd_273047 := by
    simpa [prefixWord, tailWord_273047, baseEnd_273047] using wordTrace_append hprefix tailTrace_273047
  have hstable : (prefixWord ++ tailWord_273047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273047).length < 2 ^ (prefixWord ++ tailWord_273047).sum := by decide
  have hdescent : baseEnd_273047 < baseStart_273047 := by decide
  rcases family_descends (prefixWord ++ tailWord_273047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273079 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 6]
def baseStart_273079 : Nat := 118140960795 + 273079 * 2 ^ 59
def prefixEnd_273079 : Nat := 4983230072969 + 3 ^ 40 * 273079 * 2
def baseEnd_273079 : Nat := 31160174144276069079253

theorem tailTrace_273079 : CollatzResearch.WordTrace tailWord_273079 prefixEnd_273079 31160174144276069079253 := by
  unfold tailWord_273079
  simp only [CollatzResearch.WordTrace]
  refine ⟨9960009377688896025254291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6640006251792597350169527 9960009377688896025254291)
  ·
    refine ⟨14940014066533344037881437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9960009377688896025254291 14940014066533344037881437)
    ·
      refine ⟨5602505274950004014205539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14940014066533344037881437 5602505274950004014205539)
      ·
        refine ⟨8403757912425006021308309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5602505274950004014205539 8403757912425006021308309)
        ·
          refine ⟨393926152144922157248827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8403757912425006021308309 393926152144922157248827)
          ·
            refine ⟨590889228217383235873241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393926152144922157248827 590889228217383235873241)
            ·
              refine ⟨443166921163037426904931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590889228217383235873241 443166921163037426904931)
              ·
                refine ⟨664750381744556140357397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443166921163037426904931 664750381744556140357397)
                ·
                  refine ⟨31160174144276069079253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 664750381744556140357397 31160174144276069079253)
                  ·
                    rfl

theorem cell22_273079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 6].length) (baseStart_273079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273079 prefixEnd_273079 := by exact prefixLift 273079
  have htrace : WordTrace (prefixWord ++ tailWord_273079) baseStart_273079 baseEnd_273079 := by
    simpa [prefixWord, tailWord_273079, baseEnd_273079] using wordTrace_append hprefix tailTrace_273079
  have hstable : (prefixWord ++ tailWord_273079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273079).length < 2 ^ (prefixWord ++ tailWord_273079).sum := by decide
  have hdescent : baseEnd_273079 < baseStart_273079 := by decide
  rcases family_descends (prefixWord ++ tailWord_273079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273137 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_273137 : Nat := 118140960795 + 273137 * 2 ^ 59
def prefixEnd_273137 : Nat := 4983230072969 + 3 ^ 40 * 273137 * 2
def baseEnd_273137 : Nat := 93500377018135389287581

theorem tailTrace_273137 : CollatzResearch.WordTrace tailWord_273137 prefixEnd_273137 93500377018135389287581 := by
  unfold tailWord_273137
  simp only [CollatzResearch.WordTrace]
  refine ⟨9962124811478771930865665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6641416540985847953910443 9962124811478771930865665)
  ·
    refine ⟨7471593608609078948149249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9962124811478771930865665 7471593608609078948149249)
    ·
      refine ⟨5603695206456809211111937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7471593608609078948149249 5603695206456809211111937)
      ·
        refine ⟨4202771404842606908333953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5603695206456809211111937 4202771404842606908333953)
        ·
          refine ⟨3152078553631955181250465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4202771404842606908333953 3152078553631955181250465)
          ·
            refine ⟨2364058915223966385937849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152078553631955181250465 2364058915223966385937849)
            ·
              refine ⟨1773044186417974789453387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2364058915223966385937849 1773044186417974789453387)
              ·
                refine ⟨2659566279626962184180081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773044186417974789453387 2659566279626962184180081)
                ·
                  refine ⟨1994674709720221638135061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2659566279626962184180081 1994674709720221638135061)
                  ·
                    refine ⟨93500377018135389287581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1994674709720221638135061 93500377018135389287581)
                    ·
                      rfl

theorem cell22_273137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_273137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273137 prefixEnd_273137 := by exact prefixLift 273137
  have htrace : WordTrace (prefixWord ++ tailWord_273137) baseStart_273137 baseEnd_273137 := by
    simpa [prefixWord, tailWord_273137, baseEnd_273137] using wordTrace_append hprefix tailTrace_273137
  have hstable : (prefixWord ++ tailWord_273137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273137).length < 2 ^ (prefixWord ++ tailWord_273137).sum := by decide
  have hdescent : baseEnd_273137 < baseStart_273137 := by decide
  rcases family_descends (prefixWord ++ tailWord_273137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273186 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_273186 : Nat := 118140960795 + 273186 * 2 ^ 59
def prefixEnd_273186 : Nat := 4983230072969 + 3 ^ 40 * 273186 * 2
def baseEnd_273186 : Nat := 31172383573171864937477

theorem tailTrace_273186 : CollatzResearch.WordTrace tailWord_273186 prefixEnd_273186 31172383573171864937477 := by
  unfold tailWord_273186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490977997075313324849853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6642607992200835532932941 2490977997075313324849853)
  ·
    refine ⟨934116748903242496818695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2490977997075313324849853 934116748903242496818695)
    ·
      refine ⟨1401175123354863745228043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934116748903242496818695 1401175123354863745228043)
      ·
        refine ⟨2101762685032295617842065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1401175123354863745228043 2101762685032295617842065)
        ·
          refine ⟨1576322013774221713381549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2101762685032295617842065 1576322013774221713381549)
          ·
            refine ⟨591120755165333142518081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1576322013774221713381549 591120755165333142518081)
            ·
              refine ⟨443340566373999856888561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591120755165333142518081 443340566373999856888561)
              ·
                refine ⟨332505424780499892666421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443340566373999856888561 332505424780499892666421)
                ·
                  refine ⟨31172383573171864937477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 332505424780499892666421 31172383573171864937477)
                  ·
                    rfl

theorem cell22_273186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_273186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273186 prefixEnd_273186 := by exact prefixLift 273186
  have htrace : WordTrace (prefixWord ++ tailWord_273186) baseStart_273186 baseEnd_273186 := by
    simpa [prefixWord, tailWord_273186, baseEnd_273186] using wordTrace_append hprefix tailTrace_273186
  have hstable : (prefixWord ++ tailWord_273186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273186).length < 2 ^ (prefixWord ++ tailWord_273186).sum := by decide
  have hdescent : baseEnd_273186 < baseStart_273186 := by decide
  rcases family_descends (prefixWord ++ tailWord_273186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273351 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 1, 4]
def baseStart_273351 : Nat := 118140960795 + 273351 * 2 ^ 59
def prefixEnd_273351 : Nat := 4983230072969 + 3 ^ 40 * 273351 * 2
def baseEnd_273351 : Nat := 93573633591510164436925

theorem tailTrace_273351 : CollatzResearch.WordTrace tailWord_273351 prefixEnd_273351 93573633591510164436925 := by
  unfold tailWord_273351
  simp only [CollatzResearch.WordTrace]
  refine ⟨9969930032703486479155907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6646620021802324319437271 9969930032703486479155907)
  ·
    refine ⟨14954895049055229718733861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9969930032703486479155907 14954895049055229718733861)
    ·
      refine ⟨2804042821697855572262599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14954895049055229718733861 2804042821697855572262599)
      ·
        refine ⟨4206064232546783358393899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804042821697855572262599 4206064232546783358393899)
        ·
          refine ⟨6309096348820175037590849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4206064232546783358393899 6309096348820175037590849)
          ·
            refine ⟨4731822261615131278193137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6309096348820175037590849 4731822261615131278193137)
            ·
              refine ⟨3548866696211348458644853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4731822261615131278193137 3548866696211348458644853)
              ·
                refine ⟨332706252769813917997955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3548866696211348458644853 332706252769813917997955)
                ·
                  refine ⟨499059379154720876996933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332706252769813917997955 499059379154720876996933)
                  ·
                    refine ⟨93573633591510164436925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 499059379154720876996933 93573633591510164436925)
                    ·
                      rfl

theorem cell22_273351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_273351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273351 prefixEnd_273351 := by exact prefixLift 273351
  have htrace : WordTrace (prefixWord ++ tailWord_273351) baseStart_273351 baseEnd_273351 := by
    simpa [prefixWord, tailWord_273351, baseEnd_273351] using wordTrace_append hprefix tailTrace_273351
  have hstable : (prefixWord ++ tailWord_273351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273351).length < 2 ^ (prefixWord ++ tailWord_273351).sum := by decide
  have hdescent : baseEnd_273351 < baseStart_273351 := by decide
  rcases family_descends (prefixWord ++ tailWord_273351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273398 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_273398 : Nat := 118140960795 + 273398 * 2 ^ 59
def prefixEnd_273398 : Nat := 4983230072969 + 3 ^ 40 * 273398 * 2
def baseEnd_273398 : Nat := 93589722652017708511781

theorem tailTrace_273398 : CollatzResearch.WordTrace tailWord_273398 prefixEnd_273398 93589722652017708511781 := by
  unfold tailWord_273398
  simp only [CollatzResearch.WordTrace]
  refine ⟨623227766470825844132303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6647762842355475670744565 623227766470825844132303)
  ·
    refine ⟨934841649706238766198455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 623227766470825844132303 934841649706238766198455)
    ·
      refine ⟨1402262474559358149297683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934841649706238766198455 1402262474559358149297683)
      ·
        refine ⟨2103393711839037223946525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402262474559358149297683 2103393711839037223946525)
        ·
          refine ⟨788772641939638958979947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2103393711839037223946525 788772641939638958979947)
          ·
            refine ⟨1183158962909458438469921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788772641939638958979947 1183158962909458438469921)
            ·
              refine ⟨887369222182093828852441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183158962909458438469921 887369222182093828852441)
              ·
                refine ⟨665526916636570371639331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887369222182093828852441 665526916636570371639331)
                ·
                  refine ⟨998290374954855557458997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665526916636570371639331 998290374954855557458997)
                  ·
                    refine ⟨93589722652017708511781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 998290374954855557458997 93589722652017708511781)
                    ·
                      rfl

theorem cell22_273398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_273398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273398 prefixEnd_273398 := by exact prefixLift 273398
  have htrace : WordTrace (prefixWord ++ tailWord_273398) baseStart_273398 baseEnd_273398 := by
    simpa [prefixWord, tailWord_273398, baseEnd_273398] using wordTrace_append hprefix tailTrace_273398
  have hstable : (prefixWord ++ tailWord_273398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273398).length < 2 ^ (prefixWord ++ tailWord_273398).sum := by decide
  have hdescent : baseEnd_273398 < baseStart_273398 := by decide
  rcases family_descends (prefixWord ++ tailWord_273398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273443 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 3, 3]
def baseStart_273443 : Nat := 118140960795 + 273443 * 2 ^ 59
def prefixEnd_273443 : Nat := 4983230072969 + 3 ^ 40 * 273443 * 2
def baseEnd_273443 : Nat := 93605127071652591136643

theorem tailTrace_273443 : CollatzResearch.WordTrace tailWord_273443 prefixEnd_273443 93605127071652591136643 := by
  unfold tailWord_273443
  simp only [CollatzResearch.WordTrace]
  refine ⟨9973285548370186191504983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6648857032246790794336655 9973285548370186191504983)
  ·
    refine ⟨14959928322555279287257475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9973285548370186191504983 14959928322555279287257475)
    ·
      refine ⟨22439892483832918930886213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14959928322555279287257475 22439892483832918930886213)
      ·
        refine ⟨4207479840718672299541165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22439892483832918930886213 4207479840718672299541165)
        ·
          refine ⟨1577804940269502112327937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4207479840718672299541165 1577804940269502112327937)
          ·
            refine ⟨1183353705202126584245953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577804940269502112327937 1183353705202126584245953)
            ·
              refine ⟨887515278901594938184465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183353705202126584245953 887515278901594938184465)
              ·
                refine ⟨665636459176196203638349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887515278901594938184465 665636459176196203638349)
                ·
                  refine ⟨249613672191073576364381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665636459176196203638349 249613672191073576364381)
                  ·
                    refine ⟨93605127071652591136643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 249613672191073576364381 93605127071652591136643)
                    ·
                      rfl

theorem cell22_273443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 3].length) (baseStart_273443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273443 prefixEnd_273443 := by exact prefixLift 273443
  have htrace : WordTrace (prefixWord ++ tailWord_273443) baseStart_273443 baseEnd_273443 := by
    simpa [prefixWord, tailWord_273443, baseEnd_273443] using wordTrace_append hprefix tailTrace_273443
  have hstable : (prefixWord ++ tailWord_273443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273443).length < 2 ^ (prefixWord ++ tailWord_273443).sum := by decide
  have hdescent : baseEnd_273443 < baseStart_273443 := by decide
  rcases family_descends (prefixWord ++ tailWord_273443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273490 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_273490 : Nat := 118140960795 + 273490 * 2 ^ 59
def prefixEnd_273490 : Nat := 4983230072969 + 3 ^ 40 * 273490 * 2
def baseEnd_273490 : Nat := 31207072044053378403833

theorem tailTrace_273490 : CollatzResearch.WordTrace tailWord_273490 prefixEnd_273490 31207072044053378403833 := by
  unfold tailWord_273490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493749944799978304616481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6649999852799942145643949 2493749944799978304616481)
  ·
    refine ⟨1870312458599983728462361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2493749944799978304616481 1870312458599983728462361)
    ·
      refine ⟨1402734343949987796346771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1870312458599983728462361 1402734343949987796346771)
      ·
        refine ⟨2104101515924981694520157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402734343949987796346771 2104101515924981694520157)
        ·
          refine ⟨789038068471868135445059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2104101515924981694520157 789038068471868135445059)
          ·
            refine ⟨1183557102707802203167589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789038068471868135445059 1183557102707802203167589)
            ·
              refine ⟨221916956757712913093923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1183557102707802203167589 221916956757712913093923)
              ·
                refine ⟨332875435136569369640885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221916956757712913093923 332875435136569369640885)
                ·
                  refine ⟨31207072044053378403833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 332875435136569369640885 31207072044053378403833)
                  ·
                    rfl

theorem cell22_273490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_273490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273490 prefixEnd_273490 := by exact prefixLift 273490
  have htrace : WordTrace (prefixWord ++ tailWord_273490) baseStart_273490 baseEnd_273490 := by
    simpa [prefixWord, tailWord_273490, baseEnd_273490] using wordTrace_append hprefix tailTrace_273490
  have hstable : (prefixWord ++ tailWord_273490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273490).length < 2 ^ (prefixWord ++ tailWord_273490).sum := by decide
  have hdescent : baseEnd_273490 < baseStart_273490 := by decide
  rcases family_descends (prefixWord ++ tailWord_273490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273520 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 1, 4]
def baseStart_273520 : Nat := 118140960795 + 273520 * 2 ^ 59
def prefixEnd_273520 : Nat := 4983230072969 + 3 ^ 40 * 273520 * 2
def baseEnd_273520 : Nat := 93631485745250056961407

theorem tailTrace_273520 : CollatzResearch.WordTrace tailWord_273520 prefixEnd_273520 93631485745250056961407 := by
  unfold tailWord_273520
  simp only [CollatzResearch.WordTrace]
  refine ⟨4988046984545614171029007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6650729312727485561372009 4988046984545614171029007)
  ·
    refine ⟨7482070476818421256543511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4988046984545614171029007 7482070476818421256543511)
    ·
      refine ⟨11223105715227631884815267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7482070476818421256543511 11223105715227631884815267)
      ·
        refine ⟨16834658572841447827222901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11223105715227631884815267 16834658572841447827222901)
        ·
          refine ⟨1578249241203885733802147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16834658572841447827222901 1578249241203885733802147)
          ·
            refine ⟨2367373861805828600703221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578249241203885733802147 2367373861805828600703221)
            ·
              refine ⟨221941299544296431315927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2367373861805828600703221 221941299544296431315927)
              ·
                refine ⟨332911949316444646973891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221941299544296431315927 332911949316444646973891)
                ·
                  refine ⟨499367923974666970460837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332911949316444646973891 499367923974666970460837)
                  ·
                    refine ⟨93631485745250056961407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 499367923974666970460837 93631485745250056961407)
                    ·
                      rfl

theorem cell22_273520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 4].length) (baseStart_273520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273520 prefixEnd_273520 := by exact prefixLift 273520
  have htrace : WordTrace (prefixWord ++ tailWord_273520) baseStart_273520 baseEnd_273520 := by
    simpa [prefixWord, tailWord_273520, baseEnd_273520] using wordTrace_append hprefix tailTrace_273520
  have hstable : (prefixWord ++ tailWord_273520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273520).length < 2 ^ (prefixWord ++ tailWord_273520).sum := by decide
  have hdescent : baseEnd_273520 < baseStart_273520 := by decide
  rcases family_descends (prefixWord ++ tailWord_273520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273550 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_273550 : Nat := 118140960795 + 273550 * 2 ^ 59
def prefixEnd_273550 : Nat := 4983230072969 + 3 ^ 40 * 273550 * 2
def baseEnd_273550 : Nat := 93641755358339978711315

theorem tailTrace_273550 : CollatzResearch.WordTrace tailWord_273550 prefixEnd_273550 93641755358339978711315 := by
  unfold tailWord_273550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247148519872817933206263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6651458772655028977100069 1247148519872817933206263)
  ·
    refine ⟨1870722779809226899809395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1247148519872817933206263 1870722779809226899809395)
    ·
      refine ⟨2806084169713840349714093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1870722779809226899809395 2806084169713840349714093)
      ·
        refine ⟨1052281563642690131142785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2806084169713840349714093 1052281563642690131142785)
        ·
          refine ⟨789211172732017598357089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1052281563642690131142785 789211172732017598357089)
          ·
            refine ⟨591908379549013198767817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 789211172732017598357089 591908379549013198767817)
            ·
              refine ⟨443931284661759899075863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591908379549013198767817 443931284661759899075863)
              ·
                refine ⟨665896926992639848613795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443931284661759899075863 665896926992639848613795)
                ·
                  refine ⟨998845390488959772920693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665896926992639848613795 998845390488959772920693)
                  ·
                    refine ⟨93641755358339978711315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 998845390488959772920693 93641755358339978711315)
                    ·
                      rfl

theorem cell22_273550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_273550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273550 prefixEnd_273550 := by exact prefixLift 273550
  have htrace : WordTrace (prefixWord ++ tailWord_273550) baseStart_273550 baseEnd_273550 := by
    simpa [prefixWord, tailWord_273550, baseEnd_273550] using wordTrace_append hprefix tailTrace_273550
  have hstable : (prefixWord ++ tailWord_273550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273550).length < 2 ^ (prefixWord ++ tailWord_273550).sum := by decide
  have hdescent : baseEnd_273550 < baseStart_273550 := by decide
  rcases family_descends (prefixWord ++ tailWord_273550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273608 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 5]
def baseStart_273608 : Nat := 118140960795 + 273608 * 2 ^ 59
def prefixEnd_273608 : Nat := 4983230072969 + 3 ^ 40 * 273608 * 2
def baseEnd_273608 : Nat := 31220536647882386920379

theorem tailTrace_273608 : CollatzResearch.WordTrace tailWord_273608 prefixEnd_273608 31220536647882386920379 := by
  unfold tailWord_273608
  simp only [CollatzResearch.WordTrace]
  refine ⟨4989651796386209685630739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6652869061848279580840985 4989651796386209685630739)
  ·
    refine ⟨7484477694579314528446109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4989651796386209685630739 7484477694579314528446109)
    ·
      refine ⟨2806679135467242948167291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7484477694579314528446109 2806679135467242948167291)
      ·
        refine ⟨4210018703200864422250937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2806679135467242948167291 4210018703200864422250937)
        ·
          refine ⟨3157514027400648316688203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4210018703200864422250937 3157514027400648316688203)
          ·
            refine ⟨4736271041100972475032305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157514027400648316688203 4736271041100972475032305)
            ·
              refine ⟨3552203280825729356274229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4736271041100972475032305 3552203280825729356274229)
              ·
                refine ⟨333019057577412127150709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3552203280825729356274229 333019057577412127150709)
                ·
                  refine ⟨31220536647882386920379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 333019057577412127150709 31220536647882386920379)
                  ·
                    rfl

theorem cell22_273608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_273608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273608 prefixEnd_273608 := by exact prefixLift 273608
  have htrace : WordTrace (prefixWord ++ tailWord_273608) baseStart_273608 baseEnd_273608 := by
    simpa [prefixWord, tailWord_273608, baseEnd_273608] using wordTrace_append hprefix tailTrace_273608
  have hstable : (prefixWord ++ tailWord_273608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273608).length < 2 ^ (prefixWord ++ tailWord_273608).sum := by decide
  have hdescent : baseEnd_273608 < baseStart_273608 := by decide
  rcases family_descends (prefixWord ++ tailWord_273608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273698 : List Nat := [3, 3, 1, 1, 14]
def baseStart_273698 : Nat := 118140960795 + 273698 * 2 ^ 59
def prefixEnd_273698 : Nat := 4983230072969 + 3 ^ 40 * 273698 * 2
def baseEnd_273698 : Nat := 385565509394719860127

theorem tailTrace_273698 : CollatzResearch.WordTrace tailWord_273698 prefixEnd_273698 385565509394719860127 := by
  unfold tailWord_273698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495646540611591185509437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6655057441630909828025165 2495646540611591185509437)
  ·
    refine ⟨935867452729346694566039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2495646540611591185509437 935867452729346694566039)
    ·
      refine ⟨1403801179094020041849059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935867452729346694566039 1403801179094020041849059)
      ·
        refine ⟨2105701768641030062773589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1403801179094020041849059 2105701768641030062773589)
        ·
          refine ⟨385565509394719860127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 2105701768641030062773589 385565509394719860127)
          ·
            rfl

theorem cell22_273698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 14].length) (baseStart_273698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273698 prefixEnd_273698 := by exact prefixLift 273698
  have htrace : WordTrace (prefixWord ++ tailWord_273698) baseStart_273698 baseEnd_273698 := by
    simpa [prefixWord, tailWord_273698, baseEnd_273698] using wordTrace_append hprefix tailTrace_273698
  have hstable : (prefixWord ++ tailWord_273698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273698).length < 2 ^ (prefixWord ++ tailWord_273698).sum := by decide
  have hdescent : baseEnd_273698 < baseStart_273698 := by decide
  rcases family_descends (prefixWord ++ tailWord_273698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273700 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_273700 : Nat := 118140960795 + 273700 * 2 ^ 59
def prefixEnd_273700 : Nat := 4983230072969 + 3 ^ 40 * 273700 * 2
def baseEnd_273700 : Nat := 93693103423789587460855

theorem tailTrace_273700 : CollatzResearch.WordTrace tailWord_273700 prefixEnd_273700 93693103423789587460855 := by
  unfold tailWord_273700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4991329554219559541805277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6655106072292746055740369 4991329554219559541805277)
  ·
    refine ⟨1871748582832334828176979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4991329554219559541805277 1871748582832334828176979)
    ·
      refine ⟨2807622874248502242265469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1871748582832334828176979 2807622874248502242265469)
      ·
        refine ⟨1052858577843188340849551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2807622874248502242265469 1052858577843188340849551)
        ·
          refine ⟨1579287866764782511274327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052858577843188340849551 1579287866764782511274327)
          ·
            refine ⟨2368931800147173766911491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579287866764782511274327 2368931800147173766911491)
            ·
              refine ⟨3553397700220760650367237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368931800147173766911491 3553397700220760650367237)
              ·
                refine ⟨666262068791392621943857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3553397700220760650367237 666262068791392621943857)
                ·
                  refine ⟨499696551593544466457893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 666262068791392621943857 499696551593544466457893)
                  ·
                    refine ⟨93693103423789587460855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 499696551593544466457893 93693103423789587460855)
                    ·
                      rfl

theorem cell22_273700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_273700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273700 prefixEnd_273700 := by exact prefixLift 273700
  have htrace : WordTrace (prefixWord ++ tailWord_273700) baseStart_273700 baseEnd_273700 := by
    simpa [prefixWord, tailWord_273700, baseEnd_273700] using wordTrace_append hprefix tailTrace_273700
  have hstable : (prefixWord ++ tailWord_273700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273700).length < 2 ^ (prefixWord ++ tailWord_273700).sum := by decide
  have hdescent : baseEnd_273700 < baseStart_273700 := by decide
  rcases family_descends (prefixWord ++ tailWord_273700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273704 : List Nat := [2, 1, 5, 1, 2, 1, 4, 2, 4]
def baseStart_273704 : Nat := 118140960795 + 273704 * 2 ^ 59
def prefixEnd_273704 : Nat := 4983230072969 + 3 ^ 40 * 273704 * 2
def baseEnd_273704 : Nat := 31231490901844970120281

theorem tailTrace_273704 : CollatzResearch.WordTrace tailWord_273704 prefixEnd_273704 31231490901844970120281 := by
  unfold tailWord_273704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4991402500212313883378083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6655203333616418511170777 4991402500212313883378083)
  ·
    refine ⟨7487103750318470825067125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4991402500212313883378083 7487103750318470825067125)
    ·
      refine ⟨701915976592356639850043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7487103750318470825067125 701915976592356639850043)
      ·
        refine ⟨1052873964888534959775065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701915976592356639850043 1052873964888534959775065)
        ·
          refine ⟨789655473666401219831299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1052873964888534959775065 789655473666401219831299)
          ·
            refine ⟨1184483210499601829746949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789655473666401219831299 1184483210499601829746949)
            ·
              refine ⟨222090601968675343077553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1184483210499601829746949 222090601968675343077553)
              ·
                refine ⟨166567951476506507308165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222090601968675343077553 166567951476506507308165)
                ·
                  refine ⟨31231490901844970120281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166567951476506507308165 31231490901844970120281)
                  ·
                    rfl

theorem cell22_273704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 4].length) (baseStart_273704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273704 prefixEnd_273704 := by exact prefixLift 273704
  have htrace : WordTrace (prefixWord ++ tailWord_273704) baseStart_273704 baseEnd_273704 := by
    simpa [prefixWord, tailWord_273704, baseEnd_273704] using wordTrace_append hprefix tailTrace_273704
  have hstable : (prefixWord ++ tailWord_273704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273704).length < 2 ^ (prefixWord ++ tailWord_273704).sum := by decide
  have hdescent : baseEnd_273704 < baseStart_273704 := by decide
  rcases family_descends (prefixWord ++ tailWord_273704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273715 : List Nat := [1, 1, 1, 2, 5, 4, 1, 7]
def baseStart_273715 : Nat := 118140960795 + 273715 * 2 ^ 59
def prefixEnd_273715 : Nat := 4983230072969 + 3 ^ 40 * 273715 * 2
def baseEnd_273715 : Nat := 10410915358926060926201

theorem tailTrace_273715 : CollatzResearch.WordTrace tailWord_273715 prefixEnd_273715 10410915358926060926201 := by
  unfold tailWord_273715
  simp only [CollatzResearch.WordTrace]
  refine ⟨9983206203384776645406599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6655470802256517763604399 9983206203384776645406599)
  ·
    refine ⟨14974809305077164968109899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9983206203384776645406599 14974809305077164968109899)
    ·
      refine ⟨22462213957615747452164849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14974809305077164968109899 22462213957615747452164849)
      ·
        refine ⟨16846660468211810589123637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22462213957615747452164849 16846660468211810589123637)
        ·
          refine ⟨1579374418894857242730341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16846660468211810589123637 1579374418894857242730341)
          ·
            refine ⟨296132703542785733011939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1579374418894857242730341 296132703542785733011939)
            ·
              refine ⟨444199055314178599517909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296132703542785733011939 444199055314178599517909)
              ·
                refine ⟨10410915358926060926201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 444199055314178599517909 10410915358926060926201)
                ·
                  rfl

theorem cell22_273715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 7].length) (baseStart_273715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273715 prefixEnd_273715 := by exact prefixLift 273715
  have htrace : WordTrace (prefixWord ++ tailWord_273715) baseStart_273715 baseEnd_273715 := by
    simpa [prefixWord, tailWord_273715, baseEnd_273715] using wordTrace_append hprefix tailTrace_273715
  have hstable : (prefixWord ++ tailWord_273715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273715).length < 2 ^ (prefixWord ++ tailWord_273715).sum := by decide
  have hdescent : baseEnd_273715 < baseStart_273715 := by decide
  rcases family_descends (prefixWord ++ tailWord_273715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273728 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_273728 : Nat := 118140960795 + 273728 * 2 ^ 59
def prefixEnd_273728 : Nat := 4983230072969 + 3 ^ 40 * 273728 * 2
def baseEnd_273728 : Nat := 93702688396006847760769

theorem tailTrace_273728 : CollatzResearch.WordTrace tailWord_273728 prefixEnd_273728 93702688396006847760769 := by
  unfold tailWord_273728
  simp only [CollatzResearch.WordTrace]
  refine ⟨4991840176168839932814919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6655786901558453243753225 4991840176168839932814919)
  ·
    refine ⟨7487760264253259899222379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4991840176168839932814919 7487760264253259899222379)
    ·
      refine ⟨11231640396379889848833569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7487760264253259899222379 11231640396379889848833569)
      ·
        refine ⟨8423730297284917386625177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11231640396379889848833569 8423730297284917386625177)
        ·
          refine ⟨6317797722963688039968883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8423730297284917386625177 6317797722963688039968883)
          ·
            refine ⟨9476696584445532059953325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6317797722963688039968883 9476696584445532059953325)
            ·
              refine ⟨3553761219167074522482497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9476696584445532059953325 3553761219167074522482497)
              ·
                refine ⟨2665320914375305891861873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3553761219167074522482497 2665320914375305891861873)
                ·
                  refine ⟨1998990685781479418896405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2665320914375305891861873 1998990685781479418896405)
                  ·
                    refine ⟨93702688396006847760769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1998990685781479418896405 93702688396006847760769)
                    ·
                      rfl

theorem cell22_273728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_273728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273728 prefixEnd_273728 := by exact prefixLift 273728
  have htrace : WordTrace (prefixWord ++ tailWord_273728) baseStart_273728 baseEnd_273728 := by
    simpa [prefixWord, tailWord_273728, baseEnd_273728] using wordTrace_append hprefix tailTrace_273728
  have hstable : (prefixWord ++ tailWord_273728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273728).length < 2 ^ (prefixWord ++ tailWord_273728).sum := by decide
  have hdescent : baseEnd_273728 < baseStart_273728 := by decide
  rcases family_descends (prefixWord ++ tailWord_273728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273760 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 7]
def baseStart_273760 : Nat := 118140960795 + 273760 * 2 ^ 59
def prefixEnd_273760 : Nat := 4983230072969 + 3 ^ 40 * 273760 * 2
def baseEnd_273760 : Nat := 31237880883323143653557

theorem tailTrace_273760 : CollatzResearch.WordTrace tailWord_273760 prefixEnd_273760 31237880883323143653557 := by
  unfold tailWord_273760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4992423744110874665397367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6656564992147832887196489 4992423744110874665397367)
  ·
    refine ⟨7488635616166311998096051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4992423744110874665397367 7488635616166311998096051)
    ·
      refine ⟨11232953424249467997144077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7488635616166311998096051 11232953424249467997144077)
      ·
        refine ⟨4212357534093550498929029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11232953424249467997144077 4212357534093550498929029)
        ·
          refine ⟨789817037642540718549193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4212357534093550498929029 789817037642540718549193)
          ·
            refine ⟨592362778231905538911895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 789817037642540718549193 592362778231905538911895)
            ·
              refine ⟨888544167347858308367843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592362778231905538911895 888544167347858308367843)
              ·
                refine ⟨1332816251021787462551765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888544167347858308367843 1332816251021787462551765)
                ·
                  refine ⟨31237880883323143653557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1332816251021787462551765 31237880883323143653557)
                  ·
                    rfl

theorem cell22_273760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_273760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273760 prefixEnd_273760 := by exact prefixLift 273760
  have htrace : WordTrace (prefixWord ++ tailWord_273760) baseStart_273760 baseEnd_273760 := by
    simpa [prefixWord, tailWord_273760, baseEnd_273760] using wordTrace_append hprefix tailTrace_273760
  have hstable : (prefixWord ++ tailWord_273760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273760).length < 2 ^ (prefixWord ++ tailWord_273760).sum := by decide
  have hdescent : baseEnd_273760 < baseStart_273760 := by decide
  rcases family_descends (prefixWord ++ tailWord_273760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273764 : List Nat := [2, 3, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_273764 : Nat := 118140960795 + 273764 * 2 ^ 59
def prefixEnd_273764 : Nat := 4983230072969 + 3 ^ 40 * 273764 * 2
def baseEnd_273764 : Nat := 93715011931714753860659

theorem tailTrace_273764 : CollatzResearch.WordTrace tailWord_273764 prefixEnd_273764 93715011931714753860659 := by
  unfold tailWord_273764
  simp only [CollatzResearch.WordTrace]
  refine ⟨4992496690103629006970173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6656662253471505342626897 4992496690103629006970173)
  ·
    refine ⟨1872186258788860877613815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4992496690103629006970173 1872186258788860877613815)
    ·
      refine ⟨2808279388183291316420723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1872186258788860877613815 2808279388183291316420723)
      ·
        refine ⟨4212419082274936974631085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2808279388183291316420723 4212419082274936974631085)
        ·
          refine ⟨1579657155853101365486657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4212419082274936974631085 1579657155853101365486657)
          ·
            refine ⟨1184742866889826024114993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1579657155853101365486657 1184742866889826024114993)
            ·
              refine ⟨888557150167369518086245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184742866889826024114993 888557150167369518086245)
              ·
                refine ⟨166604465656381784641171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 888557150167369518086245 166604465656381784641171)
                ·
                  refine ⟨249906698484572676961757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166604465656381784641171 249906698484572676961757)
                  ·
                    refine ⟨93715011931714753860659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 249906698484572676961757 93715011931714753860659)
                    ·
                      rfl

theorem cell22_273764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_273764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273764 prefixEnd_273764 := by exact prefixLift 273764
  have htrace : WordTrace (prefixWord ++ tailWord_273764) baseStart_273764 baseEnd_273764 := by
    simpa [prefixWord, tailWord_273764, baseEnd_273764] using wordTrace_append hprefix tailTrace_273764
  have hstable : (prefixWord ++ tailWord_273764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273764).length < 2 ^ (prefixWord ++ tailWord_273764).sum := by decide
  have hdescent : baseEnd_273764 < baseStart_273764 := by decide
  rcases family_descends (prefixWord ++ tailWord_273764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273880 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_273880 : Nat := 118140960795 + 273880 * 2 ^ 59
def prefixEnd_273880 : Nat := 4983230072969 + 3 ^ 40 * 273880 * 2
def baseEnd_273880 : Nat := 93754721102329117960303

theorem tailTrace_273880 : CollatzResearch.WordTrace tailWord_273880 prefixEnd_273880 93754721102329117960303 := by
  unfold tailWord_273880
  simp only [CollatzResearch.WordTrace]
  refine ⟨4994612123893504912581547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6659482831858006550108729 4994612123893504912581547)
  ·
    refine ⟨7491918185840257368872321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4994612123893504912581547 7491918185840257368872321)
    ·
      refine ⟨5618938639380193026654241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7491918185840257368872321 5618938639380193026654241)
      ·
        refine ⟨4214203979535144769990681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5618938639380193026654241 4214203979535144769990681)
        ·
          refine ⟨3160652984651358577493011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4214203979535144769990681 3160652984651358577493011)
          ·
            refine ⟨4740979476977037866239517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160652984651358577493011 4740979476977037866239517)
            ·
              refine ⟨1777867303866389199839819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4740979476977037866239517 1777867303866389199839819)
              ·
                refine ⟨2666800955799583799759729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777867303866389199839819 2666800955799583799759729)
                ·
                  refine ⟨2000100716849687849819797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2666800955799583799759729 2000100716849687849819797)
                  ·
                    refine ⟨93754721102329117960303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2000100716849687849819797 93754721102329117960303)
                    ·
                      rfl

theorem cell22_273880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_273880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273880 prefixEnd_273880 := by exact prefixLift 273880
  have htrace : WordTrace (prefixWord ++ tailWord_273880) baseStart_273880 baseEnd_273880 := by
    simpa [prefixWord, tailWord_273880, baseEnd_273880] using wordTrace_append hprefix tailTrace_273880
  have hstable : (prefixWord ++ tailWord_273880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273880).length < 2 ^ (prefixWord ++ tailWord_273880).sum := by decide
  have hdescent : baseEnd_273880 < baseStart_273880 := by decide
  rcases family_descends (prefixWord ++ tailWord_273880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273927 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 2, 5]
def baseStart_273927 : Nat := 118140960795 + 273927 * 2 ^ 59
def prefixEnd_273927 : Nat := 4983230072969 + 3 ^ 40 * 273927 * 2
def baseEnd_273927 : Nat := 93770810162836662035159

theorem tailTrace_273927 : CollatzResearch.WordTrace tailWord_273927 prefixEnd_273927 93770810162836662035159 := by
  unfold tailWord_273927
  simp only [CollatzResearch.WordTrace]
  refine ⟨9990938478616736852124035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6660625652411157901416023 9990938478616736852124035)
  ·
    refine ⟨14986407717925105278186053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9990938478616736852124035 14986407717925105278186053)
    ·
      refine ⟨2809951447110957239659885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14986407717925105278186053 2809951447110957239659885)
      ·
        refine ⟨1053731792666608964872457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2809951447110957239659885 1053731792666608964872457)
        ·
          refine ⟨790298844499956723654343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1053731792666608964872457 790298844499956723654343)
          ·
            refine ⟨1185448266749935085481515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790298844499956723654343 1185448266749935085481515)
            ·
              refine ⟨1778172400124902628222273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185448266749935085481515 1778172400124902628222273)
              ·
                refine ⟨1333629300093676971166705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778172400124902628222273 1333629300093676971166705)
                ·
                  refine ⟨1000221975070257728375029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1333629300093676971166705 1000221975070257728375029)
                  ·
                    refine ⟨93770810162836662035159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1000221975070257728375029 93770810162836662035159)
                    ·
                      rfl

theorem cell22_273927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_273927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273927 prefixEnd_273927 := by exact prefixLift 273927
  have htrace : WordTrace (prefixWord ++ tailWord_273927) baseStart_273927 baseEnd_273927 := by
    simpa [prefixWord, tailWord_273927, baseEnd_273927] using wordTrace_append hprefix tailTrace_273927
  have hstable : (prefixWord ++ tailWord_273927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273927).length < 2 ^ (prefixWord ++ tailWord_273927).sum := by decide
  have hdescent : baseEnd_273927 < baseStart_273927 := by decide
  rcases family_descends (prefixWord ++ tailWord_273927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273989 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 2, 3]
def baseStart_273989 : Nat := 118140960795 + 273989 * 2 ^ 59
def prefixEnd_273989 : Nat := 4983230072969 + 3 ^ 40 * 273989 * 2
def baseEnd_273989 : Nat := 93792034029889166984969

theorem tailTrace_273989 : CollatzResearch.WordTrace tailWord_273989 prefixEnd_273989 93792034029889166984969 := by
  unfold tailWord_273989
  simp only [CollatzResearch.WordTrace]
  refine ⟨9993199804392121440881021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6662133202928080960587347 9993199804392121440881021)
  ·
    refine ⟨3747449926647045540330383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9993199804392121440881021 3747449926647045540330383)
    ·
      refine ⟨5621174889970568310495575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3747449926647045540330383 5621174889970568310495575)
      ·
        refine ⟨8431762334955852465743363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5621174889970568310495575 8431762334955852465743363)
        ·
          refine ⟨12647643502433778698615045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8431762334955852465743363 12647643502433778698615045)
          ·
            refine ⟨2371433156706333505990321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12647643502433778698615045 2371433156706333505990321)
            ·
              refine ⟨1778574867529750129492741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2371433156706333505990321 1778574867529750129492741)
              ·
                refine ⟨333482787661828149279889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1778574867529750129492741 333482787661828149279889)
                ·
                  refine ⟨250112090746371111959917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333482787661828149279889 250112090746371111959917)
                  ·
                    refine ⟨93792034029889166984969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250112090746371111959917 93792034029889166984969)
                    ·
                      rfl

theorem cell22_273989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_273989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273989 prefixEnd_273989 := by exact prefixLift 273989
  have htrace : WordTrace (prefixWord ++ tailWord_273989) baseStart_273989 baseEnd_273989 := by
    simpa [prefixWord, tailWord_273989, baseEnd_273989] using wordTrace_append hprefix tailTrace_273989
  have hstable : (prefixWord ++ tailWord_273989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273989).length < 2 ^ (prefixWord ++ tailWord_273989).sum := by decide
  have hdescent : baseEnd_273989 < baseStart_273989 := by decide
  rcases family_descends (prefixWord ++ tailWord_273989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273991 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 6]
def baseStart_273991 : Nat := 118140960795 + 273991 * 2 ^ 59
def prefixEnd_273991 : Nat := 4983230072969 + 3 ^ 40 * 273991 * 2
def baseEnd_273991 : Nat := 31264239556920609478321

theorem tailTrace_273991 : CollatzResearch.WordTrace tailWord_273991 prefixEnd_273991 31264239556920609478321 := by
  unfold tailWord_273991
  simp only [CollatzResearch.WordTrace]
  refine ⟨9993272750384875782453827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6662181833589917188302551 9993272750384875782453827)
  ·
    refine ⟨14989909125577313673680741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9993272750384875782453827 14989909125577313673680741)
    ·
      refine ⟨2810607961045746313815139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14989909125577313673680741 2810607961045746313815139)
      ·
        refine ⟨4215911941568619470722709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2810607961045746313815139 4215911941568619470722709)
        ·
          refine ⟨197620872261029037690127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4215911941568619470722709 197620872261029037690127)
          ·
            refine ⟨296431308391543556535191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197620872261029037690127 296431308391543556535191)
            ·
              refine ⟨444646962587315334802787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296431308391543556535191 444646962587315334802787)
              ·
                refine ⟨666970443880973002204181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444646962587315334802787 666970443880973002204181)
                ·
                  refine ⟨31264239556920609478321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 666970443880973002204181 31264239556920609478321)
                  ·
                    rfl

theorem cell22_273991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 6].length) (baseStart_273991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_273991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_273991 prefixEnd_273991 := by exact prefixLift 273991
  have htrace : WordTrace (prefixWord ++ tailWord_273991) baseStart_273991 baseEnd_273991 := by
    simpa [prefixWord, tailWord_273991, baseEnd_273991] using wordTrace_append hprefix tailTrace_273991
  have hstable : (prefixWord ++ tailWord_273991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273991).length < 2 ^ (prefixWord ++ tailWord_273991).sum := by decide
  have hdescent : baseEnd_273991 < baseStart_273991 := by decide
  rcases family_descends (prefixWord ++ tailWord_273991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274002 : List Nat := [3, 2, 2, 1, 2, 2, 1, 9]
def baseStart_274002 : Nat := 118140960795 + 274002 * 2 ^ 59
def prefixEnd_274002 : Nat := 4983230072969 + 3 ^ 40 * 274002 * 2
def baseEnd_274002 : Nat := 10421831577284607378881

theorem tailTrace_274002 : CollatzResearch.WordTrace tailWord_274002 prefixEnd_274002 10421831577284607378881 := by
  unfold tailWord_274002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498418488336256165276065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6662449302230016440736173 2498418488336256165276065)
  ·
    refine ⟨1873813866252192123957049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2498418488336256165276065 1873813866252192123957049)
    ·
      refine ⟨1405360399689144092967787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1873813866252192123957049 1405360399689144092967787)
      ·
        refine ⟨2108040599533716139451681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1405360399689144092967787 2108040599533716139451681)
        ·
          refine ⟨1581030449650287104588761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2108040599533716139451681 1581030449650287104588761)
          ·
            refine ⟨1185772837237715328441571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1581030449650287104588761 1185772837237715328441571)
            ·
              refine ⟨1778659255856572992662357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185772837237715328441571 1778659255856572992662357)
              ·
                refine ⟨10421831577284607378881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1778659255856572992662357 10421831577284607378881)
                ·
                  rfl

theorem cell22_274002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_274002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274002 prefixEnd_274002 := by exact prefixLift 274002
  have htrace : WordTrace (prefixWord ++ tailWord_274002) baseStart_274002 baseEnd_274002 := by
    simpa [prefixWord, tailWord_274002, baseEnd_274002] using wordTrace_append hprefix tailTrace_274002
  have hstable : (prefixWord ++ tailWord_274002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274002).length < 2 ^ (prefixWord ++ tailWord_274002).sum := by decide
  have hdescent : baseEnd_274002 < baseStart_274002 := by decide
  rcases family_descends (prefixWord ++ tailWord_274002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274068 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_274068 : Nat := 118140960795 + 274068 * 2 ^ 59
def prefixEnd_274068 : Nat := 4983230072969 + 3 ^ 40 * 274068 * 2
def baseEnd_274068 : Nat := 93819077344359294259727

theorem tailTrace_274068 : CollatzResearch.WordTrace tailWord_274068 prefixEnd_274068 93819077344359294259727 := by
  unfold tailWord_274068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4998040585552958966503429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6664054114070611955337905 4998040585552958966503429)
  ·
    refine ⟨937132609791179806219393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4998040585552958966503429 937132609791179806219393)
    ·
      refine ⟨702849457343384854664545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 937132609791179806219393 702849457343384854664545)
      ·
        refine ⟨527137093007538640998409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 702849457343384854664545 527137093007538640998409)
        ·
          refine ⟨395352819755653980748807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527137093007538640998409 395352819755653980748807)
          ·
            refine ⟨593029229633480971123211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395352819755653980748807 593029229633480971123211)
            ·
              refine ⟨889543844450221456684817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593029229633480971123211 889543844450221456684817)
              ·
                refine ⟨667157883337666092513613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889543844450221456684817 667157883337666092513613)
                ·
                  refine ⟨250184206251624784692605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667157883337666092513613 250184206251624784692605)
                  ·
                    refine ⟨93819077344359294259727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250184206251624784692605 93819077344359294259727)
                    ·
                      rfl

theorem cell22_274068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_274068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274068 prefixEnd_274068 := by exact prefixLift 274068
  have htrace : WordTrace (prefixWord ++ tailWord_274068) baseStart_274068 baseEnd_274068 := by
    simpa [prefixWord, tailWord_274068, baseEnd_274068] using wordTrace_append hprefix tailTrace_274068
  have hstable : (prefixWord ++ tailWord_274068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274068).length < 2 ^ (prefixWord ++ tailWord_274068).sum := by decide
  have hdescent : baseEnd_274068 < baseStart_274068 := by decide
  rcases family_descends (prefixWord ++ tailWord_274068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274107 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 3, 5]
def baseStart_274107 : Nat := 118140960795 + 274107 * 2 ^ 59
def prefixEnd_274107 : Nat := 4983230072969 + 3 ^ 40 * 274107 * 2
def baseEnd_274107 : Nat := 93832427841376192534607

theorem tailTrace_274107 : CollatzResearch.WordTrace tailWord_274107 prefixEnd_274107 93832427841376192534607 := by
  unfold tailWord_274107
  simp only [CollatzResearch.WordTrace]
  refine ⟨9997503617964627593676575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6665002411976418395784383 9997503617964627593676575)
  ·
    refine ⟨14996255426946941390514863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9997503617964627593676575 14996255426946941390514863)
    ·
      refine ⟨22494383140420412085772295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14996255426946941390514863 22494383140420412085772295)
      ·
        refine ⟨33741574710630618128658443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22494383140420412085772295 33741574710630618128658443)
        ·
          refine ⟨50612362065945927192987665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33741574710630618128658443 50612362065945927192987665)
          ·
            refine ⟨37959271549459445394740749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50612362065945927192987665 37959271549459445394740749)
            ·
              refine ⟨14234726831047292023027781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37959271549459445394740749 14234726831047292023027781)
              ·
                refine ⟨2669011280821367254317709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14234726831047292023027781 2669011280821367254317709)
                ·
                  refine ⟨1000879230308012720369141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2669011280821367254317709 1000879230308012720369141)
                  ·
                    refine ⟨93832427841376192534607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1000879230308012720369141 93832427841376192534607)
                    ·
                      rfl

theorem cell22_274107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_274107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274107 prefixEnd_274107 := by exact prefixLift 274107
  have htrace : WordTrace (prefixWord ++ tailWord_274107) baseStart_274107 baseEnd_274107 := by
    simpa [prefixWord, tailWord_274107, baseEnd_274107] using wordTrace_append hprefix tailTrace_274107
  have hstable : (prefixWord ++ tailWord_274107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274107).length < 2 ^ (prefixWord ++ tailWord_274107).sum := by decide
  have hdescent : baseEnd_274107 < baseStart_274107 := by decide
  rcases family_descends (prefixWord ++ tailWord_274107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274109 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 6]
def baseStart_274109 : Nat := 118140960795 + 274109 * 2 ^ 59
def prefixEnd_274109 : Nat := 4983230072969 + 3 ^ 40 * 274109 * 2
def baseEnd_274109 : Nat := 31277704160749617994867

theorem tailTrace_274109 : CollatzResearch.WordTrace tailWord_274109 prefixEnd_274109 31277704160749617994867 := by
  unfold tailWord_274109
  simp only [CollatzResearch.WordTrace]
  refine ⟨9997576563957381935249381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6665051042638254623499587 9997576563957381935249381)
  ·
    refine ⟨1874545605742009112859259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9997576563957381935249381 1874545605742009112859259)
    ·
      refine ⟨2811818408613013669288889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1874545605742009112859259 2811818408613013669288889)
      ·
        refine ⟨2108863806459760251966667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2811818408613013669288889 2108863806459760251966667)
        ·
          refine ⟨3163295709689640377950001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108863806459760251966667 3163295709689640377950001)
          ·
            refine ⟨2372471782267230283462501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3163295709689640377950001 2372471782267230283462501)
            ·
              refine ⟨444838459175105678149219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2372471782267230283462501 444838459175105678149219)
              ·
                refine ⟨667257688762658517223829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444838459175105678149219 667257688762658517223829)
                ·
                  refine ⟨31277704160749617994867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 667257688762658517223829 31277704160749617994867)
                  ·
                    rfl

theorem cell22_274109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_274109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274109 prefixEnd_274109 := by exact prefixLift 274109
  have htrace : WordTrace (prefixWord ++ tailWord_274109) baseStart_274109 baseEnd_274109 := by
    simpa [prefixWord, tailWord_274109, baseEnd_274109] using wordTrace_append hprefix tailTrace_274109
  have hstable : (prefixWord ++ tailWord_274109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274109).length < 2 ^ (prefixWord ++ tailWord_274109).sum := by decide
  have hdescent : baseEnd_274109 < baseStart_274109 := by decide
  rcases family_descends (prefixWord ++ tailWord_274109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274216 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 5]
def baseStart_274216 : Nat := 118140960795 + 274216 * 2 ^ 59
def prefixEnd_274216 : Nat := 4983230072969 + 3 ^ 40 * 274216 * 2
def baseEnd_274216 : Nat := 31289913589645413853091

theorem tailTrace_274216 : CollatzResearch.WordTrace tailWord_274216 prefixEnd_274216 31289913589645413853091 := by
  unfold tailWord_274216
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000739587284869604697251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6667652783046492806263001 5000739587284869604697251)
  ·
    refine ⟨7501109380927304407045877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5000739587284869604697251 7501109380927304407045877)
    ·
      refine ⟨703229004461934788160551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7501109380927304407045877 703229004461934788160551)
      ·
        refine ⟨1054843506692902182240827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703229004461934788160551 1054843506692902182240827)
        ·
          refine ⟨1582265260039353273361241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054843506692902182240827 1582265260039353273361241)
          ·
            refine ⟨1186698945029514955020931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1582265260039353273361241 1186698945029514955020931)
            ·
              refine ⟨1780048417544272432531397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186698945029514955020931 1780048417544272432531397)
              ·
                refine ⟨333759078289551081099637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1780048417544272432531397 333759078289551081099637)
                ·
                  refine ⟨31289913589645413853091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 333759078289551081099637 31289913589645413853091)
                  ·
                    rfl

theorem cell22_274216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_274216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274216 prefixEnd_274216 := by exact prefixLift 274216
  have htrace : WordTrace (prefixWord ++ tailWord_274216) baseStart_274216 baseEnd_274216 := by
    simpa [prefixWord, tailWord_274216, baseEnd_274216] using wordTrace_append hprefix tailTrace_274216
  have hstable : (prefixWord ++ tailWord_274216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274216).length < 2 ^ (prefixWord ++ tailWord_274216).sum := by decide
  have hdescent : baseEnd_274216 < baseStart_274216 := by decide
  rcases family_descends (prefixWord ++ tailWord_274216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274220 : List Nat := [2, 2, 1, 1, 1, 5, 4, 2, 1, 3]
def baseStart_274220 : Nat := 118140960795 + 274220 * 2 ^ 59
def prefixEnd_274220 : Nat := 4983230072969 + 3 ^ 40 * 274220 * 2
def baseEnd_274220 : Nat := 93871110050681564459261

theorem tailTrace_274220 : CollatzResearch.WordTrace tailWord_274220 prefixEnd_274220 93871110050681564459261 := by
  unfold tailWord_274220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000812533277623946270057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6667750044370165261693409 5000812533277623946270057)
  ·
    refine ⟨3750609399958217959702543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5000812533277623946270057 3750609399958217959702543)
    ·
      refine ⟨5625914099937326939553815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3750609399958217959702543 5625914099937326939553815)
      ·
        refine ⟨8438871149905990409330723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625914099937326939553815 8438871149905990409330723)
        ·
          refine ⟨12658306724858985613996085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8438871149905990409330723 12658306724858985613996085)
          ·
            refine ⟨1186716255455529901312133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12658306724858985613996085 1186716255455529901312133)
            ·
              refine ⟨222509297897911856496025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1186716255455529901312133 222509297897911856496025)
              ·
                refine ⟨166881973423433892372019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222509297897911856496025 166881973423433892372019)
                ·
                  refine ⟨250322960135150838558029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166881973423433892372019 250322960135150838558029)
                  ·
                    refine ⟨93871110050681564459261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250322960135150838558029 93871110050681564459261)
                    ·
                      rfl

theorem cell22_274220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_274220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274220 prefixEnd_274220 := by exact prefixLift 274220
  have htrace : WordTrace (prefixWord ++ tailWord_274220) baseStart_274220 baseEnd_274220 := by
    simpa [prefixWord, tailWord_274220, baseEnd_274220] using wordTrace_append hprefix tailTrace_274220
  have hstable : (prefixWord ++ tailWord_274220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274220).length < 2 ^ (prefixWord ++ tailWord_274220).sum := by decide
  have hdescent : baseEnd_274220 < baseStart_274220 := by decide
  rcases family_descends (prefixWord ++ tailWord_274220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274263 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 1, 4]
def baseStart_274263 : Nat := 118140960795 + 274263 * 2 ^ 59
def prefixEnd_274263 : Nat := 4983230072969 + 3 ^ 40 * 274263 * 2
def baseEnd_274263 : Nat := 93885829829443785634129

theorem tailTrace_274263 : CollatzResearch.WordTrace tailWord_274263 prefixEnd_274263 93885829829443785634129 := by
  unfold tailWord_274263
  simp only [CollatzResearch.WordTrace]
  refine ⟨10003193405399466236355443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6668795603599644157570295 10003193405399466236355443)
  ·
    refine ⟨15004790108099199354533165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10003193405399466236355443 15004790108099199354533165)
    ·
      refine ⟨5626796290537199757949937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15004790108099199354533165 5626796290537199757949937)
      ·
        refine ⟨4220097217902899818462453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5626796290537199757949937 4220097217902899818462453)
        ·
          refine ⟨395634114178396857980855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4220097217902899818462453 395634114178396857980855)
          ·
            refine ⟨593451171267595286971283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395634114178396857980855 593451171267595286971283)
            ·
              refine ⟨890176756901392930456925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593451171267595286971283 890176756901392930456925)
              ·
                refine ⟨333816283838022348921347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 890176756901392930456925 333816283838022348921347)
                ·
                  refine ⟨500724425757033523382021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333816283838022348921347 500724425757033523382021)
                  ·
                    refine ⟨93885829829443785634129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 500724425757033523382021 93885829829443785634129)
                    ·
                      rfl

theorem cell22_274263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_274263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274263 prefixEnd_274263 := by exact prefixLift 274263
  have htrace : WordTrace (prefixWord ++ tailWord_274263) baseStart_274263 baseEnd_274263 := by
    simpa [prefixWord, tailWord_274263, baseEnd_274263] using wordTrace_append hprefix tailTrace_274263
  have hstable : (prefixWord ++ tailWord_274263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274263).length < 2 ^ (prefixWord ++ tailWord_274263).sum := by decide
  have hdescent : baseEnd_274263 < baseStart_274263 := by decide
  rcases family_descends (prefixWord ++ tailWord_274263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274289 : List Nat := [1, 2, 2, 2, 1, 3, 2, 9]
def baseStart_274289 : Nat := 118140960795 + 274289 * 2 ^ 59
def prefixEnd_274289 : Nat := 4983230072969 + 3 ^ 40 * 274289 * 2
def baseEnd_274289 : Nat := 10432747795643153831561

theorem tailTrace_274289 : CollatzResearch.WordTrace tailWord_274289 prefixEnd_274289 10432747795643153831561 := by
  unfold tailWord_274289
  simp only [CollatzResearch.WordTrace]
  refine ⟨10004141703305272676801921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6669427802203515117867947 10004141703305272676801921)
  ·
    refine ⟨7503106277478954507601441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10004141703305272676801921 7503106277478954507601441)
    ·
      refine ⟨5627329708109215880701081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7503106277478954507601441 5627329708109215880701081)
      ·
        refine ⟨4220497281081911910525811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5627329708109215880701081 4220497281081911910525811)
        ·
          refine ⟨6330745921622867865788717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220497281081911910525811 6330745921622867865788717)
          ·
            refine ⟨2374029720608575449670769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6330745921622867865788717 2374029720608575449670769)
            ·
              refine ⟨1780522290456431587253077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2374029720608575449670769 1780522290456431587253077)
              ·
                refine ⟨10432747795643153831561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1780522290456431587253077 10432747795643153831561)
                ·
                  rfl

theorem cell22_274289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 9].length) (baseStart_274289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274289 prefixEnd_274289 := by exact prefixLift 274289
  have htrace : WordTrace (prefixWord ++ tailWord_274289) baseStart_274289 baseEnd_274289 := by
    simpa [prefixWord, tailWord_274289, baseEnd_274289] using wordTrace_append hprefix tailTrace_274289
  have hstable : (prefixWord ++ tailWord_274289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274289).length < 2 ^ (prefixWord ++ tailWord_274289).sum := by decide
  have hdescent : baseEnd_274289 < baseStart_274289 := by decide
  rcases family_descends (prefixWord ++ tailWord_274289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274304 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_274304 : Nat := 118140960795 + 274304 * 2 ^ 59
def prefixEnd_274304 : Nat := 4983230072969 + 3 ^ 40 * 274304 * 2
def baseEnd_274304 : Nat := 93899864967333345359003

theorem tailTrace_274304 : CollatzResearch.WordTrace tailWord_274304 prefixEnd_274304 93899864967333345359003 := by
  unfold tailWord_274304
  simp only [CollatzResearch.WordTrace]
  refine ⟨5002344399125465119298983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6669792532167286825731977 5002344399125465119298983)
  ·
    refine ⟨7503516598688197678948475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5002344399125465119298983 7503516598688197678948475)
    ·
      refine ⟨11255274898032296518422713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7503516598688197678948475 11255274898032296518422713)
      ·
        refine ⟨8441456173524222388817035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11255274898032296518422713 8441456173524222388817035)
        ·
          refine ⟨12662184260286333583225553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8441456173524222388817035 12662184260286333583225553)
          ·
            refine ⟨9496638195214750187419165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12662184260286333583225553 9496638195214750187419165)
            ·
              refine ⟨3561239323205531320282187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9496638195214750187419165 3561239323205531320282187)
              ·
                refine ⟨5341858984808296980423281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561239323205531320282187 5341858984808296980423281)
                ·
                  refine ⟨4006394238606222735317461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5341858984808296980423281 4006394238606222735317461)
                  ·
                    refine ⟨93899864967333345359003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4006394238606222735317461 93899864967333345359003)
                    ·
                      rfl

theorem cell22_274304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_274304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274304 prefixEnd_274304 := by exact prefixLift 274304
  have htrace : WordTrace (prefixWord ++ tailWord_274304) baseStart_274304 baseEnd_274304 := by
    simpa [prefixWord, tailWord_274304, baseEnd_274304] using wordTrace_append hprefix tailTrace_274304
  have hstable : (prefixWord ++ tailWord_274304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274304).length < 2 ^ (prefixWord ++ tailWord_274304).sum := by decide
  have hdescent : baseEnd_274304 < baseStart_274304 := by decide
  rcases family_descends (prefixWord ++ tailWord_274304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274312 : List Nat := [2, 1, 3, 3, 4, 1, 1, 3, 4]
def baseStart_274312 : Nat := 118140960795 + 274312 * 2 ^ 59
def prefixEnd_274312 : Nat := 4983230072969 + 3 ^ 40 * 274312 * 2
def baseEnd_274312 : Nat := 31300867843607997052993

theorem tailTrace_274312 : CollatzResearch.WordTrace tailWord_274312 prefixEnd_274312 31300867843607997052993 := by
  unfold tailWord_274312
  simp only [CollatzResearch.WordTrace]
  refine ⟨5002490291110973802444595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6669987054814631736592793 5002490291110973802444595)
  ·
    refine ⟨7503735436666460703666893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5002490291110973802444595 7503735436666460703666893)
    ·
      refine ⟨2813900788749922763875085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7503735436666460703666893 2813900788749922763875085)
      ·
        refine ⟨1055212795781221036453157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2813900788749922763875085 1055212795781221036453157)
        ·
          refine ⟨197852399208978944334967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1055212795781221036453157 197852399208978944334967)
          ·
            refine ⟨296778598813468416502451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197852399208978944334967 296778598813468416502451)
            ·
              refine ⟨445167898220202624753677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296778598813468416502451 445167898220202624753677)
              ·
                refine ⟨166937961832575984282629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 445167898220202624753677 166937961832575984282629)
                ·
                  refine ⟨31300867843607997052993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166937961832575984282629 31300867843607997052993)
                  ·
                    rfl

theorem cell22_274312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 4].length) (baseStart_274312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274312 prefixEnd_274312 := by exact prefixLift 274312
  have htrace : WordTrace (prefixWord ++ tailWord_274312) baseStart_274312 baseEnd_274312 := by
    simpa [prefixWord, tailWord_274312, baseEnd_274312] using wordTrace_append hprefix tailTrace_274312
  have hstable : (prefixWord ++ tailWord_274312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274312).length < 2 ^ (prefixWord ++ tailWord_274312).sum := by decide
  have hdescent : baseEnd_274312 < baseStart_274312 := by decide
  rcases family_descends (prefixWord ++ tailWord_274312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274321 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 5, 3]
def baseStart_274321 : Nat := 118140960795 + 274321 * 2 ^ 59
def prefixEnd_274321 : Nat := 4983230072969 + 3 ^ 40 * 274321 * 2
def baseEnd_274321 : Nat := 93905684414750967683951

theorem tailTrace_274321 : CollatzResearch.WordTrace tailWord_274321 prefixEnd_274321 93905684414750967683951 := by
  unfold tailWord_274321
  simp only [CollatzResearch.WordTrace]
  refine ⟨10005308839189342141966817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6670205892792894761311211 10005308839189342141966817)
  ·
    refine ⟨7503981629392006606475113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10005308839189342141966817 7503981629392006606475113)
    ·
      refine ⟨5627986222044004954856335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7503981629392006606475113 5627986222044004954856335)
      ·
        refine ⟨8441979333066007432284503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5627986222044004954856335 8441979333066007432284503)
        ·
          refine ⟨12662968999599011148426755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8441979333066007432284503 12662968999599011148426755)
          ·
            refine ⟨18994453499398516722640133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12662968999599011148426755 18994453499398516722640133)
            ·
              refine ⟨3561460031137221885495025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18994453499398516722640133 3561460031137221885495025)
              ·
                refine ⟨2671095023352916414121269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561460031137221885495025 2671095023352916414121269)
                ·
                  refine ⟨250415158439335913823869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2671095023352916414121269 250415158439335913823869)
                  ·
                    refine ⟨93905684414750967683951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250415158439335913823869 93905684414750967683951)
                    ·
                      rfl

theorem cell22_274321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_274321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274321 prefixEnd_274321 := by exact prefixLift 274321
  have htrace : WordTrace (prefixWord ++ tailWord_274321) baseStart_274321 baseEnd_274321 := by
    simpa [prefixWord, tailWord_274321, baseEnd_274321] using wordTrace_append hprefix tailTrace_274321
  have hstable : (prefixWord ++ tailWord_274321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274321).length < 2 ^ (prefixWord ++ tailWord_274321).sum := by decide
  have hdescent : baseEnd_274321 < baseStart_274321 := by decide
  rcases family_descends (prefixWord ++ tailWord_274321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274351 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 5]
def baseStart_274351 : Nat := 118140960795 + 274351 * 2 ^ 59
def prefixEnd_274351 : Nat := 4983230072969 + 3 ^ 40 * 274351 * 2
def baseEnd_274351 : Nat := 31305318009280296477953

theorem tailTrace_274351 : CollatzResearch.WordTrace tailWord_274351 prefixEnd_274351 31305318009280296477953 := by
  unfold tailWord_274351
  simp only [CollatzResearch.WordTrace]
  refine ⟨10006403029080657265558907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6670935352720438177039271 10006403029080657265558907)
  ·
    refine ⟨15009604543620985898338361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10006403029080657265558907 15009604543620985898338361)
    ·
      refine ⟨11257203407715739423753771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15009604543620985898338361 11257203407715739423753771)
      ·
        refine ⟨16885805111573609135630657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11257203407715739423753771 16885805111573609135630657)
        ·
          refine ⟨12664353833680206851722993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16885805111573609135630657 12664353833680206851722993)
          ·
            refine ⟨9498265375260155138792245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12664353833680206851722993 9498265375260155138792245)
            ·
              refine ⟨890462378930639544261773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9498265375260155138792245 890462378930639544261773)
              ·
                refine ⟨333923392098989829098165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 890462378930639544261773 333923392098989829098165)
                ·
                  refine ⟨31305318009280296477953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 333923392098989829098165 31305318009280296477953)
                  ·
                    rfl

theorem cell22_274351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 5].length) (baseStart_274351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274351 prefixEnd_274351 := by exact prefixLift 274351
  have htrace : WordTrace (prefixWord ++ tailWord_274351) baseStart_274351 baseEnd_274351 := by
    simpa [prefixWord, tailWord_274351, baseEnd_274351] using wordTrace_append hprefix tailTrace_274351
  have hstable : (prefixWord ++ tailWord_274351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274351).length < 2 ^ (prefixWord ++ tailWord_274351).sum := by decide
  have hdescent : baseEnd_274351 < baseStart_274351 := by decide
  rcases family_descends (prefixWord ++ tailWord_274351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274389 : List Nat := [1, 3, 2, 3, 2, 3, 2, 2, 1, 3]
def baseStart_274389 : Nat := 118140960795 + 274389 * 2 ^ 59
def prefixEnd_274389 : Nat := 4983230072969 + 3 ^ 40 * 274389 * 2
def baseEnd_274389 : Nat := 93928962204421456983743

theorem tailTrace_274389 : CollatzResearch.WordTrace tailWord_274389 prefixEnd_274389 93928962204421456983743 := by
  unfold tailWord_274389
  simp only [CollatzResearch.WordTrace]
  refine ⟨10007789002942989755442221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6671859335295326503628147 10007789002942989755442221)
  ·
    refine ⟨3752920876103621158290833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10007789002942989755442221 3752920876103621158290833)
    ·
      refine ⟨2814690657077715868718125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3752920876103621158290833 2814690657077715868718125)
      ·
        refine ⟨1055508996404143450769297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2814690657077715868718125 1055508996404143450769297)
        ·
          refine ⟨791631747303107588076973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055508996404143450769297 791631747303107588076973)
          ·
            refine ⟨296861905238665345528865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 791631747303107588076973 296861905238665345528865)
            ·
              refine ⟨222646428928999009146649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296861905238665345528865 222646428928999009146649)
              ·
                refine ⟨166984821696749256859987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222646428928999009146649 166984821696749256859987)
                ·
                  refine ⟨250477232545123885289981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166984821696749256859987 250477232545123885289981)
                  ·
                    refine ⟨93928962204421456983743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250477232545123885289981 93928962204421456983743)
                    ·
                      rfl

theorem cell22_274389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_274389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274389 prefixEnd_274389 := by exact prefixLift 274389
  have htrace : WordTrace (prefixWord ++ tailWord_274389) baseStart_274389 baseEnd_274389 := by
    simpa [prefixWord, tailWord_274389, baseEnd_274389] using wordTrace_append hprefix tailTrace_274389
  have hstable : (prefixWord ++ tailWord_274389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274389).length < 2 ^ (prefixWord ++ tailWord_274389).sum := by decide
  have hdescent : baseEnd_274389 < baseStart_274389 := by decide
  rcases family_descends (prefixWord ++ tailWord_274389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274428 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 4, 3]
def baseStart_274428 : Nat := 118140960795 + 274428 * 2 ^ 59
def prefixEnd_274428 : Nat := 4983230072969 + 3 ^ 40 * 274428 * 2
def baseEnd_274428 : Nat := 93942312701438355258623

theorem tailTrace_274428 : CollatzResearch.WordTrace tailWord_274428 prefixEnd_274428 93942312701438355258623 := by
  unfold tailWord_274428
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004605724900849708055969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6672807633201132944074625 5004605724900849708055969)
  ·
    refine ⟨3753454293675637281041977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5004605724900849708055969 3753454293675637281041977)
    ·
      refine ⟨2815090720256727960781483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3753454293675637281041977 2815090720256727960781483)
      ·
        refine ⟨4222636080385091941172225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2815090720256727960781483 4222636080385091941172225)
        ·
          refine ⟨3166977060288818955879169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4222636080385091941172225 3166977060288818955879169)
          ·
            refine ⟨2375232795216614216909377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166977060288818955879169 2375232795216614216909377)
            ·
              refine ⟨1781424596412460662682033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2375232795216614216909377 1781424596412460662682033)
              ·
                refine ⟨1336068447309345497011525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781424596412460662682033 1336068447309345497011525)
                ·
                  refine ⟨250512833870502280689661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1336068447309345497011525 250512833870502280689661)
                  ·
                    refine ⟨93942312701438355258623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250512833870502280689661 93942312701438355258623)
                    ·
                      rfl

theorem cell22_274428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_274428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274428 prefixEnd_274428 := by exact prefixLift 274428
  have htrace : WordTrace (prefixWord ++ tailWord_274428) baseStart_274428 baseEnd_274428 := by
    simpa [prefixWord, tailWord_274428, baseEnd_274428] using wordTrace_append hprefix tailTrace_274428
  have hstable : (prefixWord ++ tailWord_274428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274428).length < 2 ^ (prefixWord ++ tailWord_274428).sum := by decide
  have hdescent : baseEnd_274428 < baseStart_274428 := by decide
  rcases family_descends (prefixWord ++ tailWord_274428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274503 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 5]
def baseStart_274503 : Nat := 118140960795 + 274503 * 2 ^ 59
def prefixEnd_274503 : Nat := 4983230072969 + 3 ^ 40 * 274503 * 2
def baseEnd_274503 : Nat := 31322662244721053211131

theorem tailTrace_274503 : CollatzResearch.WordTrace tailWord_274503 prefixEnd_274503 31322662244721053211131 := by
  unfold tailWord_274503
  simp only [CollatzResearch.WordTrace]
  refine ⟨10011946924529987225092163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6674631283019991483394775 10011946924529987225092163)
  ·
    refine ⟨15017920386794980837638245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10011946924529987225092163 15017920386794980837638245)
    ·
      refine ⟨2815860072524058907057171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15017920386794980837638245 2815860072524058907057171)
      ·
        refine ⟨4223790108786088360585757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2815860072524058907057171 4223790108786088360585757)
        ·
          refine ⟨1583921290794783135219659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4223790108786088360585757 1583921290794783135219659)
          ·
            refine ⟨2375881936192174702829489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583921290794783135219659 2375881936192174702829489)
            ·
              refine ⟨1781911452144131027122117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2375881936192174702829489 1781911452144131027122117)
              ·
                refine ⟨334108397277024567585397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1781911452144131027122117 334108397277024567585397)
                ·
                  refine ⟨31322662244721053211131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 334108397277024567585397 31322662244721053211131)
                  ·
                    rfl

theorem cell22_274503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 5].length) (baseStart_274503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274503 prefixEnd_274503 := by exact prefixLift 274503
  have htrace : WordTrace (prefixWord ++ tailWord_274503) baseStart_274503 baseEnd_274503 := by
    simpa [prefixWord, tailWord_274503, baseEnd_274503] using wordTrace_append hprefix tailTrace_274503
  have hstable : (prefixWord ++ tailWord_274503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274503).length < 2 ^ (prefixWord ++ tailWord_274503).sum := by decide
  have hdescent : baseEnd_274503 < baseStart_274503 := by decide
  rcases family_descends (prefixWord ++ tailWord_274503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274520 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 5]
def baseStart_274520 : Nat := 118140960795 + 274520 * 2 ^ 59
def prefixEnd_274520 : Nat := 4983230072969 + 3 ^ 40 * 274520 * 2
def baseEnd_274520 : Nat := 31324602060526927319447

theorem tailTrace_274520 : CollatzResearch.WordTrace tailWord_274520 prefixEnd_274520 31324602060526927319447 := by
  unfold tailWord_274520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006283482734199564230507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6675044643645599418974009 5006283482734199564230507)
  ·
    refine ⟨7509425224101299346345761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5006283482734199564230507 7509425224101299346345761)
    ·
      refine ⟨5632068918075974509759321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7509425224101299346345761 5632068918075974509759321)
      ·
        refine ⟨4224051688556980882319491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5632068918075974509759321 4224051688556980882319491)
        ·
          refine ⟨6336077532835471323479237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224051688556980882319491 6336077532835471323479237)
          ·
            refine ⟨1188014537406650873152357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6336077532835471323479237 1188014537406650873152357)
            ·
              refine ⟨222752725763747038716067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1188014537406650873152357 222752725763747038716067)
              ·
                refine ⟨334129088645620558074101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222752725763747038716067 334129088645620558074101)
                ·
                  refine ⟨31324602060526927319447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 334129088645620558074101 31324602060526927319447)
                  ·
                    rfl

theorem cell22_274520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 5].length) (baseStart_274520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274520 prefixEnd_274520 := by exact prefixLift 274520
  have htrace : WordTrace (prefixWord ++ tailWord_274520) baseStart_274520 baseEnd_274520 := by
    simpa [prefixWord, tailWord_274520, baseEnd_274520] using wordTrace_append hprefix tailTrace_274520
  have hstable : (prefixWord ++ tailWord_274520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274520).length < 2 ^ (prefixWord ++ tailWord_274520).sum := by decide
  have hdescent : baseEnd_274520 < baseStart_274520 := by decide
  rcases family_descends (prefixWord ++ tailWord_274520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274599 : List Nat := [1, 1, 6, 2, 2, 1, 2, 3, 4]
def baseStart_274599 : Nat := 118140960795 + 274599 * 2 ^ 59
def prefixEnd_274599 : Nat := 4983230072969 + 3 ^ 40 * 274599 * 2
def baseEnd_274599 : Nat := 31333616498683636411033

theorem tailTrace_274599 : CollatzResearch.WordTrace tailWord_274599 prefixEnd_274599 31333616498683636411033 := by
  unfold tailWord_274599
  simp only [CollatzResearch.WordTrace]
  refine ⟨10015448332182195620586851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6676965554788130413724567 10015448332182195620586851)
  ·
    refine ⟨15023172498273293430880277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10015448332182195620586851 15023172498273293430880277)
    ·
      refine ⟨704211210856560629572513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15023172498273293430880277 704211210856560629572513)
      ·
        refine ⟨528158408142420472179385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704211210856560629572513 528158408142420472179385)
        ·
          refine ⟨396118806106815354134539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528158408142420472179385 396118806106815354134539)
          ·
            refine ⟨594178209160223031201809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396118806106815354134539 594178209160223031201809)
            ·
              refine ⟨445633656870167273401357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594178209160223031201809 445633656870167273401357)
              ·
                refine ⟨167112621326312727525509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 445633656870167273401357 167112621326312727525509)
                ·
                  refine ⟨31333616498683636411033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167112621326312727525509 31333616498683636411033)
                  ·
                    rfl

theorem cell22_274599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 4].length) (baseStart_274599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274599 prefixEnd_274599 := by exact prefixLift 274599
  have htrace : WordTrace (prefixWord ++ tailWord_274599) baseStart_274599 baseEnd_274599 := by
    simpa [prefixWord, tailWord_274599, baseEnd_274599] using wordTrace_append hprefix tailTrace_274599
  have hstable : (prefixWord ++ tailWord_274599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274599).length < 2 ^ (prefixWord ++ tailWord_274599).sum := by decide
  have hdescent : baseEnd_274599 < baseStart_274599 := by decide
  rcases family_descends (prefixWord ++ tailWord_274599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274642 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_274642 : Nat := 118140960795 + 274642 * 2 ^ 59
def prefixEnd_274642 : Nat := 4983230072969 + 3 ^ 40 * 274642 * 2
def baseEnd_274642 : Nat := 94015569274813130407967

theorem tailTrace_274642 : CollatzResearch.WordTrace tailWord_274642 prefixEnd_274642 94015569274813130407967 := by
  unfold tailWord_274642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2504254167756603491100545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6678011114017609309601453 2504254167756603491100545)
  ·
    refine ⟨1878190625817452618325409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2504254167756603491100545 1878190625817452618325409)
    ·
      refine ⟨1408642969363089463744057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1878190625817452618325409 1408642969363089463744057)
      ·
        refine ⟨1056482227022317097808043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1408642969363089463744057 1056482227022317097808043)
        ·
          refine ⟨1584723340533475646712065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056482227022317097808043 1584723340533475646712065)
          ·
            refine ⟨1188542505400106735034049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1584723340533475646712065 1188542505400106735034049)
            ·
              refine ⟨891406879050080051275537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188542505400106735034049 891406879050080051275537)
              ·
                refine ⟨668555159287560038456653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891406879050080051275537 668555159287560038456653)
                ·
                  refine ⟨250708184732835014421245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668555159287560038456653 250708184732835014421245)
                  ·
                    refine ⟨94015569274813130407967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250708184732835014421245 94015569274813130407967)
                    ·
                      rfl

theorem cell22_274642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_274642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274642 prefixEnd_274642 := by exact prefixLift 274642
  have htrace : WordTrace (prefixWord ++ tailWord_274642) baseStart_274642 baseEnd_274642 := by
    simpa [prefixWord, tailWord_274642, baseEnd_274642] using wordTrace_append hprefix tailTrace_274642
  have hstable : (prefixWord ++ tailWord_274642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274642).length < 2 ^ (prefixWord ++ tailWord_274642).sum := by decide
  have hdescent : baseEnd_274642 < baseStart_274642 := by decide
  rcases family_descends (prefixWord ++ tailWord_274642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274715 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 6, 3]
def baseStart_274715 : Nat := 118140960795 + 274715 * 2 ^ 59
def prefixEnd_274715 : Nat := 4983230072969 + 3 ^ 40 * 274715 * 2
def baseEnd_274715 : Nat := 94040558666665273332743

theorem tailTrace_274715 : CollatzResearch.WordTrace tailWord_274715 prefixEnd_274715 94040558666665273332743 := by
  unfold tailWord_274715
  simp only [CollatzResearch.WordTrace]
  refine ⟨10019679199761947431809599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6679786133174631621206399 10019679199761947431809599)
  ·
    refine ⟨15029518799642921147714399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10019679199761947431809599 15029518799642921147714399)
    ·
      refine ⟨22544278199464381721571599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15029518799642921147714399 22544278199464381721571599)
      ·
        refine ⟨33816417299196572582357399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22544278199464381721571599 33816417299196572582357399)
        ·
          refine ⟨50724625948794858873536099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33816417299196572582357399 50724625948794858873536099)
          ·
            refine ⟨76086938923192288310304149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50724625948794858873536099 76086938923192288310304149)
            ·
              refine ⟨3566575262024638514545507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76086938923192288310304149 3566575262024638514545507)
              ·
                refine ⟨5349862893036957771818261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3566575262024638514545507 5349862893036957771818261)
                ·
                  refine ⟨250774823111107395553981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5349862893036957771818261 250774823111107395553981)
                  ·
                    refine ⟨94040558666665273332743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250774823111107395553981 94040558666665273332743)
                    ·
                      rfl

theorem cell22_274715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 3].length) (baseStart_274715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274715 prefixEnd_274715 := by exact prefixLift 274715
  have htrace : WordTrace (prefixWord ++ tailWord_274715) baseStart_274715 baseEnd_274715 := by
    simpa [prefixWord, tailWord_274715, baseEnd_274715] using wordTrace_append hprefix tailTrace_274715
  have hstable : (prefixWord ++ tailWord_274715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274715).length < 2 ^ (prefixWord ++ tailWord_274715).sum := by decide
  have hdescent : baseEnd_274715 < baseStart_274715 := by decide
  rcases family_descends (prefixWord ++ tailWord_274715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274719 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 1, 4]
def baseStart_274719 : Nat := 118140960795 + 274719 * 2 ^ 59
def prefixEnd_274719 : Nat := 4983230072969 + 3 ^ 40 * 274719 * 2
def baseEnd_274719 : Nat := 94041927948410596232731

theorem tailTrace_274719 : CollatzResearch.WordTrace tailWord_274719 prefixEnd_274719 94041927948410596232731 := by
  unfold tailWord_274719
  simp only [CollatzResearch.WordTrace]
  refine ⟨10019825091747456114955211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6679883394498304076636807 10019825091747456114955211)
  ·
    refine ⟨15029737637621184172432817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10019825091747456114955211 15029737637621184172432817)
    ·
      refine ⟨11272303228215888129324613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15029737637621184172432817 11272303228215888129324613)
      ·
        refine ⟨2113556855290479024248365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11272303228215888129324613 2113556855290479024248365)
        ·
          refine ⟨792583820733929634093137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2113556855290479024248365 792583820733929634093137)
          ·
            refine ⟨594437865550447225569853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792583820733929634093137 594437865550447225569853)
            ·
              refine ⟨222914199581417709588695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 594437865550447225569853 222914199581417709588695)
              ·
                refine ⟨334371299372126564383043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222914199581417709588695 334371299372126564383043)
                ·
                  refine ⟨501556949058189846574565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334371299372126564383043 501556949058189846574565)
                  ·
                    refine ⟨94041927948410596232731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 501556949058189846574565 94041927948410596232731)
                    ·
                      rfl

theorem cell22_274719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 4].length) (baseStart_274719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274719 prefixEnd_274719 := by exact prefixLift 274719
  have htrace : WordTrace (prefixWord ++ tailWord_274719) baseStart_274719 baseEnd_274719 := by
    simpa [prefixWord, tailWord_274719, baseEnd_274719] using wordTrace_append hprefix tailTrace_274719
  have hstable : (prefixWord ++ tailWord_274719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274719).length < 2 ^ (prefixWord ++ tailWord_274719).sum := by decide
  have hdescent : baseEnd_274719 < baseStart_274719 := by decide
  rcases family_descends (prefixWord ++ tailWord_274719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274727 : List Nat := [1, 1, 8, 1, 1, 2, 2, 2, 1, 3]
def baseStart_274727 : Nat := 118140960795 + 274727 * 2 ^ 59
def prefixEnd_274727 : Nat := 4983230072969 + 3 ^ 40 * 274727 * 2
def baseEnd_274727 : Nat := 94044666511901242032707

theorem tailTrace_274727 : CollatzResearch.WordTrace tailWord_274727 prefixEnd_274727 94044666511901242032707 := by
  unfold tailWord_274727
  simp only [CollatzResearch.WordTrace]
  refine ⟨10020116875718473481246435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6680077917145648987497623 10020116875718473481246435)
  ·
    refine ⟨15030175313577710221869653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10020116875718473481246435 15030175313577710221869653)
    ·
      refine ⟨176134866955988791662535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 15030175313577710221869653 176134866955988791662535)
      ·
        refine ⟨264202300433983187493803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176134866955988791662535 264202300433983187493803)
        ·
          refine ⟨396303450650974781240705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264202300433983187493803 396303450650974781240705)
          ·
            refine ⟨297227587988231085930529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396303450650974781240705 297227587988231085930529)
            ·
              refine ⟨222920690991173314447897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297227587988231085930529 222920690991173314447897)
              ·
                refine ⟨167190518243379985835923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222920690991173314447897 167190518243379985835923)
                ·
                  refine ⟨250785777365069978753885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167190518243379985835923 250785777365069978753885)
                  ·
                    refine ⟨94044666511901242032707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250785777365069978753885 94044666511901242032707)
                    ·
                      rfl

theorem cell22_274727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_274727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274727 prefixEnd_274727 := by exact prefixLift 274727
  have htrace : WordTrace (prefixWord ++ tailWord_274727) baseStart_274727 baseEnd_274727 := by
    simpa [prefixWord, tailWord_274727, baseEnd_274727] using wordTrace_append hprefix tailTrace_274727
  have hstable : (prefixWord ++ tailWord_274727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274727).length < 2 ^ (prefixWord ++ tailWord_274727).sum := by decide
  have hdescent : baseEnd_274727 < baseStart_274727 := by decide
  rcases family_descends (prefixWord ++ tailWord_274727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274732 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 2, 3]
def baseStart_274732 : Nat := 118140960795 + 274732 * 2 ^ 59
def prefixEnd_274732 : Nat := 4983230072969 + 3 ^ 40 * 274732 * 2
def baseEnd_274732 : Nat := 94046378114082895657691

theorem tailTrace_274732 : CollatzResearch.WordTrace tailWord_274732 prefixEnd_274732 94046378114082895657691 := by
  unfold tailWord_274732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5010149620350179667589225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6680199493800239556785633 5010149620350179667589225)
  ·
    refine ⟨3757612215262634750691919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5010149620350179667589225 3757612215262634750691919)
    ·
      refine ⟨5636418322893952126037879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3757612215262634750691919 5636418322893952126037879)
      ·
        refine ⟨8454627484340928189056819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5636418322893952126037879 8454627484340928189056819)
        ·
          refine ⟨12681941226511392283585229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8454627484340928189056819 12681941226511392283585229)
          ·
            refine ⟨4755727959941772106344461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12681941226511392283585229 4755727959941772106344461)
            ·
              refine ⟨1783397984978164539879173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4755727959941772106344461 1783397984978164539879173)
              ·
                refine ⟨334387122183405851227345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1783397984978164539879173 334387122183405851227345)
                ·
                  refine ⟨250790341637554388420509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334387122183405851227345 250790341637554388420509)
                  ·
                    refine ⟨94046378114082895657691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250790341637554388420509 94046378114082895657691)
                    ·
                      rfl

theorem cell22_274732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_274732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274732 prefixEnd_274732 := by exact prefixLift 274732
  have htrace : WordTrace (prefixWord ++ tailWord_274732) baseStart_274732 baseEnd_274732 := by
    simpa [prefixWord, tailWord_274732, baseEnd_274732] using wordTrace_append hprefix tailTrace_274732
  have hstable : (prefixWord ++ tailWord_274732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274732).length < 2 ^ (prefixWord ++ tailWord_274732).sum := by decide
  have hdescent : baseEnd_274732 < baseStart_274732 := by decide
  rcases family_descends (prefixWord ++ tailWord_274732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274794 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 3, 3]
def baseStart_274794 : Nat := 118140960795 + 274794 * 2 ^ 59
def prefixEnd_274794 : Nat := 4983230072969 + 3 ^ 40 * 274794 * 2
def baseEnd_274794 : Nat := 94067601981135400607501

theorem tailTrace_274794 : CollatzResearch.WordTrace tailWord_274794 prefixEnd_274794 94067601981135400607501 := by
  unfold tailWord_274794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505640141618935980983859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6681707044317162615956957 2505640141618935980983859)
  ·
    refine ⟨3758460212428403971475789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2505640141618935980983859 3758460212428403971475789)
    ·
      refine ⟨1409422579660651489303421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3758460212428403971475789 1409422579660651489303421)
      ·
        refine ⟨528533467372744308488783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1409422579660651489303421 528533467372744308488783)
        ·
          refine ⟨792800201059116462733175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528533467372744308488783 792800201059116462733175)
          ·
            refine ⟨1189200301588674694099763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792800201059116462733175 1189200301588674694099763)
            ·
              refine ⟨1783800452383012041149645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189200301588674694099763 1783800452383012041149645)
              ·
                refine ⟨668925169643629515431117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1783800452383012041149645 668925169643629515431117)
                ·
                  refine ⟨250846938616361068286669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668925169643629515431117 250846938616361068286669)
                  ·
                    refine ⟨94067601981135400607501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250846938616361068286669 94067601981135400607501)
                    ·
                      rfl

theorem cell22_274794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_274794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274794 prefixEnd_274794 := by exact prefixLift 274794
  have htrace : WordTrace (prefixWord ++ tailWord_274794) baseStart_274794 baseEnd_274794 := by
    simpa [prefixWord, tailWord_274794, baseEnd_274794] using wordTrace_append hprefix tailTrace_274794
  have hstable : (prefixWord ++ tailWord_274794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274794).length < 2 ^ (prefixWord ++ tailWord_274794).sum := by decide
  have hdescent : baseEnd_274794 < baseStart_274794 := by decide
  rcases family_descends (prefixWord ++ tailWord_274794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274852 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 6]
def baseStart_274852 : Nat := 118140960795 + 274852 * 2 ^ 59
def prefixEnd_274852 : Nat := 4983230072969 + 3 ^ 40 * 274852 * 2
def baseEnd_274852 : Nat := 31362485522147527552441

theorem tailTrace_274852 : CollatzResearch.WordTrace tailWord_274852 prefixEnd_274852 31362485522147527552441 := by
  unfold tailWord_274852
  simp only [CollatzResearch.WordTrace]
  refine ⟨5012338000132809914773405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6683117333510413219697873 5012338000132809914773405)
  ·
    refine ⟨1879626750049803718040027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5012338000132809914773405 1879626750049803718040027)
    ·
      refine ⟨2819440125074705577060041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1879626750049803718040027 2819440125074705577060041)
      ·
        refine ⟨2114580093806029182795031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2819440125074705577060041 2114580093806029182795031)
        ·
          refine ⟨3171870140709043774192547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2114580093806029182795031 3171870140709043774192547)
          ·
            refine ⟨4757805211063565661288821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3171870140709043774192547 4757805211063565661288821)
            ·
              refine ⟨446044238537209280745827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4757805211063565661288821 446044238537209280745827)
              ·
                refine ⟨669066357805813921118741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446044238537209280745827 669066357805813921118741)
                ·
                  refine ⟨31362485522147527552441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 669066357805813921118741 31362485522147527552441)
                  ·
                    rfl

theorem cell22_274852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_274852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274852 prefixEnd_274852 := by exact prefixLift 274852
  have htrace : WordTrace (prefixWord ++ tailWord_274852) baseStart_274852 baseEnd_274852 := by
    simpa [prefixWord, tailWord_274852, baseEnd_274852] using wordTrace_append hprefix tailTrace_274852
  have hstable : (prefixWord ++ tailWord_274852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274852).length < 2 ^ (prefixWord ++ tailWord_274852).sum := by decide
  have hdescent : baseEnd_274852 < baseStart_274852 := by decide
  rcases family_descends (prefixWord ++ tailWord_274852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274858 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_274858 : Nat := 118140960795 + 274858 * 2 ^ 59
def prefixEnd_274858 : Nat := 4983230072969 + 3 ^ 40 * 274858 * 2
def baseEnd_274858 : Nat := 31363170163020189002435

theorem tailTrace_274858 : CollatzResearch.WordTrace tailWord_274858 prefixEnd_274858 31363170163020189002435 := by
  unfold tailWord_274858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2506223709560970713566307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6683263225495921902843485 2506223709560970713566307)
  ·
    refine ⟨3759335564341456070349461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2506223709560970713566307 3759335564341456070349461)
    ·
      refine ⟨176218854578505753297631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3759335564341456070349461 176218854578505753297631)
      ·
        refine ⟨264328281867758629946447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176218854578505753297631 264328281867758629946447)
        ·
          refine ⟨396492422801637944919671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264328281867758629946447 396492422801637944919671)
          ·
            refine ⟨594738634202456917379507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396492422801637944919671 594738634202456917379507)
            ·
              refine ⟨892107951303685376069261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594738634202456917379507 892107951303685376069261)
              ·
                refine ⟨334540481738882016025973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 892107951303685376069261 334540481738882016025973)
                ·
                  refine ⟨31363170163020189002435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 334540481738882016025973 31363170163020189002435)
                  ·
                    rfl

theorem cell22_274858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_274858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274858 prefixEnd_274858 := by exact prefixLift 274858
  have htrace : WordTrace (prefixWord ++ tailWord_274858) baseStart_274858 baseEnd_274858 := by
    simpa [prefixWord, tailWord_274858, baseEnd_274858] using wordTrace_append hprefix tailTrace_274858
  have hstable : (prefixWord ++ tailWord_274858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274858).length < 2 ^ (prefixWord ++ tailWord_274858).sum := by decide
  have hdescent : baseEnd_274858 < baseStart_274858 := by decide
  rcases family_descends (prefixWord ++ tailWord_274858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274901 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 2, 3]
def baseStart_274901 : Nat := 118140960795 + 274901 * 2 ^ 59
def prefixEnd_274901 : Nat := 4983230072969 + 3 ^ 40 * 274901 * 2
def baseEnd_274901 : Nat := 94104230267822788182173

theorem tailTrace_274901 : CollatzResearch.WordTrace tailWord_274901 prefixEnd_274901 94104230267822788182173 := by
  unfold tailWord_274901
  simp only [CollatzResearch.WordTrace]
  refine ⟨10026463177088101198080557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6684308784725400798720371 10026463177088101198080557)
  ·
    refine ⟨3759923691408037949280209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10026463177088101198080557 3759923691408037949280209)
    ·
      refine ⟨2819942768556028461960157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3759923691408037949280209 2819942768556028461960157)
      ·
        refine ⟨1057478538208510673235059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2819942768556028461960157 1057478538208510673235059)
        ·
          refine ⟨1586217807312766009852589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057478538208510673235059 1586217807312766009852589)
          ·
            refine ⟨594831677742287253694721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1586217807312766009852589 594831677742287253694721)
            ·
              refine ⟨446123758306715440271041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594831677742287253694721 446123758306715440271041)
              ·
                refine ⟨334592818730036580203281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446123758306715440271041 334592818730036580203281)
                ·
                  refine ⟨250944614047527435152461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334592818730036580203281 250944614047527435152461)
                  ·
                    refine ⟨94104230267822788182173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250944614047527435152461 94104230267822788182173)
                    ·
                      rfl

theorem cell22_274901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_274901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274901 prefixEnd_274901 := by exact prefixLift 274901
  have htrace : WordTrace (prefixWord ++ tailWord_274901) baseStart_274901 baseEnd_274901 := by
    simpa [prefixWord, tailWord_274901, baseEnd_274901] using wordTrace_append hprefix tailTrace_274901
  have hstable : (prefixWord ++ tailWord_274901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274901).length < 2 ^ (prefixWord ++ tailWord_274901).sum := by decide
  have hdescent : baseEnd_274901 < baseStart_274901 := by decide
  rcases family_descends (prefixWord ++ tailWord_274901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274929 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 3, 3]
def baseStart_274929 : Nat := 118140960795 + 274929 * 2 ^ 59
def prefixEnd_274929 : Nat := 4983230072969 + 3 ^ 40 * 274929 * 2
def baseEnd_274929 : Nat := 94113815240040048482087

theorem tailTrace_274929 : CollatzResearch.WordTrace tailWord_274929 prefixEnd_274929 94113815240040048482087 := by
  unfold tailWord_274929
  simp only [CollatzResearch.WordTrace]
  refine ⟨10027484420986661980099841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6684989613991107986733227 10027484420986661980099841)
  ·
    refine ⟨7520613315739996485074881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10027484420986661980099841 7520613315739996485074881)
    ·
      refine ⟨5640459986804997363806161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7520613315739996485074881 5640459986804997363806161)
      ·
        refine ⟨4230344990103748022854621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5640459986804997363806161 4230344990103748022854621)
        ·
          refine ⟨1586379371288905508570483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4230344990103748022854621 1586379371288905508570483)
          ·
            refine ⟨2379569056933358262855725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586379371288905508570483 2379569056933358262855725)
            ·
              refine ⟨892338396350009348570897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2379569056933358262855725 892338396350009348570897)
              ·
                refine ⟨669253797262507011428173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892338396350009348570897 669253797262507011428173)
                ·
                  refine ⟨250970173973440129285565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669253797262507011428173 250970173973440129285565)
                  ·
                    refine ⟨94113815240040048482087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250970173973440129285565 94113815240040048482087)
                    ·
                      rfl

theorem cell22_274929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_274929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274929 prefixEnd_274929 := by exact prefixLift 274929
  have htrace : WordTrace (prefixWord ++ tailWord_274929) baseStart_274929 baseEnd_274929 := by
    simpa [prefixWord, tailWord_274929, baseEnd_274929] using wordTrace_append hprefix tailTrace_274929
  have hstable : (prefixWord ++ tailWord_274929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274929).length < 2 ^ (prefixWord ++ tailWord_274929).sum := by decide
  have hdescent : baseEnd_274929 < baseStart_274929 := by decide
  rcases family_descends (prefixWord ++ tailWord_274929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274933 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 2, 4]
def baseStart_274933 : Nat := 118140960795 + 274933 * 2 ^ 59
def prefixEnd_274933 : Nat := 4983230072969 + 3 ^ 40 * 274933 * 2
def baseEnd_274933 : Nat := 94115184521785371382075

theorem tailTrace_274933 : CollatzResearch.WordTrace tailWord_274933 prefixEnd_274933 94115184521785371382075 := by
  unfold tailWord_274933
  simp only [CollatzResearch.WordTrace]
  refine ⟨10027630312972170663245453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6685086875314780442163635 10027630312972170663245453)
  ·
    refine ⟨3760361367364563998717045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10027630312972170663245453 3760361367364563998717045)
    ·
      refine ⟨352533878190427874879723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3760361367364563998717045 352533878190427874879723)
      ·
        refine ⟨528800817285641812319585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352533878190427874879723 528800817285641812319585)
        ·
          refine ⟨396600612964231359239689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528800817285641812319585 396600612964231359239689)
          ·
            refine ⟨297450459723173519429767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396600612964231359239689 297450459723173519429767)
            ·
              refine ⟨446175689584760279144651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297450459723173519429767 446175689584760279144651)
              ·
                refine ⟨669263534377140418716977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446175689584760279144651 669263534377140418716977)
                ·
                  refine ⟨501947650782855314037733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 669263534377140418716977 501947650782855314037733)
                  ·
                    refine ⟨94115184521785371382075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 501947650782855314037733 94115184521785371382075)
                    ·
                      rfl

theorem cell22_274933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_274933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_274933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_274933 prefixEnd_274933 := by exact prefixLift 274933
  have htrace : WordTrace (prefixWord ++ tailWord_274933) baseStart_274933 baseEnd_274933 := by
    simpa [prefixWord, tailWord_274933, baseEnd_274933] using wordTrace_append hprefix tailTrace_274933
  have hstable : (prefixWord ++ tailWord_274933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274933).length < 2 ^ (prefixWord ++ tailWord_274933).sum := by decide
  have hdescent : baseEnd_274933 < baseStart_274933 := by decide
  rcases family_descends (prefixWord ++ tailWord_274933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275019 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 4, 3]
def baseStart_275019 : Nat := 118140960795 + 275019 * 2 ^ 59
def prefixEnd_275019 : Nat := 4983230072969 + 3 ^ 40 * 275019 * 2
def baseEnd_275019 : Nat := 94144624079309813731811

theorem tailTrace_275019 : CollatzResearch.WordTrace tailWord_275019 prefixEnd_275019 94144624079309813731811 := by
  unfold tailWord_275019
  simp only [CollatzResearch.WordTrace]
  refine ⟨10030766990660607350876111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6687177993773738233917407 10030766990660607350876111)
  ·
    refine ⟨15046150485990911026314167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10030766990660607350876111 15046150485990911026314167)
    ·
      refine ⟨22569225728986366539471251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15046150485990911026314167 22569225728986366539471251)
      ·
        refine ⟨33853838593479549809206877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22569225728986366539471251 33853838593479549809206877)
        ·
          refine ⟨12695189472554831178452579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33853838593479549809206877 12695189472554831178452579)
          ·
            refine ⟨19042784208832246767678869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12695189472554831178452579 19042784208832246767678869)
            ·
              refine ⟨892630509789011567234947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19042784208832246767678869 892630509789011567234947)
              ·
                refine ⟨1338945764683517350852421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892630509789011567234947 1338945764683517350852421)
                ·
                  refine ⟨251052330878159503284829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1338945764683517350852421 251052330878159503284829)
                  ·
                    refine ⟨94144624079309813731811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251052330878159503284829 94144624079309813731811)
                    ·
                      rfl

theorem cell22_275019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 3].length) (baseStart_275019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275019 prefixEnd_275019 := by exact prefixLift 275019
  have htrace : WordTrace (prefixWord ++ tailWord_275019) baseStart_275019 baseEnd_275019 := by
    simpa [prefixWord, tailWord_275019, baseEnd_275019] using wordTrace_append hprefix tailTrace_275019
  have hstable : (prefixWord ++ tailWord_275019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275019).length < 2 ^ (prefixWord ++ tailWord_275019).sum := by decide
  have hdescent : baseEnd_275019 < baseStart_275019 := by decide
  rcases family_descends (prefixWord ++ tailWord_275019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275021 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 6]
def baseStart_275021 : Nat := 118140960795 + 275021 * 2 ^ 59
def prefixEnd_275021 : Nat := 4983230072969 + 3 ^ 40 * 275021 * 2
def baseEnd_275021 : Nat := 31381769573394158393935

theorem tailTrace_275021 : CollatzResearch.WordTrace tailWord_275021 prefixEnd_275021 31381769573394158393935 := by
  unfold tailWord_275021
  simp only [CollatzResearch.WordTrace]
  refine ⟨10030839936653361692448917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6687226624435574461632611 10030839936653361692448917)
  ·
    refine ⟨470195622030626329333543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10030839936653361692448917 470195622030626329333543)
    ·
      refine ⟨705293433045939494000315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470195622030626329333543 705293433045939494000315)
      ·
        refine ⟨1057940149568909241000473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705293433045939494000315 1057940149568909241000473)
        ·
          refine ⟨793455112176681930750355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1057940149568909241000473 793455112176681930750355)
          ·
            refine ⟨1190182668265022896125533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793455112176681930750355 1190182668265022896125533)
            ·
              refine ⟨446318500599383586047075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1190182668265022896125533 446318500599383586047075)
              ·
                refine ⟨669477750899075379070613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446318500599383586047075 669477750899075379070613)
                ·
                  refine ⟨31381769573394158393935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 669477750899075379070613 31381769573394158393935)
                  ·
                    rfl

theorem cell22_275021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_275021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275021 prefixEnd_275021 := by exact prefixLift 275021
  have htrace : WordTrace (prefixWord ++ tailWord_275021) baseStart_275021 baseEnd_275021 := by
    simpa [prefixWord, tailWord_275021, baseEnd_275021] using wordTrace_append hprefix tailTrace_275021
  have hstable : (prefixWord ++ tailWord_275021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275021).length < 2 ^ (prefixWord ++ tailWord_275021).sum := by decide
  have hdescent : baseEnd_275021 < baseStart_275021 := by decide
  rcases family_descends (prefixWord ++ tailWord_275021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275032 : List Nat := [2, 1, 2, 2, 1, 2, 3, 9]
def baseStart_275032 : Nat := 118140960795 + 275032 * 2 ^ 59
def prefixEnd_275032 : Nat := 4983230072969 + 3 ^ 40 * 275032 * 2
def baseEnd_275032 : Nat := 10461008249442457017419

theorem tailTrace_275032 : CollatzResearch.WordTrace tailWord_275032 prefixEnd_275032 10461008249442457017419 := by
  unfold tailWord_275032
  simp only [CollatzResearch.WordTrace]
  refine ⟨5015620569806755285549675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6687494093075673714066233 5015620569806755285549675)
  ·
    refine ⟨7523430854710132928324513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5015620569806755285549675 7523430854710132928324513)
    ·
      refine ⟨5642573141032599696243385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7523430854710132928324513 5642573141032599696243385)
      ·
        refine ⟨4231929855774449772182539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5642573141032599696243385 4231929855774449772182539)
        ·
          refine ⟨6347894783661674658273809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231929855774449772182539 6347894783661674658273809)
          ·
            refine ⟨4760921087746255993705357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6347894783661674658273809 4760921087746255993705357)
            ·
              refine ⟨1785345407904845997639509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4760921087746255993705357 1785345407904845997639509)
              ·
                refine ⟨10461008249442457017419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1785345407904845997639509 10461008249442457017419)
                ·
                  rfl

theorem cell22_275032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 9].length) (baseStart_275032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275032 prefixEnd_275032 := by exact prefixLift 275032
  have htrace : WordTrace (prefixWord ++ tailWord_275032) baseStart_275032 baseEnd_275032 := by
    simpa [prefixWord, tailWord_275032, baseEnd_275032] using wordTrace_append hprefix tailTrace_275032
  have hstable : (prefixWord ++ tailWord_275032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275032).length < 2 ^ (prefixWord ++ tailWord_275032).sum := by decide
  have hdescent : baseEnd_275032 < baseStart_275032 := by decide
  rcases family_descends (prefixWord ++ tailWord_275032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275064 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 5, 3]
def baseStart_275064 : Nat := 118140960795 + 275064 * 2 ^ 59
def prefixEnd_275064 : Nat := 4983230072969 + 3 ^ 40 * 275064 * 2
def baseEnd_275064 : Nat := 94160028498944696356673

theorem tailTrace_275064 : CollatzResearch.WordTrace tailWord_275064 prefixEnd_275064 94160028498944696356673 := by
  unfold tailWord_275064
  simp only [CollatzResearch.WordTrace]
  refine ⟨5016204137748790018132123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6688272183665053357509497 5016204137748790018132123)
  ·
    refine ⟨7524306206623185027198185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5016204137748790018132123 7524306206623185027198185)
    ·
      refine ⟨5643229654967388770398639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7524306206623185027198185 5643229654967388770398639)
      ·
        refine ⟨8464844482451083155597959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5643229654967388770398639 8464844482451083155597959)
        ·
          refine ⟨12697266723676624733396939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8464844482451083155597959 12697266723676624733396939)
          ·
            refine ⟨19045900085514937100095409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12697266723676624733396939 19045900085514937100095409)
            ·
              refine ⟨14284425064136202825071557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19045900085514937100095409 14284425064136202825071557)
              ·
                refine ⟨2678329699525538029700917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14284425064136202825071557 2678329699525538029700917)
                ·
                  refine ⟨251093409330519190284461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2678329699525538029700917 251093409330519190284461)
                  ·
                    refine ⟨94160028498944696356673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251093409330519190284461 94160028498944696356673)
                    ·
                      rfl

theorem cell22_275064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_275064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275064 prefixEnd_275064 := by exact prefixLift 275064
  have htrace : WordTrace (prefixWord ++ tailWord_275064) baseStart_275064 baseEnd_275064 := by
    simpa [prefixWord, tailWord_275064, baseEnd_275064] using wordTrace_append hprefix tailTrace_275064
  have hstable : (prefixWord ++ tailWord_275064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275064).length < 2 ^ (prefixWord ++ tailWord_275064).sum := by decide
  have hdescent : baseEnd_275064 < baseStart_275064 := by decide
  rcases family_descends (prefixWord ++ tailWord_275064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275173 : List Nat := [1, 3, 1, 4, 1, 2, 3, 3, 4]
def baseStart_275173 : Nat := 118140960795 + 275173 * 2 ^ 59
def prefixEnd_275173 : Nat := 4983230072969 + 3 ^ 40 * 275173 * 2
def baseEnd_275173 : Nat := 31399113808834915127113

theorem tailTrace_275173 : CollatzResearch.WordTrace tailWord_275173 prefixEnd_275173 31399113808834915127113 := by
  unfold tailWord_275173
  simp only [CollatzResearch.WordTrace]
  refine ⟨10036383832102691651982173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6690922554735127767988115 10036383832102691651982173)
  ·
    refine ⟨3763643937038509369493315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10036383832102691651982173 3763643937038509369493315)
    ·
      refine ⟨5645465905557764054239973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3763643937038509369493315 5645465905557764054239973)
      ·
        refine ⟨1058524857292080760169995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5645465905557764054239973 1058524857292080760169995)
        ·
          refine ⟨1587787285938121140254993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058524857292080760169995 1587787285938121140254993)
          ·
            refine ⟨1190840464453590855191245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1587787285938121140254993 1190840464453590855191245)
            ·
              refine ⟨446565174170096570696717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1190840464453590855191245 446565174170096570696717)
              ·
                refine ⟨167461940313786214011269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446565174170096570696717 167461940313786214011269)
                ·
                  refine ⟨31399113808834915127113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167461940313786214011269 31399113808834915127113)
                  ·
                    rfl

theorem cell22_275173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_275173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275173 prefixEnd_275173 := by exact prefixLift 275173
  have htrace : WordTrace (prefixWord ++ tailWord_275173) baseStart_275173 baseEnd_275173 := by
    simpa [prefixWord, tailWord_275173, baseEnd_275173] using wordTrace_append hprefix tailTrace_275173
  have hstable : (prefixWord ++ tailWord_275173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275173).length < 2 ^ (prefixWord ++ tailWord_275173).sum := by decide
  have hdescent : baseEnd_275173 < baseStart_275173 := by decide
  rcases family_descends (prefixWord ++ tailWord_275173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275186 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_275186 : Nat := 118140960795 + 275186 * 2 ^ 59
def prefixEnd_275186 : Nat := 4983230072969 + 3 ^ 40 * 275186 * 2
def baseEnd_275186 : Nat := 94201791592177044806299

theorem tailTrace_275186 : CollatzResearch.WordTrace tailWord_275186 prefixEnd_275186 94201791592177044806299 := by
  unfold tailWord_275186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509214495263898718051353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6691238654037063248136941 2509214495263898718051353)
  ·
    refine ⟨1881910871447924038538515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2509214495263898718051353 1881910871447924038538515)
    ·
      refine ⟨2822866307171886057807773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1881910871447924038538515 2822866307171886057807773)
      ·
        refine ⟨1058574865189457271677915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2822866307171886057807773 1058574865189457271677915)
        ·
          refine ⟨1587862297784185907516873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058574865189457271677915 1587862297784185907516873)
          ·
            refine ⟨1190896723338139430637655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1587862297784185907516873 1190896723338139430637655)
            ·
              refine ⟨1786345085007209145956483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190896723338139430637655 1786345085007209145956483)
              ·
                refine ⟨2679517627510813718934725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786345085007209145956483 2679517627510813718934725)
                ·
                  refine ⟨502409555158277572300261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2679517627510813718934725 502409555158277572300261)
                  ·
                    refine ⟨94201791592177044806299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 502409555158277572300261 94201791592177044806299)
                    ·
                      rfl

theorem cell22_275186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_275186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275186 prefixEnd_275186 := by exact prefixLift 275186
  have htrace : WordTrace (prefixWord ++ tailWord_275186) baseStart_275186 baseEnd_275186 := by
    simpa [prefixWord, tailWord_275186, baseEnd_275186] using wordTrace_append hprefix tailTrace_275186
  have hstable : (prefixWord ++ tailWord_275186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275186).length < 2 ^ (prefixWord ++ tailWord_275186).sum := by decide
  have hdescent : baseEnd_275186 < baseStart_275186 := by decide
  rcases family_descends (prefixWord ++ tailWord_275186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275190 : List Nat := [5, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_275190 : Nat := 118140960795 + 275190 * 2 ^ 59
def prefixEnd_275190 : Nat := 4983230072969 + 3 ^ 40 * 275190 * 2
def baseEnd_275190 : Nat := 31401053624640789235429

theorem tailTrace_275190 : CollatzResearch.WordTrace tailWord_275190 prefixEnd_275190 31401053624640789235429 := by
  unfold tailWord_275190
  simp only [CollatzResearch.WordTrace]
  refine ⟨627312742065068972209439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6691335915360735703567349 627312742065068972209439)
  ·
    refine ⟨940969113097603458314159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627312742065068972209439 940969113097603458314159)
    ·
      refine ⟨1411453669646405187471239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 940969113097603458314159 1411453669646405187471239)
      ·
        refine ⟨2117180504469607781206859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411453669646405187471239 2117180504469607781206859)
        ·
          refine ⟨3175770756704411671810289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117180504469607781206859 3175770756704411671810289)
          ·
            refine ⟨2381828067528308753857717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3175770756704411671810289 2381828067528308753857717)
            ·
              refine ⟨223296381330778945674161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2381828067528308753857717 223296381330778945674161)
              ·
                refine ⟨167472285998084209255621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223296381330778945674161 167472285998084209255621)
                ·
                  refine ⟨31401053624640789235429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167472285998084209255621 31401053624640789235429)
                  ·
                    rfl

theorem cell22_275190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_275190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275190 prefixEnd_275190 := by exact prefixLift 275190
  have htrace : WordTrace (prefixWord ++ tailWord_275190) baseStart_275190 baseEnd_275190 := by
    simpa [prefixWord, tailWord_275190, baseEnd_275190] using wordTrace_append hprefix tailTrace_275190
  have hstable : (prefixWord ++ tailWord_275190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275190).length < 2 ^ (prefixWord ++ tailWord_275190).sum := by decide
  have hdescent : baseEnd_275190 < baseStart_275190 := by decide
  rcases family_descends (prefixWord ++ tailWord_275190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275250 : List Nat := [3, 2, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_275250 : Nat := 118140960795 + 275250 * 2 ^ 59
def prefixEnd_275250 : Nat := 4983230072969 + 3 ^ 40 * 275250 * 2
def baseEnd_275250 : Nat := 94223700100102211206103

theorem tailTrace_275250 : CollatzResearch.WordTrace tailWord_275250 prefixEnd_275250 94223700100102211206103 := by
  unfold tailWord_275250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509798063205933450633801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6692794835215822535023469 2509798063205933450633801)
  ·
    refine ⟨1882348547404450087975351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2509798063205933450633801 1882348547404450087975351)
    ·
      refine ⟨2823522821106675131963027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1882348547404450087975351 2823522821106675131963027)
      ·
        refine ⟨4235284231660012697944541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2823522821106675131963027 4235284231660012697944541)
        ·
          refine ⟨1588231586872504761729203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4235284231660012697944541 1588231586872504761729203)
          ·
            refine ⟨2382347380308757142593805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588231586872504761729203 2382347380308757142593805)
            ·
              refine ⟨893380267615783928472677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2382347380308757142593805 893380267615783928472677)
              ·
                refine ⟨167508800177959486588627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 893380267615783928472677 167508800177959486588627)
                ·
                  refine ⟨251263200266939229882941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167508800177959486588627 251263200266939229882941)
                  ·
                    refine ⟨94223700100102211206103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251263200266939229882941 94223700100102211206103)
                    ·
                      rfl

theorem cell22_275250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_275250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275250 prefixEnd_275250 := by exact prefixLift 275250
  have htrace : WordTrace (prefixWord ++ tailWord_275250) baseStart_275250 baseEnd_275250 := by
    simpa [prefixWord, tailWord_275250, baseEnd_275250] using wordTrace_append hprefix tailTrace_275250
  have hstable : (prefixWord ++ tailWord_275250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275250).length < 2 ^ (prefixWord ++ tailWord_275250).sum := by decide
  have hdescent : baseEnd_275250 < baseStart_275250 := by decide
  rcases family_descends (prefixWord ++ tailWord_275250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275308 : List Nat := [2, 2, 1, 1, 4, 1, 1, 6, 4]
def baseStart_275308 : Nat := 118140960795 + 275308 * 2 ^ 59
def prefixEnd_275308 : Nat := 4983230072969 + 3 ^ 40 * 275308 * 2
def baseEnd_275308 : Nat := 31414518228469797751975

theorem tailTrace_275308 : CollatzResearch.WordTrace tailWord_275308 prefixEnd_275308 31414518228469797751975 := by
  unfold tailWord_275308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020653843306804854073289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6694205124409073138764385 5020653843306804854073289)
  ·
    refine ⟨3765490382480103640554967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5020653843306804854073289 3765490382480103640554967)
    ·
      refine ⟨5648235573720155460832451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3765490382480103640554967 5648235573720155460832451)
      ·
        refine ⟨8472353360580233191248677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5648235573720155460832451 8472353360580233191248677)
        ·
          refine ⟨1588566255108793723359127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8472353360580233191248677 1588566255108793723359127)
          ·
            refine ⟨2382849382663190585038691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588566255108793723359127 2382849382663190585038691)
            ·
              refine ⟨3574274073994785877558037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382849382663190585038691 3574274073994785877558037)
              ·
                refine ⟨167544097218505588010533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3574274073994785877558037 167544097218505588010533)
                ·
                  refine ⟨31414518228469797751975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167544097218505588010533 31414518228469797751975)
                  ·
                    rfl

theorem cell22_275308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_275308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275308 prefixEnd_275308 := by exact prefixLift 275308
  have htrace : WordTrace (prefixWord ++ tailWord_275308) baseStart_275308 baseEnd_275308 := by
    simpa [prefixWord, tailWord_275308, baseEnd_275308] using wordTrace_append hprefix tailTrace_275308
  have hstable : (prefixWord ++ tailWord_275308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275308).length < 2 ^ (prefixWord ++ tailWord_275308).sum := by decide
  have hdescent : baseEnd_275308 < baseStart_275308 := by decide
  rcases family_descends (prefixWord ++ tailWord_275308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275321 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_275321 : Nat := 118140960795 + 275321 * 2 ^ 59
def prefixEnd_275321 : Nat := 4983230072969 + 3 ^ 40 * 275321 * 2
def baseEnd_275321 : Nat := 94248004851081692680885

theorem tailTrace_275321 : CollatzResearch.WordTrace tailWord_275321 prefixEnd_275321 94248004851081692680885 := by
  unfold tailWord_275321
  simp only [CollatzResearch.WordTrace]
  refine ⟨10041781835566512928369817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6694521223711008618913211 10041781835566512928369817)
  ·
    refine ⟨7531336376674884696277363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10041781835566512928369817 7531336376674884696277363)
    ·
      refine ⟨11297004565012327044416045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7531336376674884696277363 11297004565012327044416045)
      ·
        refine ⟨4236376711879622641656017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11297004565012327044416045 4236376711879622641656017)
        ·
          refine ⟨3177282533909716981242013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4236376711879622641656017 3177282533909716981242013)
          ·
            refine ⟨1191480950216143867965755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3177282533909716981242013 1191480950216143867965755)
            ·
              refine ⟨1787221425324215801948633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191480950216143867965755 1787221425324215801948633)
              ·
                refine ⟨1340416068993161851461475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1787221425324215801948633 1340416068993161851461475)
                ·
                  refine ⟨2010624103489742777192213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340416068993161851461475 2010624103489742777192213)
                  ·
                    refine ⟨94248004851081692680885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2010624103489742777192213 94248004851081692680885)
                    ·
                      rfl

theorem cell22_275321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_275321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275321 prefixEnd_275321 := by exact prefixLift 275321
  have htrace : WordTrace (prefixWord ++ tailWord_275321) baseStart_275321 baseEnd_275321 := by
    simpa [prefixWord, tailWord_275321, baseEnd_275321] using wordTrace_append hprefix tailTrace_275321
  have hstable : (prefixWord ++ tailWord_275321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275321).length < 2 ^ (prefixWord ++ tailWord_275321).sum := by decide
  have hdescent : baseEnd_275321 < baseStart_275321 := by decide
  rcases family_descends (prefixWord ++ tailWord_275321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275323 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 2, 3]
def baseStart_275323 : Nat := 118140960795 + 275323 * 2 ^ 59
def prefixEnd_275323 : Nat := 4983230072969 + 3 ^ 40 * 275323 * 2
def baseEnd_275323 : Nat := 94248689491954354130879

theorem tailTrace_275323 : CollatzResearch.WordTrace tailWord_275323 prefixEnd_275323 94248689491954354130879 := by
  unfold tailWord_275323
  simp only [CollatzResearch.WordTrace]
  refine ⟨10041854781559267269942623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6694569854372844846628415 10041854781559267269942623)
  ·
    refine ⟨15062782172338900904913935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10041854781559267269942623 15062782172338900904913935)
    ·
      refine ⟨22594173258508351357370903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15062782172338900904913935 22594173258508351357370903)
      ·
        refine ⟨33891259887762527036056355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22594173258508351357370903 33891259887762527036056355)
        ·
          refine ⟨50836889831643790554084533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33891259887762527036056355 50836889831643790554084533)
          ·
            refine ⟨4765958421716605364445425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50836889831643790554084533 4765958421716605364445425)
            ·
              refine ⟨3574468816287454023334069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4765958421716605364445425 3574468816287454023334069)
              ·
                refine ⟨335106451526948814687569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3574468816287454023334069 335106451526948814687569)
                ·
                  refine ⟨251329838645211611015677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335106451526948814687569 251329838645211611015677)
                  ·
                    refine ⟨94248689491954354130879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251329838645211611015677 94248689491954354130879)
                    ·
                      rfl

theorem cell22_275323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 3].length) (baseStart_275323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275323 prefixEnd_275323 := by exact prefixLift 275323
  have htrace : WordTrace (prefixWord ++ tailWord_275323) baseStart_275323 baseEnd_275323 := by
    simpa [prefixWord, tailWord_275323, baseEnd_275323] using wordTrace_append hprefix tailTrace_275323
  have hstable : (prefixWord ++ tailWord_275323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275323).length < 2 ^ (prefixWord ++ tailWord_275323).sum := by decide
  have hdescent : baseEnd_275323 < baseStart_275323 := by decide
  rcases family_descends (prefixWord ++ tailWord_275323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275338 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_275338 : Nat := 118140960795 + 275338 * 2 ^ 59
def prefixEnd_275338 : Nat := 4983230072969 + 3 ^ 40 * 275338 * 2
def baseEnd_275338 : Nat := 94253824298499315005833

theorem tailTrace_275338 : CollatzResearch.WordTrace tailWord_275338 prefixEnd_275338 94253824298499315005833 := by
  unfold tailWord_275338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510600469126231207934667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6694934584336616554492445 2510600469126231207934667)
  ·
    refine ⟨3765900703689346811902001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2510600469126231207934667 3765900703689346811902001)
    ·
      refine ⟨2824425527767010108926501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3765900703689346811902001 2824425527767010108926501)
      ·
        refine ⟨529579786456314395423719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2824425527767010108926501 529579786456314395423719)
        ·
          refine ⟨794369679684471593135579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529579786456314395423719 794369679684471593135579)
          ·
            refine ⟨1191554519526707389703369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794369679684471593135579 1191554519526707389703369)
            ·
              refine ⟨893665889645030542277527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1191554519526707389703369 893665889645030542277527)
              ·
                refine ⟨1340498834467545813416291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893665889645030542277527 1340498834467545813416291)
                ·
                  refine ⟨2010748251701318720124437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340498834467545813416291 2010748251701318720124437)
                  ·
                    refine ⟨94253824298499315005833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2010748251701318720124437 94253824298499315005833)
                    ·
                      rfl

theorem cell22_275338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_275338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275338 prefixEnd_275338 := by exact prefixLift 275338
  have htrace : WordTrace (prefixWord ++ tailWord_275338) baseStart_275338 baseEnd_275338 := by
    simpa [prefixWord, tailWord_275338, baseEnd_275338] using wordTrace_append hprefix tailTrace_275338
  have hstable : (prefixWord ++ tailWord_275338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275338).length < 2 ^ (prefixWord ++ tailWord_275338).sum := by decide
  have hdescent : baseEnd_275338 < baseStart_275338 := by decide
  rcases family_descends (prefixWord ++ tailWord_275338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275473 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_275473 : Nat := 118140960795 + 275473 * 2 ^ 59
def prefixEnd_275473 : Nat := 4983230072969 + 3 ^ 40 * 275473 * 2
def baseEnd_275473 : Nat := 94300037557403962880419

theorem tailTrace_275473 : CollatzResearch.WordTrace tailWord_275473 prefixEnd_275473 94300037557403962880419 := by
  unfold tailWord_275473
  simp only [CollatzResearch.WordTrace]
  refine ⟨10047325731015842887903073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6698217154010561925268715 10047325731015842887903073)
  ·
    refine ⟨7535494298261882165927305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10047325731015842887903073 7535494298261882165927305)
    ·
      refine ⟨5651620723696411624445479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7535494298261882165927305 5651620723696411624445479)
      ·
        refine ⟨8477431085544617436668219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5651620723696411624445479 8477431085544617436668219)
        ·
          refine ⟨12716146628316926155002329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8477431085544617436668219 12716146628316926155002329)
          ·
            refine ⟨9537109971237694616251747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12716146628316926155002329 9537109971237694616251747)
            ·
              refine ⟨14305664956856541924377621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9537109971237694616251747 14305664956856541924377621)
              ·
                refine ⟨670578044852650402705201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14305664956856541924377621 670578044852650402705201)
                ·
                  refine ⟨502933533639487802028901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 670578044852650402705201 502933533639487802028901)
                  ·
                    refine ⟨94300037557403962880419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 502933533639487802028901 94300037557403962880419)
                    ·
                      rfl

theorem cell22_275473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_275473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275473 prefixEnd_275473 := by exact prefixLift 275473
  have htrace : WordTrace (prefixWord ++ tailWord_275473) baseStart_275473 baseEnd_275473 := by
    simpa [prefixWord, tailWord_275473, baseEnd_275473] using wordTrace_append hprefix tailTrace_275473
  have hstable : (prefixWord ++ tailWord_275473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275473).length < 2 ^ (prefixWord ++ tailWord_275473).sum := by decide
  have hdescent : baseEnd_275473 < baseStart_275473 := by decide
  rcases family_descends (prefixWord ++ tailWord_275473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275492 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_275492 : Nat := 118140960795 + 275492 * 2 ^ 59
def prefixEnd_275492 : Nat := 4983230072969 + 3 ^ 40 * 275492 * 2
def baseEnd_275492 : Nat := 94306541645694246655361

theorem tailTrace_275492 : CollatzResearch.WordTrace tailWord_275492 prefixEnd_275492 94306541645694246655361 := by
  unfold tailWord_275492
  simp only [CollatzResearch.WordTrace]
  refine ⟨5024009358973504566422365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6698679145298006088563153 5024009358973504566422365)
  ·
    refine ⟨1884003509615064212408387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5024009358973504566422365 1884003509615064212408387)
    ·
      refine ⟨2826005264422596318612581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1884003509615064212408387 2826005264422596318612581)
      ·
        refine ⟨529875987079236809739859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2826005264422596318612581 529875987079236809739859)
        ·
          refine ⟨794813980618855214609789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529875987079236809739859 794813980618855214609789)
          ·
            refine ⟨298055242732070705478671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 794813980618855214609789 298055242732070705478671)
            ·
              refine ⟨447082864098106058218007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298055242732070705478671 447082864098106058218007)
              ·
                refine ⟨670624296147159087327011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447082864098106058218007 670624296147159087327011)
                ·
                  refine ⟨1005936444220738630990517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670624296147159087327011 1005936444220738630990517)
                  ·
                    refine ⟨94306541645694246655361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1005936444220738630990517 94306541645694246655361)
                    ·
                      rfl

theorem cell22_275492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_275492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275492 prefixEnd_275492 := by exact prefixLift 275492
  have htrace : WordTrace (prefixWord ++ tailWord_275492) baseStart_275492 baseEnd_275492 := by
    simpa [prefixWord, tailWord_275492, baseEnd_275492] using wordTrace_append hprefix tailTrace_275492
  have hstable : (prefixWord ++ tailWord_275492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275492).length < 2 ^ (prefixWord ++ tailWord_275492).sum := by decide
  have hdescent : baseEnd_275492 < baseStart_275492 := by decide
  rcases family_descends (prefixWord ++ tailWord_275492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275537 : List Nat := [1, 2, 2, 1, 3, 1, 2, 6, 1, 3]
def baseStart_275537 : Nat := 118140960795 + 275537 * 2 ^ 59
def prefixEnd_275537 : Nat := 4983230072969 + 3 ^ 40 * 275537 * 2
def baseEnd_275537 : Nat := 94321946065329129280223

theorem tailTrace_275537 : CollatzResearch.WordTrace tailWord_275537 prefixEnd_275537 94321946065329129280223 := by
  unfold tailWord_275537
  simp only [CollatzResearch.WordTrace]
  refine ⟨10049660002783981818232865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6699773335189321212155243 10049660002783981818232865)
  ·
    refine ⟨7537245002087986363674649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10049660002783981818232865 7537245002087986363674649)
    ·
      refine ⟨5652933751565989772755987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7537245002087986363674649 5652933751565989772755987)
      ·
        refine ⟨8479400627348984659133981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5652933751565989772755987 8479400627348984659133981)
        ·
          refine ⟨3179775235255869247175243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8479400627348984659133981 3179775235255869247175243)
          ·
            refine ⟨4769662852883803870762865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179775235255869247175243 4769662852883803870762865)
            ·
              refine ⟨3577247139662852903072149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4769662852883803870762865 3577247139662852903072149)
              ·
                refine ⟨167683459671696229831507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3577247139662852903072149 167683459671696229831507)
                ·
                  refine ⟨251525189507544344747261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167683459671696229831507 251525189507544344747261)
                  ·
                    refine ⟨94321946065329129280223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251525189507544344747261 94321946065329129280223)
                    ·
                      rfl

theorem cell22_275537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_275537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275537 prefixEnd_275537 := by exact prefixLift 275537
  have htrace : WordTrace (prefixWord ++ tailWord_275537) baseStart_275537 baseEnd_275537 := by
    simpa [prefixWord, tailWord_275537, baseEnd_275537] using wordTrace_append hprefix tailTrace_275537
  have hstable : (prefixWord ++ tailWord_275537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275537).length < 2 ^ (prefixWord ++ tailWord_275537).sum := by decide
  have hdescent : baseEnd_275537 < baseStart_275537 := by decide
  rcases family_descends (prefixWord ++ tailWord_275537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275644 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 2, 3]
def baseStart_275644 : Nat := 118140960795 + 275644 * 2 ^ 59
def prefixEnd_275644 : Nat := 4983230072969 + 3 ^ 40 * 275644 * 2
def baseEnd_275644 : Nat := 94358574352016516854895

theorem tailTrace_275644 : CollatzResearch.WordTrace tailWord_275644 prefixEnd_275644 94358574352016516854895 := by
  unfold tailWord_275644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5026781306698169546188993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6702375075597559394918657 5026781306698169546188993)
  ·
    refine ⟨3770085980023627159641745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5026781306698169546188993 3770085980023627159641745)
    ·
      refine ⟨2827564485017720369731309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3770085980023627159641745 2827564485017720369731309)
      ·
        refine ⟨1060336681881645138649241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2827564485017720369731309 1060336681881645138649241)
        ·
          refine ⟨795252511411233853986931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1060336681881645138649241 795252511411233853986931)
          ·
            refine ⟨1192878767116850780980397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795252511411233853986931 1192878767116850780980397)
            ·
              refine ⟨447329537668819042867649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1192878767116850780980397 447329537668819042867649)
              ·
                refine ⟨335497153251614282150737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447329537668819042867649 335497153251614282150737)
                ·
                  refine ⟨251622864938710711613053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335497153251614282150737 251622864938710711613053)
                  ·
                    refine ⟨94358574352016516854895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251622864938710711613053 94358574352016516854895)
                    ·
                      rfl

theorem cell22_275644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_275644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275644 prefixEnd_275644 := by exact prefixLift 275644
  have htrace : WordTrace (prefixWord ++ tailWord_275644) baseStart_275644 baseEnd_275644 := by
    simpa [prefixWord, tailWord_275644, baseEnd_275644] using wordTrace_append hprefix tailTrace_275644
  have hstable : (prefixWord ++ tailWord_275644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275644).length < 2 ^ (prefixWord ++ tailWord_275644).sum := by decide
  have hdescent : baseEnd_275644 < baseStart_275644 := by decide
  rcases family_descends (prefixWord ++ tailWord_275644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275702 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_275702 : Nat := 118140960795 + 275702 * 2 ^ 59
def prefixEnd_275702 : Nat := 4983230072969 + 3 ^ 40 * 275702 * 2
def baseEnd_275702 : Nat := 31459476312441232968239

theorem tailTrace_275702 : CollatzResearch.WordTrace tailWord_275702 prefixEnd_275702 31459476312441232968239 := by
  unfold tailWord_275702
  simp only [CollatzResearch.WordTrace]
  refine ⟨628479877949138437374335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6703785364790809998659573 628479877949138437374335)
  ·
    refine ⟨942719816923707656061503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 628479877949138437374335 942719816923707656061503)
    ·
      refine ⟨1414079725385561484092255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 942719816923707656061503 1414079725385561484092255)
      ·
        refine ⟨2121119588078342226138383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414079725385561484092255 2121119588078342226138383)
        ·
          refine ⟨3181679382117513339207575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121119588078342226138383 3181679382117513339207575)
          ·
            refine ⟨4772519073176270008811363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181679382117513339207575 4772519073176270008811363)
            ·
              refine ⟨7158778609764405013217045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4772519073176270008811363 7158778609764405013217045)
              ·
                refine ⟨335567747332706484994549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7158778609764405013217045 335567747332706484994549)
                ·
                  refine ⟨31459476312441232968239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 335567747332706484994549 31459476312441232968239)
                  ·
                    rfl

theorem cell22_275702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_275702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275702 prefixEnd_275702 := by exact prefixLift 275702
  have htrace : WordTrace (prefixWord ++ tailWord_275702) baseStart_275702 baseEnd_275702 := by
    simpa [prefixWord, tailWord_275702, baseEnd_275702] using wordTrace_append hprefix tailTrace_275702
  have hstable : (prefixWord ++ tailWord_275702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275702).length < 2 ^ (prefixWord ++ tailWord_275702).sum := by decide
  have hdescent : baseEnd_275702 < baseStart_275702 := by decide
  rcases family_descends (prefixWord ++ tailWord_275702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275706 : List Nat := [3, 1, 1, 1, 1, 4, 5, 2, 1, 3]
def baseStart_275706 : Nat := 118140960795 + 275706 * 2 ^ 59
def prefixEnd_275706 : Nat := 4983230072969 + 3 ^ 40 * 275706 * 2
def baseEnd_275706 : Nat := 94379798219069021804705

theorem tailTrace_275706 : CollatzResearch.WordTrace tailWord_275706 prefixEnd_275706 94379798219069021804705 := by
  unfold tailWord_275706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2513955984792930920283743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6703882626114482454089981 2513955984792930920283743)
  ·
    refine ⟨3770933977189396380425615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2513955984792930920283743 3770933977189396380425615)
    ·
      refine ⟨5656400965784094570638423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3770933977189396380425615 5656400965784094570638423)
      ·
        refine ⟨8484601448676141855957635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5656400965784094570638423 8484601448676141855957635)
        ·
          refine ⟨12726902173014212783936453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8484601448676141855957635 12726902173014212783936453)
          ·
            refine ⟨2386294157440164896988085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12726902173014212783936453 2386294157440164896988085)
            ·
              refine ⟨223715077260015459092633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2386294157440164896988085 223715077260015459092633)
              ·
                refine ⟨167786307945011594319475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223715077260015459092633 167786307945011594319475)
                ·
                  refine ⟨251679461917517391479213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167786307945011594319475 251679461917517391479213)
                  ·
                    refine ⟨94379798219069021804705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251679461917517391479213 94379798219069021804705)
                    ·
                      rfl

theorem cell22_275706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_275706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275706 prefixEnd_275706 := by exact prefixLift 275706
  have htrace : WordTrace (prefixWord ++ tailWord_275706) baseStart_275706 baseEnd_275706 := by
    simpa [prefixWord, tailWord_275706, baseEnd_275706] using wordTrace_append hprefix tailTrace_275706
  have hstable : (prefixWord ++ tailWord_275706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275706).length < 2 ^ (prefixWord ++ tailWord_275706).sum := by decide
  have hdescent : baseEnd_275706 < baseStart_275706 := by decide
  rcases family_descends (prefixWord ++ tailWord_275706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275792 : List Nat := [2, 1, 1, 1, 1, 5, 5, 6]
def baseStart_275792 : Nat := 118140960795 + 275792 * 2 ^ 59
def prefixEnd_275792 : Nat := 4983230072969 + 3 ^ 40 * 275792 * 2
def baseEnd_275792 : Nat := 10489915308510384906049

theorem tailTrace_275792 : CollatzResearch.WordTrace tailWord_275792 prefixEnd_275792 10489915308510384906049 := by
  unfold tailWord_275792
  simp only [CollatzResearch.WordTrace]
  refine ⟨5029480308430080184382815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6705973744573440245843753 5029480308430080184382815)
  ·
    refine ⟨7544220462645120276574223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5029480308430080184382815 7544220462645120276574223)
    ·
      refine ⟨11316330693967680414861335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7544220462645120276574223 11316330693967680414861335)
      ·
        refine ⟨16974496040951520622292003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11316330693967680414861335 16974496040951520622292003)
        ·
          refine ⟨25461744061427280933438005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16974496040951520622292003 25461744061427280933438005)
          ·
            refine ⟨2387038505758807587509813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25461744061427280933438005 2387038505758807587509813)
            ·
              refine ⟨223784859914888211329045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2387038505758807587509813 223784859914888211329045)
              ·
                refine ⟨10489915308510384906049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 223784859914888211329045 10489915308510384906049)
                ·
                  rfl

theorem cell22_275792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 6].length) (baseStart_275792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275792 prefixEnd_275792 := by exact prefixLift 275792
  have htrace : WordTrace (prefixWord ++ tailWord_275792) baseStart_275792 baseEnd_275792 := by
    simpa [prefixWord, tailWord_275792, baseEnd_275792] using wordTrace_append hprefix tailTrace_275792
  have hstable : (prefixWord ++ tailWord_275792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275792).length < 2 ^ (prefixWord ++ tailWord_275792).sum := by decide
  have hdescent : baseEnd_275792 < baseStart_275792 := by decide
  rcases family_descends (prefixWord ++ tailWord_275792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275807 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 7, 3]
def baseStart_275807 : Nat := 118140960795 + 275807 * 2 ^ 59
def prefixEnd_275807 : Nat := 4983230072969 + 3 ^ 40 * 275807 * 2
def baseEnd_275807 : Nat := 94414372583138425029395

theorem tailTrace_275807 : CollatzResearch.WordTrace tailWord_275807 prefixEnd_275807 94414372583138425029395 := by
  unfold tailWord_275807
  simp only [CollatzResearch.WordTrace]
  refine ⟨10059507711805817930561675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6706338474537211953707783 10059507711805817930561675)
  ·
    refine ⟨15089261567708726895842513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10059507711805817930561675 15089261567708726895842513)
    ·
      refine ⟨11316946175781545171881885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15089261567708726895842513 11316946175781545171881885)
      ·
        refine ⟨4243854815918079439455707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11316946175781545171881885 4243854815918079439455707)
        ·
          refine ⟨6365782223877119159183561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243854815918079439455707 6365782223877119159183561)
          ·
            refine ⟨4774336667907839369387671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6365782223877119159183561 4774336667907839369387671)
            ·
              refine ⟨7161505001861759054081507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4774336667907839369387671 7161505001861759054081507)
              ·
                refine ⟨10742257502792638581122261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7161505001861759054081507 10742257502792638581122261)
                ·
                  refine ⟨251771660221702466745053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10742257502792638581122261 251771660221702466745053)
                  ·
                    refine ⟨94414372583138425029395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251771660221702466745053 94414372583138425029395)
                    ·
                      rfl

theorem cell22_275807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 3].length) (baseStart_275807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275807 prefixEnd_275807 := by exact prefixLift 275807
  have htrace : WordTrace (prefixWord ++ tailWord_275807) baseStart_275807 baseEnd_275807 := by
    simpa [prefixWord, tailWord_275807, baseEnd_275807] using wordTrace_append hprefix tailTrace_275807
  have hstable : (prefixWord ++ tailWord_275807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275807).length < 2 ^ (prefixWord ++ tailWord_275807).sum := by decide
  have hdescent : baseEnd_275807 < baseStart_275807 := by decide
  rcases family_descends (prefixWord ++ tailWord_275807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275824 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 3, 3]
def baseStart_275824 : Nat := 118140960795 + 275824 * 2 ^ 59
def prefixEnd_275824 : Nat := 4983230072969 + 3 ^ 40 * 275824 * 2
def baseEnd_275824 : Nat := 94420192030556047354343

theorem tailTrace_275824 : CollatzResearch.WordTrace tailWord_275824 prefixEnd_275824 94420192030556047354343 := by
  unfold tailWord_275824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5030063876372114916965263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6706751835162819889287017 5030063876372114916965263)
  ·
    refine ⟨7545095814558172375447895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5030063876372114916965263 7545095814558172375447895)
    ·
      refine ⟨11317643721837258563171843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7545095814558172375447895 11317643721837258563171843)
      ·
        refine ⟨16976465582755887844757765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11317643721837258563171843 16976465582755887844757765)
        ·
          refine ⟨3183087296766728970892081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16976465582755887844757765 3183087296766728970892081)
          ·
            refine ⟨2387315472575046728169061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3183087296766728970892081 2387315472575046728169061)
            ·
              refine ⟨447621651107821261531699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2387315472575046728169061 447621651107821261531699)
              ·
                refine ⟨671432476661731892297549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447621651107821261531699 671432476661731892297549)
                ·
                  refine ⟨251787178748149459611581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 671432476661731892297549 251787178748149459611581)
                  ·
                    refine ⟨94420192030556047354343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251787178748149459611581 94420192030556047354343)
                    ·
                      rfl

theorem cell22_275824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3, 3].length) (baseStart_275824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275824 prefixEnd_275824 := by exact prefixLift 275824
  have htrace : WordTrace (prefixWord ++ tailWord_275824) baseStart_275824 baseEnd_275824 := by
    simpa [prefixWord, tailWord_275824, baseEnd_275824] using wordTrace_append hprefix tailTrace_275824
  have hstable : (prefixWord ++ tailWord_275824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275824).length < 2 ^ (prefixWord ++ tailWord_275824).sum := by decide
  have hdescent : baseEnd_275824 < baseStart_275824 := by decide
  rcases family_descends (prefixWord ++ tailWord_275824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275914 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_275914 : Nat := 118140960795 + 275914 * 2 ^ 59
def prefixEnd_275914 : Nat := 4983230072969 + 3 ^ 40 * 275914 * 2
def baseEnd_275914 : Nat := 94451000869825812604067

theorem tailTrace_275914 : CollatzResearch.WordTrace tailWord_275914 prefixEnd_275914 94451000869825812604067 := by
  unfold tailWord_275914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2515852580604543801176699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6708940214945450136471197 2515852580604543801176699)
  ·
    refine ⟨3773778870906815701765049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2515852580604543801176699 3773778870906815701765049)
    ·
      refine ⟨2830334153180111776323787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3773778870906815701765049 2830334153180111776323787)
      ·
        refine ⟨4245501229770167664485681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2830334153180111776323787 4245501229770167664485681)
        ·
          refine ⟨3184125922327625748364261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4245501229770167664485681 3184125922327625748364261)
          ·
            refine ⟨597023610436429827818299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3184125922327625748364261 597023610436429827818299)
            ·
              refine ⟨895535415654644741727449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597023610436429827818299 895535415654644741727449)
              ·
                refine ⟨671651561740983556295587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895535415654644741727449 671651561740983556295587)
                ·
                  refine ⟨1007477342611475334443381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 671651561740983556295587 1007477342611475334443381)
                  ·
                    refine ⟨94451000869825812604067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1007477342611475334443381 94451000869825812604067)
                    ·
                      rfl

theorem cell22_275914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_275914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275914 prefixEnd_275914 := by exact prefixLift 275914
  have htrace : WordTrace (prefixWord ++ tailWord_275914) baseStart_275914 baseEnd_275914 := by
    simpa [prefixWord, tailWord_275914, baseEnd_275914] using wordTrace_append hprefix tailTrace_275914
  have hstable : (prefixWord ++ tailWord_275914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275914).length < 2 ^ (prefixWord ++ tailWord_275914).sum := by decide
  have hdescent : baseEnd_275914 < baseStart_275914 := by decide
  rcases family_descends (prefixWord ++ tailWord_275914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275929 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_275929 : Nat := 118140960795 + 275929 * 2 ^ 59
def prefixEnd_275929 : Nat := 4983230072969 + 3 ^ 40 * 275929 * 2
def baseEnd_275929 : Nat := 94456135676370773479021

theorem tailTrace_275929 : CollatzResearch.WordTrace tailWord_275929 prefixEnd_275929 94456135676370773479021 := by
  unfold tailWord_275929
  simp only [CollatzResearch.WordTrace]
  refine ⟨10063957417363832766502841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6709304944909221844335227 10063957417363832766502841)
  ·
    refine ⟨7547968063022874574877131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10063957417363832766502841 7547968063022874574877131)
    ·
      refine ⟨11321952094534311862315697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7547968063022874574877131 11321952094534311862315697)
      ·
        refine ⟨8491464070900733896736773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11321952094534311862315697 8491464070900733896736773)
        ·
          refine ⟨1592149513293887605638145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8491464070900733896736773 1592149513293887605638145)
          ·
            refine ⟨1194112134970415704228609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1592149513293887605638145 1194112134970415704228609)
            ·
              refine ⟨895584101227811778171457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1194112134970415704228609 895584101227811778171457)
              ·
                refine ⟨671688075920858833628593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895584101227811778171457 671688075920858833628593)
                ·
                  refine ⟨503766056940644125221445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 671688075920858833628593 503766056940644125221445)
                  ·
                    refine ⟨94456135676370773479021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 503766056940644125221445 94456135676370773479021)
                    ·
                      rfl

theorem cell22_275929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_275929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275929 prefixEnd_275929 := by exact prefixLift 275929
  have htrace : WordTrace (prefixWord ++ tailWord_275929) baseStart_275929 baseEnd_275929 := by
    simpa [prefixWord, tailWord_275929, baseEnd_275929] using wordTrace_append hprefix tailTrace_275929
  have hstable : (prefixWord ++ tailWord_275929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275929).length < 2 ^ (prefixWord ++ tailWord_275929).sum := by decide
  have hdescent : baseEnd_275929 < baseStart_275929 := by decide
  rcases family_descends (prefixWord ++ tailWord_275929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275933 : List Nat := [1, 4, 3, 1, 1, 2, 4, 2, 4]
def baseStart_275933 : Nat := 118140960795 + 275933 * 2 ^ 59
def prefixEnd_275933 : Nat := 4983230072969 + 3 ^ 40 * 275933 * 2
def baseEnd_275933 : Nat := 31485834986038698793003

theorem tailTrace_275933 : CollatzResearch.WordTrace tailWord_275933 prefixEnd_275933 31485834986038698793003 := by
  unfold tailWord_275933
  simp only [CollatzResearch.WordTrace]
  refine ⟨10064103309349341449648453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6709402206232894299765635 10064103309349341449648453)
  ·
    refine ⟨1887019370503001521809085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10064103309349341449648453 1887019370503001521809085)
    ·
      refine ⟨707632263938625570678407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1887019370503001521809085 707632263938625570678407)
      ·
        refine ⟨1061448395907938356017611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707632263938625570678407 1061448395907938356017611)
        ·
          refine ⟨1592172593861907534026417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061448395907938356017611 1592172593861907534026417)
          ·
            refine ⟨1194129445396430650519813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1592172593861907534026417 1194129445396430650519813)
            ·
              refine ⟨223899271011830746972465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1194129445396430650519813 223899271011830746972465)
              ·
                refine ⟨167924453258873060229349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223899271011830746972465 167924453258873060229349)
                ·
                  refine ⟨31485834986038698793003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167924453258873060229349 31485834986038698793003)
                  ·
                    rfl

theorem cell22_275933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_275933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275933 prefixEnd_275933 := by exact prefixLift 275933
  have htrace : WordTrace (prefixWord ++ tailWord_275933) baseStart_275933 baseEnd_275933 := by
    simpa [prefixWord, tailWord_275933, baseEnd_275933] using wordTrace_append hprefix tailTrace_275933
  have hstable : (prefixWord ++ tailWord_275933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275933).length < 2 ^ (prefixWord ++ tailWord_275933).sum := by decide
  have hdescent : baseEnd_275933 < baseStart_275933 := by decide
  rcases family_descends (prefixWord ++ tailWord_275933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275989 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 7]
def baseStart_275989 : Nat := 118140960795 + 275989 * 2 ^ 59
def prefixEnd_275989 : Nat := 4983230072969 + 3 ^ 40 * 275989 * 2
def baseEnd_275989 : Nat := 31492224967516872326279

theorem tailTrace_275989 : CollatzResearch.WordTrace tailWord_275989 prefixEnd_275989 31492224967516872326279 := by
  unfold tailWord_275989
  simp only [CollatzResearch.WordTrace]
  refine ⟨10066145797146463013687021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6710763864764308675791347 10066145797146463013687021)
  ·
    refine ⟨3774804673929923630132633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10066145797146463013687021 3774804673929923630132633)
    ·
      refine ⟨2831103505447442722599475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3774804673929923630132633 2831103505447442722599475)
      ·
        refine ⟨4246655258171164083899213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2831103505447442722599475 4246655258171164083899213)
        ·
          refine ⟨1592495721814186531462205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4246655258171164083899213 1592495721814186531462205)
          ·
            refine ⟨597185895680319949298327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1592495721814186531462205 597185895680319949298327)
            ·
              refine ⟨895778843520479923947491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597185895680319949298327 895778843520479923947491)
              ·
                refine ⟨1343668265280719885921237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895778843520479923947491 1343668265280719885921237)
                ·
                  refine ⟨31492224967516872326279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1343668265280719885921237 31492224967516872326279)
                  ·
                    rfl

theorem cell22_275989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_275989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_275989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_275989 prefixEnd_275989 := by exact prefixLift 275989
  have htrace : WordTrace (prefixWord ++ tailWord_275989) baseStart_275989 baseEnd_275989 := by
    simpa [prefixWord, tailWord_275989, baseEnd_275989] using wordTrace_append hprefix tailTrace_275989
  have hstable : (prefixWord ++ tailWord_275989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275989).length < 2 ^ (prefixWord ++ tailWord_275989).sum := by decide
  have hdescent : baseEnd_275989 < baseStart_275989 := by decide
  rcases family_descends (prefixWord ++ tailWord_275989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276064 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_276064 : Nat := 118140960795 + 276064 * 2 ^ 59
def prefixEnd_276064 : Nat := 4983230072969 + 3 ^ 40 * 276064 * 2
def baseEnd_276064 : Nat := 94502348935275421353607

theorem tailTrace_276064 : CollatzResearch.WordTrace tailWord_276064 prefixEnd_276064 94502348935275421353607 := by
  unfold tailWord_276064
  simp only [CollatzResearch.WordTrace]
  refine ⟨5034440635937375411333623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6712587514583167215111497 5034440635937375411333623)
  ·
    refine ⟨7551660953906063117000435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5034440635937375411333623 7551660953906063117000435)
    ·
      refine ⟨11327491430859094675500653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7551660953906063117000435 11327491430859094675500653)
      ·
        refine ⟨4247809286572160503312745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11327491430859094675500653 4247809286572160503312745)
        ·
          refine ⟨3185856964929120377484559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4247809286572160503312745 3185856964929120377484559)
          ·
            refine ⟨4778785447393680566226839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185856964929120377484559 4778785447393680566226839)
            ·
              refine ⟨7168178171090520849340259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778785447393680566226839 7168178171090520849340259)
              ·
                refine ⟨10752267256635781274010389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7168178171090520849340259 10752267256635781274010389)
                ·
                  refine ⟨504012527654802247219237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10752267256635781274010389 504012527654802247219237)
                  ·
                    refine ⟨94502348935275421353607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 504012527654802247219237 94502348935275421353607)
                    ·
                      rfl

theorem cell22_276064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_276064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276064 prefixEnd_276064 := by exact prefixLift 276064
  have htrace : WordTrace (prefixWord ++ tailWord_276064) baseStart_276064 baseEnd_276064 := by
    simpa [prefixWord, tailWord_276064, baseEnd_276064] using wordTrace_append hprefix tailTrace_276064
  have hstable : (prefixWord ++ tailWord_276064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276064).length < 2 ^ (prefixWord ++ tailWord_276064).sum := by decide
  have hdescent : baseEnd_276064 < baseStart_276064 := by decide
  rcases family_descends (prefixWord ++ tailWord_276064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276100 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_276100 : Nat := 118140960795 + 276100 * 2 ^ 59
def prefixEnd_276100 : Nat := 4983230072969 + 3 ^ 40 * 276100 * 2
def baseEnd_276100 : Nat := 94514672470983327453497

theorem tailTrace_276100 : CollatzResearch.WordTrace tailWord_276100 prefixEnd_276100 94514672470983327453497 := by
  unfold tailWord_276100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035097149872164485488877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6713462866496219313985169 5035097149872164485488877)
  ·
    refine ⟨1888161431202061682058329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5035097149872164485488877 1888161431202061682058329)
    ·
      refine ⟨1416121073401546261543747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1888161431202061682058329 1416121073401546261543747)
      ·
        refine ⟨2124181610102319392315621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416121073401546261543747 2124181610102319392315621)
        ·
          refine ⟨398284051894184886059179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2124181610102319392315621 398284051894184886059179)
          ·
            refine ⟨597426077841277329088769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398284051894184886059179 597426077841277329088769)
            ·
              refine ⟨448069558380957996816577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597426077841277329088769 448069558380957996816577)
              ·
                refine ⟨336052168785718497612433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448069558380957996816577 336052168785718497612433)
                ·
                  refine ⟨252039126589288873209325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336052168785718497612433 252039126589288873209325)
                  ·
                    refine ⟨94514672470983327453497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252039126589288873209325 94514672470983327453497)
                    ·
                      rfl

theorem cell22_276100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_276100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276100 prefixEnd_276100 := by exact prefixLift 276100
  have htrace : WordTrace (prefixWord ++ tailWord_276100) baseStart_276100 baseEnd_276100 := by
    simpa [prefixWord, tailWord_276100, baseEnd_276100] using wordTrace_append hprefix tailTrace_276100
  have hstable : (prefixWord ++ tailWord_276100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276100).length < 2 ^ (prefixWord ++ tailWord_276100).sum := by decide
  have hdescent : baseEnd_276100 < baseStart_276100 := by decide
  rcases family_descends (prefixWord ++ tailWord_276100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276128 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 3, 3]
def baseStart_276128 : Nat := 118140960795 + 276128 * 2 ^ 59
def prefixEnd_276128 : Nat := 4983230072969 + 3 ^ 40 * 276128 * 2
def baseEnd_276128 : Nat := 94524257443200587753411

theorem tailTrace_276128 : CollatzResearch.WordTrace tailWord_276128 prefixEnd_276128 94524257443200587753411 := by
  unfold tailWord_276128
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035607771821444876498519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6714143695761926501998025 5035607771821444876498519)
  ·
    refine ⟨7553411657732167314747779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5035607771821444876498519 7553411657732167314747779)
    ·
      refine ⟨11330117486598250972121669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7553411657732167314747779 11330117486598250972121669)
      ·
        refine ⟨2124397028737172057272813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11330117486598250972121669 2124397028737172057272813)
        ·
          refine ⟨796648885776439521477305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2124397028737172057272813 796648885776439521477305)
          ·
            refine ⟨597486664332329641107979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 796648885776439521477305 597486664332329641107979)
            ·
              refine ⟨896229996498494461661969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597486664332329641107979 896229996498494461661969)
              ·
                refine ⟨672172497373870846246477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 896229996498494461661969 672172497373870846246477)
                ·
                  refine ⟨252064686515201567342429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672172497373870846246477 252064686515201567342429)
                  ·
                    refine ⟨94524257443200587753411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252064686515201567342429 94524257443200587753411)
                    ·
                      rfl

theorem cell22_276128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3, 3].length) (baseStart_276128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276128 prefixEnd_276128 := by exact prefixLift 276128
  have htrace : WordTrace (prefixWord ++ tailWord_276128) baseStart_276128 baseEnd_276128 := by
    simpa [prefixWord, tailWord_276128, baseEnd_276128] using wordTrace_append hprefix tailTrace_276128
  have hstable : (prefixWord ++ tailWord_276128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276128).length < 2 ^ (prefixWord ++ tailWord_276128).sum := by decide
  have hdescent : baseEnd_276128 < baseStart_276128 := by decide
  rcases family_descends (prefixWord ++ tailWord_276128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276130 : List Nat := [3, 3, 1, 4, 1, 1, 3, 6]
def baseStart_276130 : Nat := 118140960795 + 276130 * 2 ^ 59
def prefixEnd_276130 : Nat := 4983230072969 + 3 ^ 40 * 276130 * 2
def baseEnd_276130 : Nat := 10502771342674805467045

theorem tailTrace_276130 : CollatzResearch.WordTrace tailWord_276130 prefixEnd_276130 10502771342674805467045 := by
  unfold tailWord_276130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517822122408911023642461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6714192326423762729713229 2517822122408911023642461)
  ·
    refine ⟨944183295903341633865923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2517822122408911023642461 944183295903341633865923)
    ·
      refine ⟨1416274943855012450798885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 944183295903341633865923 1416274943855012450798885)
      ·
        refine ⟨265551551972814834524791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1416274943855012450798885 265551551972814834524791)
        ·
          refine ⟨398327327959222251787187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265551551972814834524791 398327327959222251787187)
          ·
            refine ⟨597490991938833377680781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398327327959222251787187 597490991938833377680781)
            ·
              refine ⟨224059121977062516630293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 597490991938833377680781 224059121977062516630293)
              ·
                refine ⟨10502771342674805467045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 224059121977062516630293 10502771342674805467045)
                ·
                  rfl

theorem cell22_276130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_276130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276130 prefixEnd_276130 := by exact prefixLift 276130
  have htrace : WordTrace (prefixWord ++ tailWord_276130) baseStart_276130 baseEnd_276130 := by
    simpa [prefixWord, tailWord_276130, baseEnd_276130] using wordTrace_append hprefix tailTrace_276130
  have hstable : (prefixWord ++ tailWord_276130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276130).length < 2 ^ (prefixWord ++ tailWord_276130).sum := by decide
  have hdescent : baseEnd_276130 < baseStart_276130 := by decide
  rcases family_descends (prefixWord ++ tailWord_276130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276141 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 7]
def baseStart_276141 : Nat := 118140960795 + 276141 * 2 ^ 59
def prefixEnd_276141 : Nat := 4983230072969 + 3 ^ 40 * 276141 * 2
def baseEnd_276141 : Nat := 31509569202957629059457

theorem tailTrace_276141 : CollatzResearch.WordTrace tailWord_276141 prefixEnd_276141 31509569202957629059457 := by
  unfold tailWord_276141
  simp only [CollatzResearch.WordTrace]
  refine ⟨10071689692595792973220277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6714459795063861982146851 10071689692595792973220277)
  ·
    refine ⟨944220908680855591239401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10071689692595792973220277 944220908680855591239401)
    ·
      refine ⟨708165681510641693429551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 944220908680855591239401 708165681510641693429551)
      ·
        refine ⟨1062248522265962540144327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708165681510641693429551 1062248522265962540144327)
        ·
          refine ⟨1593372783398943810216491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062248522265962540144327 1593372783398943810216491)
          ·
            refine ⟨2390059175098415715324737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593372783398943810216491 2390059175098415715324737)
            ·
              refine ⟨1792544381323811786493553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2390059175098415715324737 1792544381323811786493553)
              ·
                refine ⟨1344408285992858839870165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1792544381323811786493553 1344408285992858839870165)
                ·
                  refine ⟨31509569202957629059457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1344408285992858839870165 31509569202957629059457)
                  ·
                    rfl

theorem cell22_276141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_276141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276141 prefixEnd_276141 := by exact prefixLift 276141
  have htrace : WordTrace (prefixWord ++ tailWord_276141) baseStart_276141 baseEnd_276141 := by
    simpa [prefixWord, tailWord_276141, baseEnd_276141] using wordTrace_append hprefix tailTrace_276141
  have hstable : (prefixWord ++ tailWord_276141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276141).length < 2 ^ (prefixWord ++ tailWord_276141).sum := by decide
  have hdescent : baseEnd_276141 < baseStart_276141 := by decide
  rcases family_descends (prefixWord ++ tailWord_276141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276156 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_276156 : Nat := 118140960795 + 276156 * 2 ^ 59
def prefixEnd_276156 : Nat := 4983230072969 + 3 ^ 40 * 276156 * 2
def baseEnd_276156 : Nat := 94533842415417848053325

theorem tailTrace_276156 : CollatzResearch.WordTrace tailWord_276156 prefixEnd_276156 94533842415417848053325 := by
  unfold tailWord_276156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036118393770725267508161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6714824525027633690010881 5036118393770725267508161)
  ·
    refine ⟨3777088795328043950631121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5036118393770725267508161 3777088795328043950631121)
    ·
      refine ⟨2832816596496032962973341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3777088795328043950631121 2832816596496032962973341)
      ·
        refine ⟨1062306223686012361115003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2832816596496032962973341 1062306223686012361115003)
        ·
          refine ⟨1593459335529018541672505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062306223686012361115003 1593459335529018541672505)
          ·
            refine ⟨1195094501646763906254379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1593459335529018541672505 1195094501646763906254379)
            ·
              refine ⟨1792641752470145859381569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195094501646763906254379 1792641752470145859381569)
              ·
                refine ⟨1344481314352609394536177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1792641752470145859381569 1344481314352609394536177)
                ·
                  refine ⟨1008360985764457045902133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344481314352609394536177 1008360985764457045902133)
                  ·
                    refine ⟨94533842415417848053325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1008360985764457045902133 94533842415417848053325)
                    ·
                      rfl

theorem cell22_276156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_276156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276156 prefixEnd_276156 := by exact prefixLift 276156
  have htrace : WordTrace (prefixWord ++ tailWord_276156) baseStart_276156 baseEnd_276156 := by
    simpa [prefixWord, tailWord_276156, baseEnd_276156] using wordTrace_append hprefix tailTrace_276156
  have hstable : (prefixWord ++ tailWord_276156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276156).length < 2 ^ (prefixWord ++ tailWord_276156).sum := by decide
  have hdescent : baseEnd_276156 < baseStart_276156 := by decide
  rcases family_descends (prefixWord ++ tailWord_276156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276158 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_276158 : Nat := 118140960795 + 276158 * 2 ^ 59
def prefixEnd_276158 : Nat := 4983230072969 + 3 ^ 40 * 276158 * 2
def baseEnd_276158 : Nat := 31511509018763503167773

theorem tailTrace_276158 : CollatzResearch.WordTrace tailWord_276158 prefixEnd_276158 31511509018763503167773 := by
  unfold tailWord_276158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259038716691775609573641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6714873155689469917726085 1259038716691775609573641)
  ·
    refine ⟨944279037518831707180231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1259038716691775609573641 944279037518831707180231)
    ·
      refine ⟨1416418556278247560770347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 944279037518831707180231 1416418556278247560770347)
      ·
        refine ⟨2124627834417371341155521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416418556278247560770347 2124627834417371341155521)
        ·
          refine ⟨1593470875813028505866641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2124627834417371341155521 1593470875813028505866641)
          ·
            refine ⟨1195103156859771379399981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1593470875813028505866641 1195103156859771379399981)
            ·
              refine ⟨448163683822414267274993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1195103156859771379399981 448163683822414267274993)
              ·
                refine ⟨336122762866810700456245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448163683822414267274993 336122762866810700456245)
                ·
                  refine ⟨31511509018763503167773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 336122762866810700456245 31511509018763503167773)
                  ·
                    rfl

theorem cell22_276158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_276158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276158 prefixEnd_276158 := by exact prefixLift 276158
  have htrace : WordTrace (prefixWord ++ tailWord_276158) baseStart_276158 baseEnd_276158 := by
    simpa [prefixWord, tailWord_276158, baseEnd_276158] using wordTrace_append hprefix tailTrace_276158
  have hstable : (prefixWord ++ tailWord_276158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276158).length < 2 ^ (prefixWord ++ tailWord_276158).sum := by decide
  have hdescent : baseEnd_276158 < baseStart_276158 := by decide
  rcases family_descends (prefixWord ++ tailWord_276158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276186 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_276186 : Nat := 118140960795 + 276186 * 2 ^ 59
def prefixEnd_276186 : Nat := 4983230072969 + 3 ^ 40 * 276186 * 2
def baseEnd_276186 : Nat := 31514704009502589934411

theorem tailTrace_276186 : CollatzResearch.WordTrace tailWord_276186 prefixEnd_276186 31514704009502589934411 := by
  unfold tailWord_276186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2518332744358191414652103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6715553984955177105738941 2518332744358191414652103)
  ·
    refine ⟨3777499116537287121978155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2518332744358191414652103 3777499116537287121978155)
    ·
      refine ⟨5666248674805930682967233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3777499116537287121978155 5666248674805930682967233)
      ·
        refine ⟨4249686506104448012225425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5666248674805930682967233 4249686506104448012225425)
        ·
          refine ⟨3187264879578336009169069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4249686506104448012225425 3187264879578336009169069)
          ·
            refine ⟨1195224329841876003438401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3187264879578336009169069 1195224329841876003438401)
            ·
              refine ⟨896418247381407002578801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195224329841876003438401 896418247381407002578801)
              ·
                refine ⟨672313685536055251934101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 896418247381407002578801 672313685536055251934101)
                ·
                  refine ⟨31514704009502589934411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 672313685536055251934101 31514704009502589934411)
                  ·
                    rfl

theorem cell22_276186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_276186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276186 prefixEnd_276186 := by exact prefixLift 276186
  have htrace : WordTrace (prefixWord ++ tailWord_276186) baseStart_276186 baseEnd_276186 := by
    simpa [prefixWord, tailWord_276186, baseEnd_276186] using wordTrace_append hprefix tailTrace_276186
  have hstable : (prefixWord ++ tailWord_276186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276186).length < 2 ^ (prefixWord ++ tailWord_276186).sum := by decide
  have hdescent : baseEnd_276186 < baseStart_276186 := by decide
  rcases family_descends (prefixWord ++ tailWord_276186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276203 : List Nat := [1, 1, 1, 1, 2, 4, 5, 3, 4]
def baseStart_276203 : Nat := 118140960795 + 276203 * 2 ^ 59
def prefixEnd_276203 : Nat := 4983230072969 + 3 ^ 40 * 276203 * 2
def baseEnd_276203 : Nat := 31516643825308464042727

theorem tailTrace_276203 : CollatzResearch.WordTrace tailWord_276203 prefixEnd_276203 31516643825308464042727 := by
  unfold tailWord_276203
  simp only [CollatzResearch.WordTrace]
  refine ⟨10073951018371177561977263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6715967345580785041318175 10073951018371177561977263)
  ·
    refine ⟨15110926527556766342965895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10073951018371177561977263 15110926527556766342965895)
    ·
      refine ⟨22666389791335149514448843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15110926527556766342965895 22666389791335149514448843)
      ·
        refine ⟨33999584687002724271673265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22666389791335149514448843 33999584687002724271673265)
        ·
          refine ⟨25499688515252043203754949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33999584687002724271673265 25499688515252043203754949)
          ·
            refine ⟨4781191596609758100704053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25499688515252043203754949 4781191596609758100704053)
            ·
              refine ⟨448236712182164821941005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4781191596609758100704053 448236712182164821941005)
              ·
                refine ⟨168088767068311808227877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448236712182164821941005 168088767068311808227877)
                ·
                  refine ⟨31516643825308464042727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168088767068311808227877 31516643825308464042727)
                  ·
                    rfl

theorem cell22_276203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 4].length) (baseStart_276203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276203 prefixEnd_276203 := by exact prefixLift 276203
  have htrace : WordTrace (prefixWord ++ tailWord_276203) baseStart_276203 baseEnd_276203 := by
    simpa [prefixWord, tailWord_276203, baseEnd_276203] using wordTrace_append hprefix tailTrace_276203
  have hstable : (prefixWord ++ tailWord_276203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276203).length < 2 ^ (prefixWord ++ tailWord_276203).sum := by decide
  have hdescent : baseEnd_276203 < baseStart_276203 := by decide
  rcases family_descends (prefixWord ++ tailWord_276203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276218 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 2, 3]
def baseStart_276218 : Nat := 118140960795 + 276218 * 2 ^ 59
def prefixEnd_276218 : Nat := 4983230072969 + 3 ^ 40 * 276218 * 2
def baseEnd_276218 : Nat := 94555066282470353003135

theorem tailTrace_276218 : CollatzResearch.WordTrace tailWord_276218 prefixEnd_276218 94555066282470353003135 := by
  unfold tailWord_276218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2518624528329208780943327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6716332075544556749182205 2518624528329208780943327)
  ·
    refine ⟨3777936792493813171414991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2518624528329208780943327 3777936792493813171414991)
    ·
      refine ⟨5666905188740719757122487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3777936792493813171414991 5666905188740719757122487)
      ·
        refine ⟨8500357783111079635683731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5666905188740719757122487 8500357783111079635683731)
        ·
          refine ⟨12750536674666619453525597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8500357783111079635683731 12750536674666619453525597)
          ·
            refine ⟨4781451252999982295072099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12750536674666619453525597 4781451252999982295072099)
            ·
              refine ⟨7172176879499973442608149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4781451252999982295072099 7172176879499973442608149)
              ·
                refine ⟨336195791226561255122257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7172176879499973442608149 336195791226561255122257)
                ·
                  refine ⟨252146843419920941341693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336195791226561255122257 252146843419920941341693)
                  ·
                    refine ⟨94555066282470353003135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252146843419920941341693 94555066282470353003135)
                    ·
                      rfl

theorem cell22_276218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_276218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276218 prefixEnd_276218 := by exact prefixLift 276218
  have htrace : WordTrace (prefixWord ++ tailWord_276218) baseStart_276218 baseEnd_276218 := by
    simpa [prefixWord, tailWord_276218, baseEnd_276218] using wordTrace_append hprefix tailTrace_276218
  have hstable : (prefixWord ++ tailWord_276218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276218).length < 2 ^ (prefixWord ++ tailWord_276218).sum := by decide
  have hdescent : baseEnd_276218 < baseStart_276218 := by decide
  rcases family_descends (prefixWord ++ tailWord_276218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276220 : List Nat := [2, 2, 2, 1, 3, 1, 5, 2, 4]
def baseStart_276220 : Nat := 118140960795 + 276220 * 2 ^ 59
def prefixEnd_276220 : Nat := 4983230072969 + 3 ^ 40 * 276220 * 2
def baseEnd_276220 : Nat := 31518583641114338151043

theorem tailTrace_276220 : CollatzResearch.WordTrace tailWord_276220 prefixEnd_276220 31518583641114338151043 := by
  unfold tailWord_276220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5037285529654794732673057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6716380706206392976897409 5037285529654794732673057)
  ·
    refine ⟨3777964147241096049504793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5037285529654794732673057 3777964147241096049504793)
    ·
      refine ⟨2833473110430822037128595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3777964147241096049504793 2833473110430822037128595)
      ·
        refine ⟨4250209665646233055692893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2833473110430822037128595 4250209665646233055692893)
        ·
          refine ⟨1593828624617337395884835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4250209665646233055692893 1593828624617337395884835)
          ·
            refine ⟨2390742936926006093827253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593828624617337395884835 2390742936926006093827253)
            ·
              refine ⟨224132150336813071296305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2390742936926006093827253 224132150336813071296305)
              ·
                refine ⟨168099112752609803472229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224132150336813071296305 168099112752609803472229)
                ·
                  refine ⟨31518583641114338151043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168099112752609803472229 31518583641114338151043)
                  ·
                    rfl

theorem cell22_276220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_276220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276220 prefixEnd_276220 := by exact prefixLift 276220
  have htrace : WordTrace (prefixWord ++ tailWord_276220) baseStart_276220 baseEnd_276220 := by
    simpa [prefixWord, tailWord_276220, baseEnd_276220] using wordTrace_append hprefix tailTrace_276220
  have hstable : (prefixWord ++ tailWord_276220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276220).length < 2 ^ (prefixWord ++ tailWord_276220).sum := by decide
  have hdescent : baseEnd_276220 < baseStart_276220 := by decide
  rcases family_descends (prefixWord ++ tailWord_276220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276235 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 2, 3]
def baseStart_276235 : Nat := 118140960795 + 276235 * 2 ^ 59
def prefixEnd_276235 : Nat := 4983230072969 + 3 ^ 40 * 276235 * 2
def baseEnd_276235 : Nat := 94560885729887975328083

theorem tailTrace_276235 : CollatzResearch.WordTrace tailWord_276235 prefixEnd_276235 94560885729887975328083 := by
  unfold tailWord_276235
  simp only [CollatzResearch.WordTrace]
  refine ⟨10075118154255247027142159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6716745436170164684761439 10075118154255247027142159)
  ·
    refine ⟨15112677231382870540713239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10075118154255247027142159 15112677231382870540713239)
    ·
      refine ⟨22669015847074305811069859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15112677231382870540713239 22669015847074305811069859)
      ·
        refine ⟨34003523770611458716604789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22669015847074305811069859 34003523770611458716604789)
        ·
          refine ⟨3187830353494824254681699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34003523770611458716604789 3187830353494824254681699)
          ·
            refine ⟨4781745530242236382022549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3187830353494824254681699 4781745530242236382022549)
            ·
              refine ⟨224144321730104830407307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4781745530242236382022549 224144321730104830407307)
              ·
                refine ⟨336216482595157245610961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224144321730104830407307 336216482595157245610961)
                ·
                  refine ⟨252162361946367934208221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336216482595157245610961 252162361946367934208221)
                  ·
                    refine ⟨94560885729887975328083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252162361946367934208221 94560885729887975328083)
                    ·
                      rfl

theorem cell22_276235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 2, 3].length) (baseStart_276235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276235 prefixEnd_276235 := by exact prefixLift 276235
  have htrace : WordTrace (prefixWord ++ tailWord_276235) baseStart_276235 baseEnd_276235 := by
    simpa [prefixWord, tailWord_276235, baseEnd_276235] using wordTrace_append hprefix tailTrace_276235
  have hstable : (prefixWord ++ tailWord_276235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276235).length < 2 ^ (prefixWord ++ tailWord_276235).sum := by decide
  have hdescent : baseEnd_276235 < baseStart_276235 := by decide
  rcases family_descends (prefixWord ++ tailWord_276235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276291 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 1, 7]
def baseStart_276291 : Nat := 118140960795 + 276291 * 2 ^ 59
def prefixEnd_276291 : Nat := 4983230072969 + 3 ^ 40 * 276291 * 2
def baseEnd_276291 : Nat := 94580055674322495927911

theorem tailTrace_276291 : CollatzResearch.WordTrace tailWord_276291 prefixEnd_276291 94580055674322495927911 := by
  unfold tailWord_276291
  simp only [CollatzResearch.WordTrace]
  refine ⟨10077160642052368591180727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6718107094701579060787151 10077160642052368591180727)
  ·
    refine ⟨15115740963078552886771091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10077160642052368591180727 15115740963078552886771091)
    ·
      refine ⟨22673611444617829330156637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15115740963078552886771091 22673611444617829330156637)
      ·
        refine ⟨8502604291731685998808739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22673611444617829330156637 8502604291731685998808739)
        ·
          refine ⟨12753906437597528998213109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8502604291731685998808739 12753906437597528998213109)
          ·
            refine ⟨1195678728524768343582479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12753906437597528998213109 1195678728524768343582479)
            ·
              refine ⟨1793518092787152515373719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195678728524768343582479 1793518092787152515373719)
              ·
                refine ⟨2690277139180728773060579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793518092787152515373719 2690277139180728773060579)
                ·
                  refine ⟨4035415708771093159590869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2690277139180728773060579 4035415708771093159590869)
                  ·
                    refine ⟨94580055674322495927911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4035415708771093159590869 94580055674322495927911)
                    ·
                      rfl

theorem cell22_276291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_276291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276291 prefixEnd_276291 := by exact prefixLift 276291
  have htrace : WordTrace (prefixWord ++ tailWord_276291) baseStart_276291 baseEnd_276291 := by
    simpa [prefixWord, tailWord_276291, baseEnd_276291] using wordTrace_append hprefix tailTrace_276291
  have hstable : (prefixWord ++ tailWord_276291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276291).length < 2 ^ (prefixWord ++ tailWord_276291).sum := by decide
  have hdescent : baseEnd_276291 < baseStart_276291 := by decide
  rcases family_descends (prefixWord ++ tailWord_276291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276321 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 8]
def baseStart_276321 : Nat := 118140960795 + 276321 * 2 ^ 59
def prefixEnd_276321 : Nat := 4983230072969 + 3 ^ 40 * 276321 * 2
def baseEnd_276321 : Nat := 31530108429137472559273

theorem tailTrace_276321 : CollatzResearch.WordTrace tailWord_276321 prefixEnd_276321 31530108429137472559273 := by
  unfold tailWord_276321
  simp only [CollatzResearch.WordTrace]
  refine ⟨10078254831943683714772817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6718836554629122476515211 10078254831943683714772817)
  ·
    refine ⟨7558691123957762786079613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10078254831943683714772817 7558691123957762786079613)
    ·
      refine ⟨2834509171484161044779855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7558691123957762786079613 2834509171484161044779855)
      ·
        refine ⟨4251763757226241567169783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2834509171484161044779855 4251763757226241567169783)
        ·
          refine ⟨6377645635839362350754675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4251763757226241567169783 6377645635839362350754675)
          ·
            refine ⟨9566468453759043526132013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6377645635839362350754675 9566468453759043526132013)
            ·
              refine ⟨3587425670159641322299505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9566468453759043526132013 3587425670159641322299505)
              ·
                refine ⟨2690569252619730991724629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587425670159641322299505 2690569252619730991724629)
                ·
                  refine ⟨31530108429137472559273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2690569252619730991724629 31530108429137472559273)
                  ·
                    rfl

theorem cell22_276321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_276321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276321 prefixEnd_276321 := by exact prefixLift 276321
  have htrace : WordTrace (prefixWord ++ tailWord_276321) baseStart_276321 baseEnd_276321 := by
    simpa [prefixWord, tailWord_276321, baseEnd_276321] using wordTrace_append hprefix tailTrace_276321
  have hstable : (prefixWord ++ tailWord_276321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276321).length < 2 ^ (prefixWord ++ tailWord_276321).sum := by decide
  have hdescent : baseEnd_276321 < baseStart_276321 := by decide
  rcases family_descends (prefixWord ++ tailWord_276321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276372 : List Nat := [2, 4, 2, 1, 1, 2, 3, 3, 4]
def baseStart_276372 : Nat := 118140960795 + 276372 * 2 ^ 59
def prefixEnd_276372 : Nat := 4983230072969 + 3 ^ 40 * 276372 * 2
def baseEnd_276372 : Nat := 31535927876555094884221

theorem tailTrace_276372 : CollatzResearch.WordTrace tailWord_276372 prefixEnd_276372 31535927876555094884221 := by
  unfold tailWord_276372
  simp only [CollatzResearch.WordTrace]
  refine ⟨5040057477379459712439685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6720076636505946283252913 5040057477379459712439685)
  ·
    refine ⟨945010777008648696082441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5040057477379459712439685 945010777008648696082441)
    ·
      refine ⟨708758082756486522061831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 945010777008648696082441 708758082756486522061831)
      ·
        refine ⟨1063137124134729783092747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708758082756486522061831 1063137124134729783092747)
        ·
          refine ⟨1594705686202094674639121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063137124134729783092747 1594705686202094674639121)
          ·
            refine ⟨1196029264651571005979341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1594705686202094674639121 1196029264651571005979341)
            ·
              refine ⟨448510974244339127242253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1196029264651571005979341 448510974244339127242253)
              ·
                refine ⟨168191615341627172715845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448510974244339127242253 168191615341627172715845)
                ·
                  refine ⟨31535927876555094884221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168191615341627172715845 31535927876555094884221)
                  ·
                    rfl

theorem cell22_276372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_276372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276372 prefixEnd_276372 := by exact prefixLift 276372
  have htrace : WordTrace (prefixWord ++ tailWord_276372) baseStart_276372 baseEnd_276372 := by
    simpa [prefixWord, tailWord_276372, baseEnd_276372] using wordTrace_append hprefix tailTrace_276372
  have hstable : (prefixWord ++ tailWord_276372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276372).length < 2 ^ (prefixWord ++ tailWord_276372).sum := by decide
  have hdescent : baseEnd_276372 < baseStart_276372 := by decide
  rcases family_descends (prefixWord ++ tailWord_276372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276449 : List Nat := [1, 2, 3, 1, 2, 1, 6, 2, 1, 3]
def baseStart_276449 : Nat := 118140960795 + 276449 * 2 ^ 59
def prefixEnd_276449 : Nat := 4983230072969 + 3 ^ 40 * 276449 * 2
def baseEnd_276449 : Nat := 94634142303262750477427

theorem tailTrace_276449 : CollatzResearch.WordTrace tailWord_276449 prefixEnd_276449 94634142303262750477427 := by
  unfold tailWord_276449
  simp only [CollatzResearch.WordTrace]
  refine ⟨10082923375479961575432401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6721948916986641050288267 10082923375479961575432401)
  ·
    refine ⟨7562192531609971181574301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10082923375479961575432401 7562192531609971181574301)
    ·
      refine ⟨2835822199353739193090363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7562192531609971181574301 2835822199353739193090363)
      ·
        refine ⟨4253733299030608789635545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2835822199353739193090363 4253733299030608789635545)
        ·
          refine ⟨3190299974272956592226659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4253733299030608789635545 3190299974272956592226659)
          ·
            refine ⟨4785449961409434888339989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190299974272956592226659 4785449961409434888339989)
            ·
              refine ⟨224317966941067260390937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4785449961409434888339989 224317966941067260390937)
              ·
                refine ⟨168238475205800445293203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224317966941067260390937 168238475205800445293203)
                ·
                  refine ⟨252357712808700667939805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168238475205800445293203 252357712808700667939805)
                  ·
                    refine ⟨94634142303262750477427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252357712808700667939805 94634142303262750477427)
                    ·
                      rfl

theorem cell22_276449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_276449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276449 prefixEnd_276449 := by exact prefixLift 276449
  have htrace : WordTrace (prefixWord ++ tailWord_276449) baseStart_276449 baseEnd_276449 := by
    simpa [prefixWord, tailWord_276449, baseEnd_276449] using wordTrace_append hprefix tailTrace_276449
  have hstable : (prefixWord ++ tailWord_276449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276449).length < 2 ^ (prefixWord ++ tailWord_276449).sum := by decide
  have hdescent : baseEnd_276449 < baseStart_276449 := by decide
  rcases family_descends (prefixWord ++ tailWord_276449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276473 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 8]
def baseStart_276473 : Nat := 118140960795 + 276473 * 2 ^ 59
def prefixEnd_276473 : Nat := 4983230072969 + 3 ^ 40 * 276473 * 2
def baseEnd_276473 : Nat := 31547452664578229292451

theorem tailTrace_276473 : CollatzResearch.WordTrace tailWord_276473 prefixEnd_276473 31547452664578229292451 := by
  unfold tailWord_276473
  simp only [CollatzResearch.WordTrace]
  refine ⟨10083798727393013674306073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6722532484928675782870715 10083798727393013674306073)
  ·
    refine ⟨7562849045544760255729555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10083798727393013674306073 7562849045544760255729555)
    ·
      refine ⟨11344273568317140383594333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7562849045544760255729555 11344273568317140383594333)
      ·
        refine ⟨4254102588118927643847875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11344273568317140383594333 4254102588118927643847875)
        ·
          refine ⟨6381153882178391465771813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4254102588118927643847875 6381153882178391465771813)
          ·
            refine ⟨1196466352908448399832215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6381153882178391465771813 1196466352908448399832215)
            ·
              refine ⟨1794699529362672599748323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196466352908448399832215 1794699529362672599748323)
              ·
                refine ⟨2692049294044008899622485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794699529362672599748323 2692049294044008899622485)
                ·
                  refine ⟨31547452664578229292451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2692049294044008899622485 31547452664578229292451)
                  ·
                    rfl

theorem cell22_276473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_276473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276473 prefixEnd_276473 := by exact prefixLift 276473
  have htrace : WordTrace (prefixWord ++ tailWord_276473) baseStart_276473 baseEnd_276473 := by
    simpa [prefixWord, tailWord_276473, baseEnd_276473] using wordTrace_append hprefix tailTrace_276473
  have hstable : (prefixWord ++ tailWord_276473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276473).length < 2 ^ (prefixWord ++ tailWord_276473).sum := by decide
  have hdescent : baseEnd_276473 < baseStart_276473 := by decide
  rcases family_descends (prefixWord ++ tailWord_276473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276522 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_276522 : Nat := 118140960795 + 276522 * 2 ^ 59
def prefixEnd_276522 : Nat := 4983230072969 + 3 ^ 40 * 276522 * 2
def baseEnd_276522 : Nat := 94659131695114893402203

theorem tailTrace_276522 : CollatzResearch.WordTrace tailWord_276522 prefixEnd_276522 94659131695114893402203 := by
  unfold tailWord_276522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2521396476053873760709955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6723723936143663361893213 2521396476053873760709955)
  ·
    refine ⟨3782094714080810641064933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2521396476053873760709955 3782094714080810641064933)
    ·
      refine ⟨709142758890151995199675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3782094714080810641064933 709142758890151995199675)
      ·
        refine ⟨1063714138335227992799513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709142758890151995199675 1063714138335227992799513)
        ·
          refine ⟨797785603751420994599635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1063714138335227992799513 797785603751420994599635)
          ·
            refine ⟨1196678405627131491899453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797785603751420994599635 1196678405627131491899453)
            ·
              refine ⟨448754402110174309462295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1196678405627131491899453 448754402110174309462295)
              ·
                refine ⟨673131603165261464193443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448754402110174309462295 673131603165261464193443)
                ·
                  refine ⟨1009697404747892196290165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673131603165261464193443 1009697404747892196290165)
                  ·
                    refine ⟨94659131695114893402203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1009697404747892196290165 94659131695114893402203)
                    ·
                      rfl

theorem cell22_276522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_276522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276522 prefixEnd_276522 := by exact prefixLift 276522
  have htrace : WordTrace (prefixWord ++ tailWord_276522) baseStart_276522 baseEnd_276522 := by
    simpa [prefixWord, tailWord_276522, baseEnd_276522] using wordTrace_append hprefix tailTrace_276522
  have hstable : (prefixWord ++ tailWord_276522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276522).length < 2 ^ (prefixWord ++ tailWord_276522).sum := by decide
  have hdescent : baseEnd_276522 < baseStart_276522 := by decide
  rcases family_descends (prefixWord ++ tailWord_276522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276535 : List Nat := [1, 1, 3, 1, 2, 2, 6, 6]
def baseStart_276535 : Nat := 118140960795 + 276535 * 2 ^ 59
def prefixEnd_276535 : Nat := 4983230072969 + 3 ^ 40 * 276535 * 2
def baseEnd_276535 : Nat := 10518175762309688091907

theorem tailTrace_276535 : CollatzResearch.WordTrace tailWord_276535 prefixEnd_276535 10518175762309688091907 := by
  unfold tailWord_276535
  simp only [CollatzResearch.WordTrace]
  refine ⟨10086060053168398263063059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6724040035445598842042039 10086060053168398263063059)
  ·
    refine ⟨15129090079752597394594589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10086060053168398263063059 15129090079752597394594589)
    ·
      refine ⟨5673408779907224022972971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15129090079752597394594589 5673408779907224022972971)
      ·
        refine ⟨8510113169860836034459457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5673408779907224022972971 8510113169860836034459457)
        ·
          refine ⟨6382584877395627025844593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8510113169860836034459457 6382584877395627025844593)
          ·
            refine ⟨4786938658046720269383445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6382584877395627025844593 4786938658046720269383445)
            ·
              refine ⟨224387749595940012627349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4786938658046720269383445 224387749595940012627349)
              ·
                refine ⟨10518175762309688091907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 224387749595940012627349 10518175762309688091907)
                ·
                  rfl

theorem cell22_276535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 6].length) (baseStart_276535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276535 prefixEnd_276535 := by exact prefixLift 276535
  have htrace : WordTrace (prefixWord ++ tailWord_276535) baseStart_276535 baseEnd_276535 := by
    simpa [prefixWord, tailWord_276535, baseEnd_276535] using wordTrace_append hprefix tailTrace_276535
  have hstable : (prefixWord ++ tailWord_276535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276535).length < 2 ^ (prefixWord ++ tailWord_276535).sum := by decide
  have hdescent : baseEnd_276535 < baseStart_276535 := by decide
  rcases family_descends (prefixWord ++ tailWord_276535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276563 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 11]
def baseStart_276563 : Nat := 118140960795 + 276563 * 2 ^ 59
def prefixEnd_276563 : Nat := 4983230072969 + 3 ^ 40 * 276563 * 2
def baseEnd_276563 : Nat := 31557722277668151042359

theorem tailTrace_276563 : CollatzResearch.WordTrace tailWord_276563 prefixEnd_276563 31557722277668151042359 := by
  unfold tailWord_276563
  simp only [CollatzResearch.WordTrace]
  refine ⟨10087081297066959045082343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6724720864711306030054895 10087081297066959045082343)
  ·
    refine ⟨15130621945600438567623515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10087081297066959045082343 15130621945600438567623515)
    ·
      refine ⟨22695932918400657851435273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15130621945600438567623515 22695932918400657851435273)
      ·
        refine ⟨17021949688800493388576455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22695932918400657851435273 17021949688800493388576455)
        ·
          refine ⟨25532924533200740082864683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17021949688800493388576455 25532924533200740082864683)
          ·
            refine ⟨38299386799801110124297025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25532924533200740082864683 38299386799801110124297025)
            ·
              refine ⟨28724540099850832593222769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38299386799801110124297025 28724540099850832593222769)
              ·
                refine ⟨21543405074888124444917077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28724540099850832593222769 21543405074888124444917077)
                ·
                  refine ⟨31557722277668151042359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 21543405074888124444917077 31557722277668151042359)
                  ·
                    rfl

theorem cell22_276563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 11].length) (baseStart_276563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276563 prefixEnd_276563 := by exact prefixLift 276563
  have htrace : WordTrace (prefixWord ++ tailWord_276563) baseStart_276563 baseEnd_276563 := by
    simpa [prefixWord, tailWord_276563, baseEnd_276563] using wordTrace_append hprefix tailTrace_276563
  have hstable : (prefixWord ++ tailWord_276563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276563).length < 2 ^ (prefixWord ++ tailWord_276563).sum := by decide
  have hdescent : baseEnd_276563 < baseStart_276563 := by decide
  rcases family_descends (prefixWord ++ tailWord_276563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276567 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 3, 3]
def baseStart_276567 : Nat := 118140960795 + 276567 * 2 ^ 59
def prefixEnd_276567 : Nat := 4983230072969 + 3 ^ 40 * 276567 * 2
def baseEnd_276567 : Nat := 94674536114749776027065

theorem tailTrace_276567 : CollatzResearch.WordTrace tailWord_276567 prefixEnd_276567 94674536114749776027065 := by
  unfold tailWord_276567
  simp only [CollatzResearch.WordTrace]
  refine ⟨10087227189052467728227955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6724818126034978485485303 10087227189052467728227955)
  ·
    refine ⟨15130840783578701592341933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10087227189052467728227955 15130840783578701592341933)
    ·
      refine ⟨5674065293842013097128225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15130840783578701592341933 5674065293842013097128225)
      ·
        refine ⟨4255548970381509822846169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5674065293842013097128225 4255548970381509822846169)
        ·
          refine ⟨3191661727786132367134627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4255548970381509822846169 3191661727786132367134627)
          ·
            refine ⟨4787492591679198550701941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191661727786132367134627 4787492591679198550701941)
            ·
              refine ⟨448827430469924864128307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4787492591679198550701941 448827430469924864128307)
              ·
                refine ⟨673241145704887296192461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448827430469924864128307 673241145704887296192461)
                ·
                  refine ⟨252465429639332736072173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673241145704887296192461 252465429639332736072173)
                  ·
                    refine ⟨94674536114749776027065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252465429639332736072173 94674536114749776027065)
                    ·
                      rfl

theorem cell22_276567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_276567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276567 prefixEnd_276567 := by exact prefixLift 276567
  have htrace : WordTrace (prefixWord ++ tailWord_276567) baseStart_276567 baseEnd_276567 := by
    simpa [prefixWord, tailWord_276567, baseEnd_276567] using wordTrace_append hprefix tailTrace_276567
  have hstable : (prefixWord ++ tailWord_276567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276567).length < 2 ^ (prefixWord ++ tailWord_276567).sum := by decide
  have hdescent : baseEnd_276567 < baseStart_276567 := by decide
  rcases family_descends (prefixWord ++ tailWord_276567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276573 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_276573 : Nat := 118140960795 + 276573 * 2 ^ 59
def prefixEnd_276573 : Nat := 4983230072969 + 3 ^ 40 * 276573 * 2
def baseEnd_276573 : Nat := 94676590037367760377047

theorem tailTrace_276573 : CollatzResearch.WordTrace tailWord_276573 prefixEnd_276573 94676590037367760377047 := by
  unfold tailWord_276573
  simp only [CollatzResearch.WordTrace]
  refine ⟨10087446027030730752946373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6724964018020487168630915 10087446027030730752946373)
  ·
    refine ⟨1891396130068262016177445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10087446027030730752946373 1891396130068262016177445)
    ·
      refine ⟨354636774387799128033271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1891396130068262016177445 354636774387799128033271)
      ·
        refine ⟨531955161581698692049907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354636774387799128033271 531955161581698692049907)
        ·
          refine ⟨797932742372548038074861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531955161581698692049907 797932742372548038074861)
          ·
            refine ⟨299224778389705514278073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 797932742372548038074861 299224778389705514278073)
            ·
              refine ⟨224418583792279135708555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299224778389705514278073 224418583792279135708555)
              ·
                refine ⟨336627875688418703562833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224418583792279135708555 336627875688418703562833)
                ·
                  refine ⟨252470906766314027672125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336627875688418703562833 252470906766314027672125)
                  ·
                    refine ⟨94676590037367760377047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252470906766314027672125 94676590037367760377047)
                    ·
                      rfl

theorem cell22_276573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_276573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276573 prefixEnd_276573 := by exact prefixLift 276573
  have htrace : WordTrace (prefixWord ++ tailWord_276573) baseStart_276573 baseEnd_276573 := by
    simpa [prefixWord, tailWord_276573, baseEnd_276573] using wordTrace_append hprefix tailTrace_276573
  have hstable : (prefixWord ++ tailWord_276573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276573).length < 2 ^ (prefixWord ++ tailWord_276573).sum := by decide
  have hdescent : baseEnd_276573 < baseStart_276573 := by decide
  rcases family_descends (prefixWord ++ tailWord_276573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276618 : List Nat := [3, 1, 2, 3, 1, 4, 2, 2, 1, 3]
def baseStart_276618 : Nat := 118140960795 + 276618 * 2 ^ 59
def prefixEnd_276618 : Nat := 4983230072969 + 3 ^ 40 * 276618 * 2
def baseEnd_276618 : Nat := 94691994457002643001909

theorem tailTrace_276618 : CollatzResearch.WordTrace tailWord_276618 prefixEnd_276618 94691994457002643001909 := by
  unfold tailWord_276618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2522271827966925859583627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6726058207911802292223005 2522271827966925859583627)
  ·
    refine ⟨3783407741950388789375441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2522271827966925859583627 3783407741950388789375441)
    ·
      refine ⟨2837555806462791592031581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3783407741950388789375441 2837555806462791592031581)
      ·
        refine ⟨1064083427423546847011843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2837555806462791592031581 1064083427423546847011843)
        ·
          refine ⟨1596125141135320270517765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064083427423546847011843 1596125141135320270517765)
          ·
            refine ⟨299273463962872550722081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1596125141135320270517765 299273463962872550722081)
            ·
              refine ⟨224455097972154413041561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299273463962872550722081 224455097972154413041561)
              ·
                refine ⟨168341323479115809781171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224455097972154413041561 168341323479115809781171)
                ·
                  refine ⟨252511985218673714671757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168341323479115809781171 252511985218673714671757)
                  ·
                    refine ⟨94691994457002643001909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252511985218673714671757 94691994457002643001909)
                    ·
                      rfl

theorem cell22_276618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_276618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276618 prefixEnd_276618 := by exact prefixLift 276618
  have htrace : WordTrace (prefixWord ++ tailWord_276618) baseStart_276618 baseEnd_276618 := by
    simpa [prefixWord, tailWord_276618, baseEnd_276618] using wordTrace_append hprefix tailTrace_276618
  have hstable : (prefixWord ++ tailWord_276618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276618).length < 2 ^ (prefixWord ++ tailWord_276618).sum := by decide
  have hdescent : baseEnd_276618 < baseStart_276618 := by decide
  rcases family_descends (prefixWord ++ tailWord_276618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276642 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_276642 : Nat := 118140960795 + 276642 * 2 ^ 59
def prefixEnd_276642 : Nat := 4983230072969 + 3 ^ 40 * 276642 * 2
def baseEnd_276642 : Nat := 31566736715824860133945

theorem tailTrace_276642 : CollatzResearch.WordTrace tailWord_276642 prefixEnd_276642 31566736715824860133945 := by
  unfold tailWord_276642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2522490665945188884302045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6726641775853837024805453 2522490665945188884302045)
  ·
    refine ⟨945933999729445831613267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2522490665945188884302045 945933999729445831613267)
    ·
      refine ⟨1418900999594168747419901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 945933999729445831613267 1418900999594168747419901)
      ·
        refine ⟨532087874847813280282463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1418900999594168747419901 532087874847813280282463)
        ·
          refine ⟨798131812271719920423695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532087874847813280282463 798131812271719920423695)
          ·
            refine ⟨1197197718407579880635543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798131812271719920423695 1197197718407579880635543)
            ·
              refine ⟨1795796577611369820953315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197197718407579880635543 1795796577611369820953315)
              ·
                refine ⟨2693694866417054731429973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795796577611369820953315 2693694866417054731429973)
                ·
                  refine ⟨31566736715824860133945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2693694866417054731429973 31566736715824860133945)
                  ·
                    rfl

theorem cell22_276642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_276642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276642 prefixEnd_276642 := by exact prefixLift 276642
  have htrace : WordTrace (prefixWord ++ tailWord_276642) baseStart_276642 baseEnd_276642 := by
    simpa [prefixWord, tailWord_276642, baseEnd_276642] using wordTrace_append hprefix tailTrace_276642
  have hstable : (prefixWord ++ tailWord_276642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276642).length < 2 ^ (prefixWord ++ tailWord_276642).sum := by decide
  have hdescent : baseEnd_276642 < baseStart_276642 := by decide
  rcases family_descends (prefixWord ++ tailWord_276642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276661 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 1, 4]
def baseStart_276661 : Nat := 118140960795 + 276661 * 2 ^ 59
def prefixEnd_276661 : Nat := 4983230072969 + 3 ^ 40 * 276661 * 2
def baseEnd_276661 : Nat := 94706714235764864176777

theorem tailTrace_276661 : CollatzResearch.WordTrace tailWord_276661 prefixEnd_276661 94706714235764864176777 := by
  unfold tailWord_276661
  simp only [CollatzResearch.WordTrace]
  refine ⟨10090655650711921782149837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6727103767141281188099891 10090655650711921782149837)
  ·
    refine ⟨3783995869016970668306189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10090655650711921782149837 3783995869016970668306189)
    ·
      refine ⟨1418998450881364000614821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3783995869016970668306189 1418998450881364000614821)
      ·
        refine ⟨266062209540255750115279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1418998450881364000614821 266062209540255750115279)
        ·
          refine ⟨399093314310383625172919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266062209540255750115279 399093314310383625172919)
          ·
            refine ⟨598639971465575437759379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399093314310383625172919 598639971465575437759379)
            ·
              refine ⟨897959957198363156639069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598639971465575437759379 897959957198363156639069)
              ·
                refine ⟨336734983949386183739651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897959957198363156639069 336734983949386183739651)
                ·
                  refine ⟨505102475924079275609477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336734983949386183739651 505102475924079275609477)
                  ·
                    refine ⟨94706714235764864176777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 505102475924079275609477 94706714235764864176777)
                    ·
                      rfl

theorem cell22_276661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_276661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276661 prefixEnd_276661 := by exact prefixLift 276661
  have htrace : WordTrace (prefixWord ++ tailWord_276661) baseStart_276661 baseEnd_276661 := by
    simpa [prefixWord, tailWord_276661, baseEnd_276661] using wordTrace_append hprefix tailTrace_276661
  have hstable : (prefixWord ++ tailWord_276661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276661).length < 2 ^ (prefixWord ++ tailWord_276661).sum := by decide
  have hdescent : baseEnd_276661 < baseStart_276661 := by decide
  rcases family_descends (prefixWord ++ tailWord_276661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276715 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 9]
def baseStart_276715 : Nat := 118140960795 + 276715 * 2 ^ 59
def prefixEnd_276715 : Nat := 4983230072969 + 3 ^ 40 * 276715 * 2
def baseEnd_276715 : Nat := 31575066513108907775537

theorem tailTrace_276715 : CollatzResearch.WordTrace tailWord_276715 prefixEnd_276715 31575066513108907775537 := by
  unfold tailWord_276715
  simp only [CollatzResearch.WordTrace]
  refine ⟨10092625192516289004615599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6728416795010859336410399 10092625192516289004615599)
  ·
    refine ⟨15138937788774433506923399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10092625192516289004615599 15138937788774433506923399)
    ·
      refine ⟨22708406683161650260385099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15138937788774433506923399 22708406683161650260385099)
      ·
        refine ⟨34062610024742475390577649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22708406683161650260385099 34062610024742475390577649)
        ·
          refine ⟨25546957518556856542933237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34062610024742475390577649 25546957518556856542933237)
          ·
            refine ⟨2395027267364705300899991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25546957518556856542933237 2395027267364705300899991)
            ·
              refine ⟨3592540901047057951349987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2395027267364705300899991 3592540901047057951349987)
              ·
                refine ⟨5388811351570586927024981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592540901047057951349987 5388811351570586927024981)
                ·
                  refine ⟨31575066513108907775537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5388811351570586927024981 31575066513108907775537)
                  ·
                    rfl

theorem cell22_276715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 9].length) (baseStart_276715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276715 prefixEnd_276715 := by exact prefixLift 276715
  have htrace : WordTrace (prefixWord ++ tailWord_276715) baseStart_276715 baseEnd_276715 := by
    simpa [prefixWord, tailWord_276715, baseEnd_276715] using wordTrace_append hprefix tailTrace_276715
  have hstable : (prefixWord ++ tailWord_276715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276715).length < 2 ^ (prefixWord ++ tailWord_276715).sum := by decide
  have hdescent : baseEnd_276715 < baseStart_276715 := by decide
  rcases family_descends (prefixWord ++ tailWord_276715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276732 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 7]
def baseStart_276732 : Nat := 118140960795 + 276732 * 2 ^ 59
def prefixEnd_276732 : Nat := 4983230072969 + 3 ^ 40 * 276732 * 2
def baseEnd_276732 : Nat := 31577006328914781883853

theorem tailTrace_276732 : CollatzResearch.WordTrace tailWord_276732 prefixEnd_276732 31577006328914781883853 := by
  unfold tailWord_276732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5046622616727350453992225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6728830155636467271989633 5046622616727350453992225)
  ·
    refine ⟨3784966962545512840494169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5046622616727350453992225 3784966962545512840494169)
    ·
      refine ⟨2838725221909134630370627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3784966962545512840494169 2838725221909134630370627)
      ·
        refine ⟨4258087832863701945555941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2838725221909134630370627 4258087832863701945555941)
        ·
          refine ⟨798391468661944114791739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4258087832863701945555941 798391468661944114791739)
          ·
            refine ⟨1197587202992916172187609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798391468661944114791739 1197587202992916172187609)
            ·
              refine ⟨898190402244687129140707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1197587202992916172187609 898190402244687129140707)
              ·
                refine ⟨1347285603367030693711061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898190402244687129140707 1347285603367030693711061)
                ·
                  refine ⟨31577006328914781883853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1347285603367030693711061 31577006328914781883853)
                  ·
                    rfl

theorem cell22_276732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_276732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276732 prefixEnd_276732 := by exact prefixLift 276732
  have htrace : WordTrace (prefixWord ++ tailWord_276732) baseStart_276732 baseEnd_276732 := by
    simpa [prefixWord, tailWord_276732, baseEnd_276732] using wordTrace_append hprefix tailTrace_276732
  have hstable : (prefixWord ++ tailWord_276732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276732).length < 2 ^ (prefixWord ++ tailWord_276732).sum := by decide
  have hdescent : baseEnd_276732 < baseStart_276732 := by decide
  rcases family_descends (prefixWord ++ tailWord_276732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276807 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 1, 6]
def baseStart_276807 : Nat := 118140960795 + 276807 * 2 ^ 59
def prefixEnd_276807 : Nat := 4983230072969 + 3 ^ 40 * 276807 * 2
def baseEnd_276807 : Nat := 94756693019469150026329

theorem tailTrace_276807 : CollatzResearch.WordTrace tailWord_276807 prefixEnd_276807 94756693019469150026329 := by
  unfold tailWord_276807
  simp only [CollatzResearch.WordTrace]
  refine ⟨10095980708182988716964675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6730653805455325811309783 10095980708182988716964675)
  ·
    refine ⟨15143971062274483075447013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10095980708182988716964675 15143971062274483075447013)
    ·
      refine ⟨2839494574176465576646315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15143971062274483075447013 2839494574176465576646315)
      ·
        refine ⟨4259241861264698364969473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2839494574176465576646315 4259241861264698364969473)
        ·
          refine ⟨3194431395948523773727105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4259241861264698364969473 3194431395948523773727105)
          ·
            refine ⟨2395823546961392830295329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3194431395948523773727105 2395823546961392830295329)
            ·
              refine ⟨1796867660221044622721497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2395823546961392830295329 1796867660221044622721497)
              ·
                refine ⟨1347650745165783467041123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1796867660221044622721497 1347650745165783467041123)
                ·
                  refine ⟨2021476117748675200561685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347650745165783467041123 2021476117748675200561685)
                  ·
                    refine ⟨94756693019469150026329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2021476117748675200561685 94756693019469150026329)
                    ·
                      rfl

theorem cell22_276807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_276807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276807 prefixEnd_276807 := by exact prefixLift 276807
  have htrace : WordTrace (prefixWord ++ tailWord_276807) baseStart_276807 baseEnd_276807 := by
    simpa [prefixWord, tailWord_276807, baseEnd_276807] using wordTrace_append hprefix tailTrace_276807
  have hstable : (prefixWord ++ tailWord_276807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276807).length < 2 ^ (prefixWord ++ tailWord_276807).sum := by decide
  have hdescent : baseEnd_276807 < baseStart_276807 := by decide
  rcases family_descends (prefixWord ++ tailWord_276807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276914 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_276914 : Nat := 118140960795 + 276914 * 2 ^ 59
def prefixEnd_276914 : Nat := 4983230072969 + 3 ^ 40 * 276914 * 2
def baseEnd_276914 : Nat := 94793321306156537601001

theorem tailTrace_276914 : CollatzResearch.WordTrace tailWord_276914 prefixEnd_276914 94793321306156537601001 := by
  unfold tailWord_276914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2524970829698836497777449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6733255545863563994073197 2524970829698836497777449)
  ·
    refine ⟨1893728122274127373333087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2524970829698836497777449 1893728122274127373333087)
    ·
      refine ⟨2840592183411191059999631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1893728122274127373333087 2840592183411191059999631)
      ·
        refine ⟨4260888275116786589999447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2840592183411191059999631 4260888275116786589999447)
        ·
          refine ⟨6391332412675179884999171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4260888275116786589999447 6391332412675179884999171)
          ·
            refine ⟨9586998619012769827498757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6391332412675179884999171 9586998619012769827498757)
            ·
              refine ⟨1797562241064894342656017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9586998619012769827498757 1797562241064894342656017)
              ·
                refine ⟨1348171680798670756992013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1797562241064894342656017 1348171680798670756992013)
                ·
                  refine ⟨505564380299501533872005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1348171680798670756992013 505564380299501533872005)
                  ·
                    refine ⟨94793321306156537601001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 505564380299501533872005 94793321306156537601001)
                    ·
                      rfl

theorem cell22_276914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_276914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276914 prefixEnd_276914 := by exact prefixLift 276914
  have htrace : WordTrace (prefixWord ++ tailWord_276914) baseStart_276914 baseEnd_276914 := by
    simpa [prefixWord, tailWord_276914, baseEnd_276914] using wordTrace_append hprefix tailTrace_276914
  have hstable : (prefixWord ++ tailWord_276914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276914).length < 2 ^ (prefixWord ++ tailWord_276914).sum := by decide
  have hdescent : baseEnd_276914 < baseStart_276914 := by decide
  rcases family_descends (prefixWord ++ tailWord_276914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276963 : List Nat := [1, 1, 1, 6, 3, 1, 1, 4, 4]
def baseStart_276963 : Nat := 118140960795 + 276963 * 2 ^ 59
def prefixEnd_276963 : Nat := 4983230072969 + 3 ^ 40 * 276963 * 2
def baseEnd_276963 : Nat := 31603365002512247708617

theorem tailTrace_276963 : CollatzResearch.WordTrace tailWord_276963 prefixEnd_276963 31603365002512247708617 := by
  unfold tailWord_276963
  simp only [CollatzResearch.WordTrace]
  refine ⟨10101670495617827359643543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6734446997078551573095695 10101670495617827359643543)
  ·
    refine ⟨15152505743426741039465315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10101670495617827359643543 15152505743426741039465315)
    ·
      refine ⟨22728758615140111559197973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15152505743426741039465315 22728758615140111559197973)
      ·
        refine ⟨1065410560084692729337405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22728758615140111559197973 1065410560084692729337405)
        ·
          refine ⟨399528960031759773501527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1065410560084692729337405 399528960031759773501527)
          ·
            refine ⟨599293440047639660252291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399528960031759773501527 599293440047639660252291)
            ·
              refine ⟨898940160071459490378437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599293440047639660252291 898940160071459490378437)
              ·
                refine ⟨168551280013398654445957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 898940160071459490378437 168551280013398654445957)
                ·
                  refine ⟨31603365002512247708617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168551280013398654445957 31603365002512247708617)
                  ·
                    rfl

theorem cell22_276963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 4].length) (baseStart_276963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276963 prefixEnd_276963 := by exact prefixLift 276963
  have htrace : WordTrace (prefixWord ++ tailWord_276963) baseStart_276963 baseEnd_276963 := by
    simpa [prefixWord, tailWord_276963, baseEnd_276963] using wordTrace_append hprefix tailTrace_276963
  have hstable : (prefixWord ++ tailWord_276963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276963).length < 2 ^ (prefixWord ++ tailWord_276963).sum := by decide
  have hdescent : baseEnd_276963 < baseStart_276963 := by decide
  rcases family_descends (prefixWord ++ tailWord_276963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276978 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_276978 : Nat := 118140960795 + 276978 * 2 ^ 59
def prefixEnd_276978 : Nat := 4983230072969 + 3 ^ 40 * 276978 * 2
def baseEnd_276978 : Nat := 94815229814081704000805

theorem tailTrace_276978 : CollatzResearch.WordTrace tailWord_276978 prefixEnd_276978 94815229814081704000805 := by
  unfold tailWord_276978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2525554397640871230359897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6734811727042323280959725 2525554397640871230359897)
  ·
    refine ⟨1894165798230653422769923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2525554397640871230359897 1894165798230653422769923)
    ·
      refine ⟨2841248697345980134154885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1894165798230653422769923 2841248697345980134154885)
      ·
        refine ⟨532734130752371275154041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2841248697345980134154885 532734130752371275154041)
        ·
          refine ⟨399550598064278456365531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 532734130752371275154041 399550598064278456365531)
          ·
            refine ⟨599325897096417684548297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399550598064278456365531 599325897096417684548297)
            ·
              refine ⟨449494422822313263411223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 599325897096417684548297 449494422822313263411223)
              ·
                refine ⟨674241634233469895116835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449494422822313263411223 674241634233469895116835)
                ·
                  refine ⟨1011362451350204842675253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674241634233469895116835 1011362451350204842675253)
                  ·
                    refine ⟨94815229814081704000805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1011362451350204842675253 94815229814081704000805)
                    ·
                      rfl

theorem cell22_276978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_276978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276978 prefixEnd_276978 := by exact prefixLift 276978
  have htrace : WordTrace (prefixWord ++ tailWord_276978) baseStart_276978 baseEnd_276978 := by
    simpa [prefixWord, tailWord_276978, baseEnd_276978] using wordTrace_append hprefix tailTrace_276978
  have hstable : (prefixWord ++ tailWord_276978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276978).length < 2 ^ (prefixWord ++ tailWord_276978).sum := by decide
  have hdescent : baseEnd_276978 < baseStart_276978 := by decide
  rcases family_descends (prefixWord ++ tailWord_276978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276993 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 2, 4]
def baseStart_276993 : Nat := 118140960795 + 276993 * 2 ^ 59
def prefixEnd_276993 : Nat := 4983230072969 + 3 ^ 40 * 276993 * 2
def baseEnd_276993 : Nat := 94820364620626664875759

theorem tailTrace_276993 : CollatzResearch.WordTrace tailWord_276993 prefixEnd_276993 94820364620626664875759 := by
  unfold tailWord_276993
  simp only [CollatzResearch.WordTrace]
  refine ⟨10102764685509142483235633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6735176457006094988823755 10102764685509142483235633)
  ·
    refine ⟨7577073514131856862426725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10102764685509142483235633 7577073514131856862426725)
    ·
      refine ⟨1420701283899723161705011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7577073514131856862426725 1420701283899723161705011)
      ·
        refine ⟨2131051925849584742557517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420701283899723161705011 2131051925849584742557517)
        ·
          refine ⟨799144472193594278459069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2131051925849584742557517 799144472193594278459069)
          ·
            refine ⟨299679177072597854422151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 799144472193594278459069 299679177072597854422151)
            ·
              refine ⟨449518765608896781633227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299679177072597854422151 449518765608896781633227)
              ·
                refine ⟨674278148413345172449841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449518765608896781633227 674278148413345172449841)
                ·
                  refine ⟨505708611310008879337381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 674278148413345172449841 505708611310008879337381)
                  ·
                    refine ⟨94820364620626664875759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 505708611310008879337381 94820364620626664875759)
                    ·
                      rfl

theorem cell22_276993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_276993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_276993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_276993 prefixEnd_276993 := by exact prefixLift 276993
  have htrace : WordTrace (prefixWord ++ tailWord_276993) baseStart_276993 baseEnd_276993 := by
    simpa [prefixWord, tailWord_276993, baseEnd_276993] using wordTrace_append hprefix tailTrace_276993
  have hstable : (prefixWord ++ tailWord_276993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276993).length < 2 ^ (prefixWord ++ tailWord_276993).sum := by decide
  have hdescent : baseEnd_276993 < baseStart_276993 := by decide
  rcases family_descends (prefixWord ++ tailWord_276993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277012 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_277012 : Nat := 118140960795 + 277012 * 2 ^ 59
def prefixEnd_277012 : Nat := 4983230072969 + 3 ^ 40 * 277012 * 2
def baseEnd_277012 : Nat := 94826868708916948650701

theorem tailTrace_277012 : CollatzResearch.WordTrace tailWord_277012 prefixEnd_277012 94826868708916948650701 := by
  unfold tailWord_277012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051728836220154364088645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6735638448293539152118193 5051728836220154364088645)
  ·
    refine ⟨947199156791278943266621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5051728836220154364088645 947199156791278943266621)
    ·
      refine ⟨355199683796729603724983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 947199156791278943266621 355199683796729603724983)
      ·
        refine ⟨532799525695094405587475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355199683796729603724983 532799525695094405587475)
        ·
          refine ⟨799199288542641608381213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532799525695094405587475 799199288542641608381213)
          ·
            refine ⟨299699733203490603142955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 799199288542641608381213 299699733203490603142955)
            ·
              refine ⟨449549599805235904714433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299699733203490603142955 449549599805235904714433)
              ·
                refine ⟨337162199853926928535825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449549599805235904714433 337162199853926928535825)
                ·
                  refine ⟨252871649890445196401869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337162199853926928535825 252871649890445196401869)
                  ·
                    refine ⟨94826868708916948650701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252871649890445196401869 94826868708916948650701)
                    ·
                      rfl

theorem cell22_277012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_277012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277012 prefixEnd_277012 := by exact prefixLift 277012
  have htrace : WordTrace (prefixWord ++ tailWord_277012) baseStart_277012 baseEnd_277012 := by
    simpa [prefixWord, tailWord_277012, baseEnd_277012] using wordTrace_append hprefix tailTrace_277012
  have hstable : (prefixWord ++ tailWord_277012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277012).length < 2 ^ (prefixWord ++ tailWord_277012).sum := by decide
  have hdescent : baseEnd_277012 < baseStart_277012 := by decide
  rcases family_descends (prefixWord ++ tailWord_277012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277057 : List Nat := [1, 2, 5, 1, 1, 4, 1, 3, 1, 3]
def baseStart_277057 : Nat := 118140960795 + 277057 * 2 ^ 59
def prefixEnd_277057 : Nat := 4983230072969 + 3 ^ 40 * 277057 * 2
def baseEnd_277057 : Nat := 94842273128551831275563

theorem tailTrace_277057 : CollatzResearch.WordTrace tailWord_277057 prefixEnd_277057 94842273128551831275563 := by
  unfold tailWord_277057
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105098957277281413565425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6736732638184854275710283 10105098957277281413565425)
  ·
    refine ⟨7578824217957961060174069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10105098957277281413565425 7578824217957961060174069)
    ·
      refine ⟨710514770433558849391319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7578824217957961060174069 710514770433558849391319)
      ·
        refine ⟨1065772155650338274086979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710514770433558849391319 1065772155650338274086979)
        ·
          refine ⟨1598658233475507411130469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065772155650338274086979 1598658233475507411130469)
          ·
            refine ⟨299748418776657639586963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1598658233475507411130469 299748418776657639586963)
            ·
              refine ⟨449622628164986459380445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299748418776657639586963 449622628164986459380445)
              ·
                refine ⟨168608485561869922267667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 449622628164986459380445 168608485561869922267667)
                ·
                  refine ⟨252912728342804883401501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168608485561869922267667 252912728342804883401501)
                  ·
                    refine ⟨94842273128551831275563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 252912728342804883401501 94842273128551831275563)
                    ·
                      rfl

theorem cell22_277057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_277057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277057 prefixEnd_277057 := by exact prefixLift 277057
  have htrace : WordTrace (prefixWord ++ tailWord_277057) baseStart_277057 baseEnd_277057 := by
    simpa [prefixWord, tailWord_277057, baseEnd_277057] using wordTrace_append hprefix tailTrace_277057
  have hstable : (prefixWord ++ tailWord_277057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277057).length < 2 ^ (prefixWord ++ tailWord_277057).sum := by decide
  have hdescent : baseEnd_277057 < baseStart_277057 := by decide
  rcases family_descends (prefixWord ++ tailWord_277057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277064 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 8]
def baseStart_277064 : Nat := 118140960795 + 277064 * 2 ^ 59
def prefixEnd_277064 : Nat := 4983230072969 + 3 ^ 40 * 277064 * 2
def baseEnd_277064 : Nat := 31614889790535382116847

theorem tailTrace_277064 : CollatzResearch.WordTrace tailWord_277064 prefixEnd_277064 31614889790535382116847 := by
  unfold tailWord_277064
  simp only [CollatzResearch.WordTrace]
  refine ⟨5052677134125960804535123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6736902845501281072713497 5052677134125960804535123)
  ·
    refine ⟨7579015701188941206802685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5052677134125960804535123 7579015701188941206802685)
    ·
      refine ⟨2842130887945852952551007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7579015701188941206802685 2842130887945852952551007)
      ·
        refine ⟨4263196331918779428826511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842130887945852952551007 4263196331918779428826511)
        ·
          refine ⟨6394794497878169143239767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4263196331918779428826511 6394794497878169143239767)
          ·
            refine ⟨9592191746817253714859651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6394794497878169143239767 9592191746817253714859651)
            ·
              refine ⟨14388287620225880572289477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9592191746817253714859651 14388287620225880572289477)
              ·
                refine ⟨2697803928792352607304277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14388287620225880572289477 2697803928792352607304277)
                ·
                  refine ⟨31614889790535382116847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2697803928792352607304277 31614889790535382116847)
                  ·
                    rfl

theorem cell22_277064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_277064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277064 prefixEnd_277064 := by exact prefixLift 277064
  have htrace : WordTrace (prefixWord ++ tailWord_277064) baseStart_277064 baseEnd_277064 := by
    simpa [prefixWord, tailWord_277064, baseEnd_277064] using wordTrace_append hprefix tailTrace_277064
  have hstable : (prefixWord ++ tailWord_277064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277064).length < 2 ^ (prefixWord ++ tailWord_277064).sum := by decide
  have hdescent : baseEnd_277064 < baseStart_277064 := by decide
  rcases family_descends (prefixWord ++ tailWord_277064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277111 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 2, 4]
def baseStart_277111 : Nat := 118140960795 + 277111 * 2 ^ 59
def prefixEnd_277111 : Nat := 4983230072969 + 3 ^ 40 * 277111 * 2
def baseEnd_277111 : Nat := 94860758432113690425397

theorem tailTrace_277111 : CollatzResearch.WordTrace tailWord_277111 prefixEnd_277111 94860758432113690425397 := by
  unfold tailWord_277111
  simp only [CollatzResearch.WordTrace]
  refine ⟨10107068499081648636031187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6738045666054432424020791 10107068499081648636031187)
  ·
    refine ⟨15160602748622472954046781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10107068499081648636031187 15160602748622472954046781)
    ·
      refine ⟨5685226030733427357767543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15160602748622472954046781 5685226030733427357767543)
      ·
        refine ⟨8527839046100141036651315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5685226030733427357767543 8527839046100141036651315)
        ·
          refine ⟨12791758569150211554976973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8527839046100141036651315 12791758569150211554976973)
          ·
            refine ⟨4796909463431329333116365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12791758569150211554976973 4796909463431329333116365)
            ·
              refine ⟨1798841048786748499918637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4796909463431329333116365 1798841048786748499918637)
              ·
                refine ⟨674565393295030687469489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1798841048786748499918637 674565393295030687469489)
                ·
                  refine ⟨505924044971273015602117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 674565393295030687469489 505924044971273015602117)
                  ·
                    refine ⟨94860758432113690425397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 505924044971273015602117 94860758432113690425397)
                    ·
                      rfl

theorem cell22_277111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_277111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277111 prefixEnd_277111 := by exact prefixLift 277111
  have htrace : WordTrace (prefixWord ++ tailWord_277111) baseStart_277111 baseEnd_277111 := by
    simpa [prefixWord, tailWord_277111, baseEnd_277111] using wordTrace_append hprefix tailTrace_277111
  have hstable : (prefixWord ++ tailWord_277111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277111).length < 2 ^ (prefixWord ++ tailWord_277111).sum := by decide
  have hdescent : baseEnd_277111 < baseStart_277111 := by decide
  rcases family_descends (prefixWord ++ tailWord_277111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277156 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_277156 : Nat := 118140960795 + 277156 * 2 ^ 59
def prefixEnd_277156 : Nat := 4983230072969 + 3 ^ 40 * 277156 * 2
def baseEnd_277156 : Nat := 94876162851748573050259

theorem tailTrace_277156 : CollatzResearch.WordTrace tailWord_277156 prefixEnd_277156 94876162851748573050259 := by
  unfold tailWord_277156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054354891959310660709661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6739139855945747547612881 5054354891959310660709661)
  ·
    refine ⟨1895383084484741497766123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5054354891959310660709661 1895383084484741497766123)
    ·
      refine ⟨2843074626727112246649185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895383084484741497766123 2843074626727112246649185)
      ·
        refine ⟨2132305970045334184986889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2843074626727112246649185 2132305970045334184986889)
        ·
          refine ⟨1599229477534000638740167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2132305970045334184986889 1599229477534000638740167)
          ·
            refine ⟨2398844216301000958110251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599229477534000638740167 2398844216301000958110251)
            ·
              refine ⟨3598266324451501437165377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398844216301000958110251 3598266324451501437165377)
              ·
                refine ⟨2698699743338626077874033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3598266324451501437165377 2698699743338626077874033)
                ·
                  refine ⟨2024024807503969558405525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2698699743338626077874033 2024024807503969558405525)
                  ·
                    refine ⟨94876162851748573050259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2024024807503969558405525 94876162851748573050259)
                    ·
                      rfl

theorem cell22_277156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_277156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277156 prefixEnd_277156 := by exact prefixLift 277156
  have htrace : WordTrace (prefixWord ++ tailWord_277156) baseStart_277156 baseEnd_277156 := by
    simpa [prefixWord, tailWord_277156, baseEnd_277156] using wordTrace_append hprefix tailTrace_277156
  have hstable : (prefixWord ++ tailWord_277156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277156).length < 2 ^ (prefixWord ++ tailWord_277156).sum := by decide
  have hdescent : baseEnd_277156 < baseStart_277156 := by decide
  rcases family_descends (prefixWord ++ tailWord_277156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277188 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 7]
def baseStart_277188 : Nat := 118140960795 + 277188 * 2 ^ 59
def prefixEnd_277188 : Nat := 4983230072969 + 3 ^ 40 * 277188 * 2
def baseEnd_277188 : Nat := 31629039035237052083387

theorem tailTrace_277188 : CollatzResearch.WordTrace tailWord_277188 prefixEnd_277188 31629039035237052083387 := by
  unfold tailWord_277188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054938459901345393292109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6739917946535127191056145 5054938459901345393292109)
  ·
    refine ⟨1895601922463004522484541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5054938459901345393292109 1895601922463004522484541)
    ·
      refine ⟨710850720923626695931703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1895601922463004522484541 710850720923626695931703)
      ·
        refine ⟨1066276081385440043897555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710850720923626695931703 1066276081385440043897555)
        ·
          refine ⟨1599414122078160065846333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066276081385440043897555 1599414122078160065846333)
          ·
            refine ⟨599780295779310024692375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1599414122078160065846333 599780295779310024692375)
            ·
              refine ⟨899670443668965037038563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599780295779310024692375 899670443668965037038563)
              ·
                refine ⟨1349505665503447555557845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899670443668965037038563 1349505665503447555557845)
                ·
                  refine ⟨31629039035237052083387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1349505665503447555557845 31629039035237052083387)
                  ·
                    rfl

theorem cell22_277188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_277188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277188 prefixEnd_277188 := by exact prefixLift 277188
  have htrace : WordTrace (prefixWord ++ tailWord_277188) baseStart_277188 baseEnd_277188 := by
    simpa [prefixWord, tailWord_277188, baseEnd_277188] using wordTrace_append hprefix tailTrace_277188
  have hstable : (prefixWord ++ tailWord_277188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277188).length < 2 ^ (prefixWord ++ tailWord_277188).sum := by decide
  have hdescent : baseEnd_277188 < baseStart_277188 := by decide
  rcases family_descends (prefixWord ++ tailWord_277188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277250 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_277250 : Nat := 118140960795 + 277250 * 2 ^ 59
def prefixEnd_277250 : Nat := 4983230072969 + 3 ^ 40 * 277250 * 2
def baseEnd_277250 : Nat := 31636113657587887066657

theorem tailTrace_277250 : CollatzResearch.WordTrace tailWord_277250 prefixEnd_277250 31636113657587887066657 := by
  unfold tailWord_277250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2528034561394518843835301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6741425497052050250227469 2528034561394518843835301)
  ·
    refine ⟨474006480261472283219119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2528034561394518843835301 474006480261472283219119)
    ·
      refine ⟨711009720392208424828679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474006480261472283219119 711009720392208424828679)
      ·
        refine ⟨1066514580588312637243019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711009720392208424828679 1066514580588312637243019)
        ·
          refine ⟨1599771870882468955864529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066514580588312637243019 1599771870882468955864529)
          ·
            refine ⟨1199828903161851716898397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1599771870882468955864529 1199828903161851716898397)
            ·
              refine ⟨449935838685694393836899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1199828903161851716898397 449935838685694393836899)
              ·
                refine ⟨674903758028541590755349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449935838685694393836899 674903758028541590755349)
                ·
                  refine ⟨31636113657587887066657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 674903758028541590755349 31636113657587887066657)
                  ·
                    rfl

theorem cell22_277250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_277250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277250 prefixEnd_277250 := by exact prefixLift 277250
  have htrace : WordTrace (prefixWord ++ tailWord_277250) baseStart_277250 baseEnd_277250 := by
    simpa [prefixWord, tailWord_277250, baseEnd_277250] using wordTrace_append hprefix tailTrace_277250
  have hstable : (prefixWord ++ tailWord_277250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277250).length < 2 ^ (prefixWord ++ tailWord_277250).sum := by decide
  have hdescent : baseEnd_277250 < baseStart_277250 := by decide
  rcases family_descends (prefixWord ++ tailWord_277250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277280 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 2, 4]
def baseStart_277280 : Nat := 118140960795 + 277280 * 2 ^ 59
def prefixEnd_277280 : Nat := 4983230072969 + 3 ^ 40 * 277280 * 2
def baseEnd_277280 : Nat := 94918610585853582949879

theorem tailTrace_277280 : CollatzResearch.WordTrace tailWord_277280 prefixEnd_277280 94918610585853582949879 := by
  unfold tailWord_277280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5056616217734695249466647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6742154956979593665955529 5056616217734695249466647)
  ·
    refine ⟨7584924326602042874199971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5056616217734695249466647 7584924326602042874199971)
    ·
      refine ⟨11377386489903064311299957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7584924326602042874199971 11377386489903064311299957)
      ·
        refine ⟨1066629983428412279184371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11377386489903064311299957 1066629983428412279184371)
        ·
          refine ⟨1599944975142618418776557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066629983428412279184371 1599944975142618418776557)
          ·
            refine ⟨599979365678481907041209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1599944975142618418776557 599979365678481907041209)
            ·
              refine ⟨449984524258861430280907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 599979365678481907041209 449984524258861430280907)
              ·
                refine ⟨674976786388292145421361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449984524258861430280907 674976786388292145421361)
                ·
                  refine ⟨506232589791219109066021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 674976786388292145421361 506232589791219109066021)
                  ·
                    refine ⟨94918610585853582949879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 506232589791219109066021 94918610585853582949879)
                    ·
                      rfl

theorem cell22_277280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_277280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277280 prefixEnd_277280 := by exact prefixLift 277280
  have htrace : WordTrace (prefixWord ++ tailWord_277280) baseStart_277280 baseEnd_277280 := by
    simpa [prefixWord, tailWord_277280, baseEnd_277280] using wordTrace_append hprefix tailTrace_277280
  have hstable : (prefixWord ++ tailWord_277280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277280).length < 2 ^ (prefixWord ++ tailWord_277280).sum := by decide
  have hdescent : baseEnd_277280 < baseStart_277280 := by decide
  rcases family_descends (prefixWord ++ tailWord_277280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277291 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 1, 8]
def baseStart_277291 : Nat := 118140960795 + 277291 * 2 ^ 59
def prefixEnd_277291 : Nat := 4983230072969 + 3 ^ 40 * 277291 * 2
def baseEnd_277291 : Nat := 94922376110653220924845

theorem tailTrace_277291 : CollatzResearch.WordTrace tailWord_277291 prefixEnd_277291 94922376110653220924845 := by
  unfold tailWord_277291
  simp only [CollatzResearch.WordTrace]
  refine ⟨10113633638429539377583727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6742422425619692918389151 10113633638429539377583727)
  ·
    refine ⟨15170450457644309066375591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10113633638429539377583727 15170450457644309066375591)
    ·
      refine ⟨22755675686466463599563387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15170450457644309066375591 22755675686466463599563387)
      ·
        refine ⟨34133513529699695399345081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22755675686466463599563387 34133513529699695399345081)
        ·
          refine ⟨25600135147274771549508811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34133513529699695399345081 25600135147274771549508811)
          ·
            refine ⟨38400202720912157324263217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25600135147274771549508811 38400202720912157324263217)
            ·
              refine ⟨28800152040684117993197413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38400202720912157324263217 28800152040684117993197413)
              ·
                refine ⟨5400028507628272123724515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28800152040684117993197413 5400028507628272123724515)
                ·
                  refine ⟨8100042761442408185586773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5400028507628272123724515 8100042761442408185586773)
                  ·
                    refine ⟨94922376110653220924845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8100042761442408185586773 94922376110653220924845)
                    ·
                      rfl

theorem cell22_277291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_277291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277291 prefixEnd_277291 := by exact prefixLift 277291
  have htrace : WordTrace (prefixWord ++ tailWord_277291) baseStart_277291 baseEnd_277291 := by
    simpa [prefixWord, tailWord_277291, baseEnd_277291] using wordTrace_append hprefix tailTrace_277291
  have hstable : (prefixWord ++ tailWord_277291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277291).length < 2 ^ (prefixWord ++ tailWord_277291).sum := by decide
  have hdescent : baseEnd_277291 < baseStart_277291 := by decide
  rcases family_descends (prefixWord ++ tailWord_277291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277443 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 2, 6]
def baseStart_277443 : Nat := 118140960795 + 277443 * 2 ^ 59
def prefixEnd_277443 : Nat := 4983230072969 + 3 ^ 40 * 277443 * 2
def baseEnd_277443 : Nat := 94974408816975491124379

theorem tailTrace_277443 : CollatzResearch.WordTrace tailWord_277443 prefixEnd_277443 94974408816975491124379 := by
  unfold tailWord_277443
  simp only [CollatzResearch.WordTrace]
  refine ⟨10119177533878869337116983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6746118355919246224744655 10119177533878869337116983)
  ·
    refine ⟨15178766300818304005675475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10119177533878869337116983 15178766300818304005675475)
    ·
      refine ⟨22768149451227456008513213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15178766300818304005675475 22768149451227456008513213)
      ·
        refine ⟨8538056044210296003192455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22768149451227456008513213 8538056044210296003192455)
        ·
          refine ⟨12807084066315444004788683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8538056044210296003192455 12807084066315444004788683)
          ·
            refine ⟨19210626099473166007183025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12807084066315444004788683 19210626099473166007183025)
            ·
              refine ⟨14407969574604874505387269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19210626099473166007183025 14407969574604874505387269)
              ·
                refine ⟨2701494295238413969760113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14407969574604874505387269 2701494295238413969760113)
                ·
                  refine ⟨2026120721428810477320085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2701494295238413969760113 2026120721428810477320085)
                  ·
                    refine ⟨94974408816975491124379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2026120721428810477320085 94974408816975491124379)
                    ·
                      rfl

theorem cell22_277443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_277443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277443 prefixEnd_277443 := by exact prefixLift 277443
  have htrace : WordTrace (prefixWord ++ tailWord_277443) baseStart_277443 baseEnd_277443 := by
    simpa [prefixWord, tailWord_277443, baseEnd_277443] using wordTrace_append hprefix tailTrace_277443
  have hstable : (prefixWord ++ tailWord_277443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277443).length < 2 ^ (prefixWord ++ tailWord_277443).sum := by decide
  have hdescent : baseEnd_277443 < baseStart_277443 := by decide
  rcases family_descends (prefixWord ++ tailWord_277443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277537 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 6]
def baseStart_277537 : Nat := 118140960795 + 277537 * 2 ^ 59
def prefixEnd_277537 : Nat := 4983230072969 + 3 ^ 40 * 277537 * 2
def baseEnd_277537 : Nat := 31668862312663526424697

theorem tailTrace_277537 : CollatzResearch.WordTrace tailWord_277537 prefixEnd_277537 31668862312663526424697 := by
  unfold tailWord_277537
  simp only [CollatzResearch.WordTrace]
  refine ⟨10122605995538323391038865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6748403997025548927359243 10122605995538323391038865)
  ·
    refine ⟨7591954496653742543279149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10122605995538323391038865 7591954496653742543279149)
    ·
      refine ⟨2846982936245153453729681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7591954496653742543279149 2846982936245153453729681)
      ·
        refine ⟨2135237202183865090297261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2846982936245153453729681 2135237202183865090297261)
        ·
          refine ⟨800713950818949408861473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2135237202183865090297261 800713950818949408861473)
          ·
            refine ⟨600535463114212056646105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 800713950818949408861473 600535463114212056646105)
            ·
              refine ⟨450401597335659042484579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600535463114212056646105 450401597335659042484579)
              ·
                refine ⟨675602396003488563726869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450401597335659042484579 675602396003488563726869)
                ·
                  refine ⟨31668862312663526424697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 675602396003488563726869 31668862312663526424697)
                  ·
                    rfl

theorem cell22_277537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_277537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277537 prefixEnd_277537 := by exact prefixLift 277537
  have htrace : WordTrace (prefixWord ++ tailWord_277537) baseStart_277537 baseEnd_277537 := by
    simpa [prefixWord, tailWord_277537, baseEnd_277537] using wordTrace_append hprefix tailTrace_277537
  have hstable : (prefixWord ++ tailWord_277537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277537).length < 2 ^ (prefixWord ++ tailWord_277537).sum := by decide
  have hdescent : baseEnd_277537 < baseStart_277537 := by decide
  rcases family_descends (prefixWord ++ tailWord_277537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277556 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_277556 : Nat := 118140960795 + 277556 * 2 ^ 59
def prefixEnd_277556 : Nat := 4983230072969 + 3 ^ 40 * 277556 * 2
def baseEnd_277556 : Nat := 95013091026280863049033

theorem tailTrace_277556 : CollatzResearch.WordTrace tailWord_277556 prefixEnd_277556 95013091026280863049033 := by
  unfold tailWord_277556
  simp only [CollatzResearch.WordTrace]
  refine ⟨5061649491234744817990261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6748865988312993090653681 5061649491234744817990261)
  ·
    refine ⟨474529639803257326686587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5061649491234744817990261 474529639803257326686587)
    ·
      refine ⟨711794459704885990029881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474529639803257326686587 711794459704885990029881)
      ·
        refine ⟨533845844778664492522411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 711794459704885990029881 533845844778664492522411)
        ·
          refine ⟨800768767167996738783617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533845844778664492522411 800768767167996738783617)
          ·
            refine ⟨600576575375997554087713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 800768767167996738783617 600576575375997554087713)
            ·
              refine ⟨450432431531998165565785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600576575375997554087713 450432431531998165565785)
              ·
                refine ⟨337824323648998624174339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450432431531998165565785 337824323648998624174339)
                ·
                  refine ⟨506736485473497936261509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337824323648998624174339 506736485473497936261509)
                  ·
                    refine ⟨95013091026280863049033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 506736485473497936261509 95013091026280863049033)
                    ·
                      rfl

theorem cell22_277556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_277556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277556 prefixEnd_277556 := by exact prefixLift 277556
  have htrace : WordTrace (prefixWord ++ tailWord_277556) baseStart_277556 baseEnd_277556 := by
    simpa [prefixWord, tailWord_277556, baseEnd_277556] using wordTrace_append hprefix tailTrace_277556
  have hstable : (prefixWord ++ tailWord_277556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277556).length < 2 ^ (prefixWord ++ tailWord_277556).sum := by decide
  have hdescent : baseEnd_277556 < baseStart_277556 := by decide
  rcases family_descends (prefixWord ++ tailWord_277556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277642 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_277642 : Nat := 118140960795 + 277642 * 2 ^ 59
def prefixEnd_277642 : Nat := 4983230072969 + 3 ^ 40 * 277642 * 2
def baseEnd_277642 : Nat := 95042530583805305398769

theorem tailTrace_277642 : CollatzResearch.WordTrace tailWord_277642 prefixEnd_277642 95042530583805305398769 := by
  unfold tailWord_277642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2531608915039481580902795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6750957106771950882407453 2531608915039481580902795)
  ·
    refine ⟨3797413372559222371354193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2531608915039481580902795 3797413372559222371354193)
    ·
      refine ⟨2848060029419416778515645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3797413372559222371354193 2848060029419416778515645)
      ·
        refine ⟨1068022511032281291943367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2848060029419416778515645 1068022511032281291943367)
        ·
          refine ⟨1602033766548421937915051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068022511032281291943367 1602033766548421937915051)
          ·
            refine ⟨2403050649822632906872577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602033766548421937915051 2403050649822632906872577)
            ·
              refine ⟨1802287987366974680154433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2403050649822632906872577 1802287987366974680154433)
              ·
                refine ⟨1351715990525231010115825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802287987366974680154433 1351715990525231010115825)
                ·
                  refine ⟨1013786992893923257586869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1351715990525231010115825 1013786992893923257586869)
                  ·
                    refine ⟨95042530583805305398769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1013786992893923257586869 95042530583805305398769)
                    ·
                      rfl

theorem cell22_277642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_277642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277642 prefixEnd_277642 := by exact prefixLift 277642
  have htrace : WordTrace (prefixWord ++ tailWord_277642) baseStart_277642 baseEnd_277642 := by
    simpa [prefixWord, tailWord_277642, baseEnd_277642] using wordTrace_append hprefix tailTrace_277642
  have hstable : (prefixWord ++ tailWord_277642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277642).length < 2 ^ (prefixWord ++ tailWord_277642).sum := by decide
  have hdescent : baseEnd_277642 < baseStart_277642 := by decide
  rcases family_descends (prefixWord ++ tailWord_277642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277687 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 1, 5]
def baseStart_277687 : Nat := 118140960795 + 277687 * 2 ^ 59
def prefixEnd_277687 : Nat := 4983230072969 + 3 ^ 40 * 277687 * 2
def baseEnd_277687 : Nat := 95057935003440188023631

theorem tailTrace_277687 : CollatzResearch.WordTrace tailWord_277687 prefixEnd_277687 95057935003440188023631 := by
  unfold tailWord_277687
  simp only [CollatzResearch.WordTrace]
  refine ⟨10128076944994899008999315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6752051296663266005999543 10128076944994899008999315)
  ·
    refine ⟨15192115417492348513498973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10128076944994899008999315 15192115417492348513498973)
    ·
      refine ⟨5697043281559630692562115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15192115417492348513498973 5697043281559630692562115)
      ·
        refine ⟨8545564922339446038843173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5697043281559630692562115 8545564922339446038843173)
        ·
          refine ⟨1602293422938646132283095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8545564922339446038843173 1602293422938646132283095)
          ·
            refine ⟨2403440134407969198424643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602293422938646132283095 2403440134407969198424643)
            ·
              refine ⟨3605160201611953797636965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2403440134407969198424643 3605160201611953797636965)
              ·
                refine ⟨675967537802241337056931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3605160201611953797636965 675967537802241337056931)
                ·
                  refine ⟨1013951306703362005585397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675967537802241337056931 1013951306703362005585397)
                  ·
                    refine ⟨95057935003440188023631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1013951306703362005585397 95057935003440188023631)
                    ·
                      rfl

theorem cell22_277687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_277687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277687 prefixEnd_277687 := by exact prefixLift 277687
  have htrace : WordTrace (prefixWord ++ tailWord_277687) baseStart_277687 baseEnd_277687 := by
    simpa [prefixWord, tailWord_277687, baseEnd_277687] using wordTrace_append hprefix tailTrace_277687
  have hstable : (prefixWord ++ tailWord_277687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277687).length < 2 ^ (prefixWord ++ tailWord_277687).sum := by decide
  have hdescent : baseEnd_277687 < baseStart_277687 := by decide
  rcases family_descends (prefixWord ++ tailWord_277687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277689 : List Nat := [1, 2, 1, 4, 1, 3, 1, 5, 4]
def baseStart_277689 : Nat := 118140960795 + 277689 * 2 ^ 59
def prefixEnd_277689 : Nat := 4983230072969 + 3 ^ 40 * 277689 * 2
def baseEnd_277689 : Nat := 31686206548104283157875

theorem tailTrace_277689 : CollatzResearch.WordTrace tailWord_277689 prefixEnd_277689 31686206548104283157875 := by
  unfold tailWord_277689
  simp only [CollatzResearch.WordTrace]
  refine ⟨10128149890987653350572121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6752099927325102233714747 10128149890987653350572121)
  ·
    refine ⟨7596112418240740012929091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10128149890987653350572121 7596112418240740012929091)
    ·
      refine ⟨11394168627361110019393637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7596112418240740012929091 11394168627361110019393637)
      ·
        refine ⟨2136406617630208128636307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11394168627361110019393637 2136406617630208128636307)
        ·
          refine ⟨3204609926445312192954461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136406617630208128636307 3204609926445312192954461)
          ·
            refine ⟨1201728722416992072357923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3204609926445312192954461 1201728722416992072357923)
            ·
              refine ⟨1802593083625488108536885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201728722416992072357923 1802593083625488108536885)
              ·
                refine ⟨168993101589889510175333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1802593083625488108536885 168993101589889510175333)
                ·
                  refine ⟨31686206548104283157875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168993101589889510175333 31686206548104283157875)
                  ·
                    rfl

theorem cell22_277689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 4].length) (baseStart_277689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277689 prefixEnd_277689 := by exact prefixLift 277689
  have htrace : WordTrace (prefixWord ++ tailWord_277689) baseStart_277689 baseEnd_277689 := by
    simpa [prefixWord, tailWord_277689, baseEnd_277689] using wordTrace_append hprefix tailTrace_277689
  have hstable : (prefixWord ++ tailWord_277689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277689).length < 2 ^ (prefixWord ++ tailWord_277689).sum := by decide
  have hdescent : baseEnd_277689 < baseStart_277689 := by decide
  rcases family_descends (prefixWord ++ tailWord_277689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277777 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_277777 : Nat := 118140960795 + 277777 * 2 ^ 59
def prefixEnd_277777 : Nat := 4983230072969 + 3 ^ 40 * 277777 * 2
def baseEnd_277777 : Nat := 95088743842709953273355

theorem tailTrace_277777 : CollatzResearch.WordTrace tailWord_277777 prefixEnd_277777 95088743842709953273355 := by
  unfold tailWord_277777
  simp only [CollatzResearch.WordTrace]
  refine ⟨10131359514668844379775585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6754239676445896253183723 10131359514668844379775585)
  ·
    refine ⟨7598519636001633284831689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10131359514668844379775585 7598519636001633284831689)
    ·
      refine ⟨5698889727001224963623767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7598519636001633284831689 5698889727001224963623767)
      ·
        refine ⟨8548334590501837445435651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5698889727001224963623767 8548334590501837445435651)
        ·
          refine ⟨12822501885752756168153477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8548334590501837445435651 12822501885752756168153477)
          ·
            refine ⟨2404219103578641781528777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12822501885752756168153477 2404219103578641781528777)
            ·
              refine ⟨1803164327683981336146583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2404219103578641781528777 1803164327683981336146583)
              ·
                refine ⟨2704746491525972004219875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803164327683981336146583 2704746491525972004219875)
                ·
                  refine ⟨4057119737288958006329813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704746491525972004219875 4057119737288958006329813)
                  ·
                    refine ⟨95088743842709953273355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4057119737288958006329813 95088743842709953273355)
                    ·
                      rfl

theorem cell22_277777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_277777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277777 prefixEnd_277777 := by exact prefixLift 277777
  have htrace : WordTrace (prefixWord ++ tailWord_277777) baseStart_277777 baseEnd_277777 := by
    simpa [prefixWord, tailWord_277777, baseEnd_277777] using wordTrace_append hprefix tailTrace_277777
  have hstable : (prefixWord ++ tailWord_277777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277777).length < 2 ^ (prefixWord ++ tailWord_277777).sum := by decide
  have hdescent : baseEnd_277777 < baseStart_277777 := by decide
  rcases family_descends (prefixWord ++ tailWord_277777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277817 : List Nat := [1, 2, 1, 6, 2, 2, 2, 2, 1, 3]
def baseStart_277817 : Nat := 118140960795 + 277817 * 2 ^ 59
def prefixEnd_277817 : Nat := 4983230072969 + 3 ^ 40 * 277817 * 2
def baseEnd_277817 : Nat := 95102436660163182273233

theorem tailTrace_277817 : CollatzResearch.WordTrace tailWord_277817 prefixEnd_277817 95102436660163182273233 := by
  unfold tailWord_277817
  simp only [CollatzResearch.WordTrace]
  refine ⟨10132818434523931211231705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6755212289682620807487803 10132818434523931211231705)
  ·
    refine ⟨7599613825892948408423779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10132818434523931211231705 7599613825892948408423779)
    ·
      refine ⟨11399420738839422612635669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7599613825892948408423779 11399420738839422612635669)
      ·
        refine ⟨534347847133097934967297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11399420738839422612635669 534347847133097934967297)
        ·
          refine ⟨400760885349823451225473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534347847133097934967297 400760885349823451225473)
          ·
            refine ⟨300570664012367588419105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400760885349823451225473 300570664012367588419105)
            ·
              refine ⟨225427998009275691314329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300570664012367588419105 225427998009275691314329)
              ·
                refine ⟨169070998506956768485747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225427998009275691314329 169070998506956768485747)
                ·
                  refine ⟨253606497760435152728621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169070998506956768485747 253606497760435152728621)
                  ·
                    refine ⟨95102436660163182273233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 253606497760435152728621 95102436660163182273233)
                    ·
                      rfl

theorem cell22_277817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 1, 3].length) (baseStart_277817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_277817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_277817 prefixEnd_277817 := by exact prefixLift 277817
  have htrace : WordTrace (prefixWord ++ tailWord_277817) baseStart_277817 baseEnd_277817 := by
    simpa [prefixWord, tailWord_277817, baseEnd_277817] using wordTrace_append hprefix tailTrace_277817
  have hstable : (prefixWord ++ tailWord_277817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277817).length < 2 ^ (prefixWord ++ tailWord_277817).sum := by decide
  have hdescent : baseEnd_277817 < baseStart_277817 := by decide
  rcases family_descends (prefixWord ++ tailWord_277817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
