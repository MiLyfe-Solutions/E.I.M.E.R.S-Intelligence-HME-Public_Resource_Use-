import V185TrunkScan23Chunk0773

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4577489 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 1, 6]
def baseStart_4577489 : Nat := 118140960795 + 4577489 * 2 ^ 59
def prefixEnd_4577489 : Nat := 4983230072969 + 3 ^ 40 * 4577489 * 2
def baseEnd_4577489 : Nat := 783484015889582095645339

theorem tailTrace_4577489 : CollatzResearch.WordTrace tailWord_4577489 prefixEnd_4577489 783484015889582095645339 := by
  unfold tailWord_4577489
  simp only [CollatzResearch.WordTrace]
  refine ⟨166954739713546600726191521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111303159809031067150794347 166954739713546600726191521)
  ·
    refine ⟨125216054785159950544643641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166954739713546600726191521 125216054785159950544643641)
    ·
      refine ⟨93912041088869962908482731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125216054785159950544643641 93912041088869962908482731)
      ·
        refine ⟨140868061633304944362724097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93912041088869962908482731 140868061633304944362724097)
        ·
          refine ⟨105651046224978708272043073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140868061633304944362724097 105651046224978708272043073)
          ·
            refine ⟨79238284668734031204032305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105651046224978708272043073 79238284668734031204032305)
            ·
              refine ⟨59428713501550523403024229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79238284668734031204032305 59428713501550523403024229)
              ·
                refine ⟨11142883781540723138067043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59428713501550523403024229 11142883781540723138067043)
                ·
                  refine ⟨16714325672311084707100565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11142883781540723138067043 16714325672311084707100565)
                  ·
                    refine ⟨783484015889582095645339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16714325672311084707100565 783484015889582095645339)
                    ·
                      rfl

theorem cell23_4577489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_4577489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577489 prefixEnd_4577489 := by exact prefixLift 4577489
  have htrace : WordTrace (prefixWord ++ tailWord_4577489) baseStart_4577489 baseEnd_4577489 := by
    simpa [prefixWord, tailWord_4577489, baseEnd_4577489] using wordTrace_append hprefix tailTrace_4577489
  have hstable : (prefixWord ++ tailWord_4577489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577489).length < 2 ^ (prefixWord ++ tailWord_4577489).sum := by decide
  have hdescent : baseEnd_4577489 < baseStart_4577489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577499 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 5]
def baseStart_4577499 : Nat := 118140960795 + 4577499 * 2 ^ 59
def prefixEnd_4577499 : Nat := 4983230072969 + 3 ^ 40 * 4577499 * 2
def baseEnd_4577499 : Nat := 2350457182475291247810971

theorem tailTrace_4577499 : CollatzResearch.WordTrace tailWord_4577499 prefixEnd_4577499 2350457182475291247810971 := by
  unfold tailWord_4577499
  simp only [CollatzResearch.WordTrace]
  refine ⟨166955104443510372434055551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111303402962340248289370367 166955104443510372434055551)
  ·
    refine ⟨250432656665265558651083327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166955104443510372434055551 250432656665265558651083327)
    ·
      refine ⟨375648984997898337976624991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250432656665265558651083327 375648984997898337976624991)
      ·
        refine ⟨563473477496847506964937487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375648984997898337976624991 563473477496847506964937487)
        ·
          refine ⟨845210216245271260447406231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563473477496847506964937487 845210216245271260447406231)
          ·
            refine ⟨1267815324367906890671109347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845210216245271260447406231 1267815324367906890671109347)
            ·
              refine ⟨1901722986551860336006664021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267815324367906890671109347 1901722986551860336006664021)
              ·
                refine ⟨11142908124327306656289047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1901722986551860336006664021 11142908124327306656289047)
                ·
                  refine ⟨16714362186490959984433571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11142908124327306656289047 16714362186490959984433571)
                  ·
                    refine ⟨25071543279736439976650357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16714362186490959984433571 25071543279736439976650357)
                    ·
                      refine ⟨2350457182475291247810971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25071543279736439976650357 2350457182475291247810971)
                      ·
                        rfl

theorem cell23_4577499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 5].length) (baseStart_4577499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577499 prefixEnd_4577499 := by exact prefixLift 4577499
  have htrace : WordTrace (prefixWord ++ tailWord_4577499) baseStart_4577499 baseEnd_4577499 := by
    simpa [prefixWord, tailWord_4577499, baseEnd_4577499] using wordTrace_append hprefix tailTrace_4577499
  have hstable : (prefixWord ++ tailWord_4577499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577499).length < 2 ^ (prefixWord ++ tailWord_4577499).sum := by decide
  have hdescent : baseEnd_4577499 < baseStart_4577499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577507 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4577507 : Nat := 118140960795 + 4577507 * 2 ^ 59
def prefixEnd_4577507 : Nat := 4983230072969 + 3 ^ 40 * 4577507 * 2
def baseEnd_4577507 : Nat := 2350461290320527216510935

theorem tailTrace_4577507 : CollatzResearch.WordTrace tailWord_4577507 prefixEnd_4577507 2350461290320527216510935 := by
  unfold tailWord_4577507
  simp only [CollatzResearch.WordTrace]
  refine ⟨166955396227481389800346775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111303597484987593200231183 166955396227481389800346775)
  ·
    refine ⟨250433094341222084700520163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166955396227481389800346775 250433094341222084700520163)
    ·
      refine ⟨375649641511833127050780245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250433094341222084700520163 375649641511833127050780245)
      ·
        refine ⟨4402144236466794457626331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 375649641511833127050780245 4402144236466794457626331)
        ·
          refine ⟨6603216354700191686439497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4402144236466794457626331 6603216354700191686439497)
          ·
            refine ⟨4952412266025143764829623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6603216354700191686439497 4952412266025143764829623)
            ·
              refine ⟨7428618399037715647244435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4952412266025143764829623 7428618399037715647244435)
              ·
                refine ⟨11142927598556573470866653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7428618399037715647244435 11142927598556573470866653)
                ·
                  refine ⟨4178597849458715051574995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11142927598556573470866653 4178597849458715051574995)
                  ·
                    refine ⟨6267896774188072577362493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4178597849458715051574995 6267896774188072577362493)
                    ·
                      refine ⟨2350461290320527216510935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6267896774188072577362493 2350461290320527216510935)
                      ·
                        rfl

theorem cell23_4577507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4577507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577507 prefixEnd_4577507 := by exact prefixLift 4577507
  have htrace : WordTrace (prefixWord ++ tailWord_4577507) baseStart_4577507 baseEnd_4577507 := by
    simpa [prefixWord, tailWord_4577507, baseEnd_4577507] using wordTrace_append hprefix tailTrace_4577507
  have hstable : (prefixWord ++ tailWord_4577507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577507).length < 2 ^ (prefixWord ++ tailWord_4577507).sum := by decide
  have hdescent : baseEnd_4577507 < baseStart_4577507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577516 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 3]
def baseStart_4577516 : Nat := 118140960795 + 4577516 * 2 ^ 59
def prefixEnd_4577516 : Nat := 4983230072969 + 3 ^ 40 * 4577516 * 2
def baseEnd_4577516 : Nat := 2350465911646417681298393

theorem tailTrace_4577516 : CollatzResearch.WordTrace tailWord_4577516 prefixEnd_4577516 2350465911646417681298393 := by
  unfold tailWord_4577516
  simp only [CollatzResearch.WordTrace]
  refine ⟨83477862242224392168712201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111303816322965856224949601 83477862242224392168712201)
  ·
    refine ⟨62608396681668294126534151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83477862242224392168712201 62608396681668294126534151)
    ·
      refine ⟨93912595022502441189801227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62608396681668294126534151 93912595022502441189801227)
      ·
        refine ⟨140868892533753661784701841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93912595022502441189801227 140868892533753661784701841)
        ·
          refine ⟨105651669400315246338526381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140868892533753661784701841 105651669400315246338526381)
          ·
            refine ⟨39619376025118217376947393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105651669400315246338526381 39619376025118217376947393)
            ·
              refine ⟨29714532018838663032710545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39619376025118217376947393 29714532018838663032710545)
              ·
                refine ⟨22285899014128997274532909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29714532018838663032710545 22285899014128997274532909)
                ·
                  refine ⟨8357212130298373977949841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22285899014128997274532909 8357212130298373977949841)
                  ·
                    refine ⟨6267909097723780483462381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8357212130298373977949841 6267909097723780483462381)
                    ·
                      refine ⟨2350465911646417681298393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6267909097723780483462381 2350465911646417681298393)
                      ·
                        rfl

theorem cell23_4577516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_4577516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577516 prefixEnd_4577516 := by exact prefixLift 4577516
  have htrace : WordTrace (prefixWord ++ tailWord_4577516) baseStart_4577516 baseEnd_4577516 := by
    simpa [prefixWord, tailWord_4577516, baseEnd_4577516] using wordTrace_append hprefix tailTrace_4577516
  have hstable : (prefixWord ++ tailWord_4577516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577516).length < 2 ^ (prefixWord ++ tailWord_4577516).sum := by decide
  have hdescent : baseEnd_4577516 < baseStart_4577516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577519 : List Nat := [1, 1, 2, 1, 6, 1, 1, 10]
def baseStart_4577519 : Nat := 118140960795 + 4577519 * 2 ^ 59
def prefixEnd_4577519 : Nat := 4983230072969 + 3 ^ 40 * 4577519 * 2
def baseEnd_4577519 : Nat := 87054350077347450724477

theorem tailTrace_4577519 : CollatzResearch.WordTrace tailWord_4577519 prefixEnd_4577519 87054350077347450724477 := by
  unfold tailWord_4577519
  simp only [CollatzResearch.WordTrace]
  refine ⟨166955833903437915849783611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111303889268958610566522407 166955833903437915849783611)
  ·
    refine ⟨250433750855156873774675417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166955833903437915849783611 250433750855156873774675417)
    ·
      refine ⟨187825313141367655331006563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250433750855156873774675417 187825313141367655331006563)
      ·
        refine ⟨281737969712051482996509845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187825313141367655331006563 281737969712051482996509845)
        ·
          refine ⟨13206467330252413265461399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 281737969712051482996509845 13206467330252413265461399)
          ·
            refine ⟨19809700995378619898192099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13206467330252413265461399 19809700995378619898192099)
            ·
              refine ⟨29714551493067929847288149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19809700995378619898192099 29714551493067929847288149)
              ·
                refine ⟨87054350077347450724477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29714551493067929847288149 87054350077347450724477)
                ·
                  rfl

theorem cell23_4577519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 10].length) (baseStart_4577519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577519 prefixEnd_4577519 := by exact prefixLift 4577519
  have htrace : WordTrace (prefixWord ++ tailWord_4577519) baseStart_4577519 baseEnd_4577519 := by
    simpa [prefixWord, tailWord_4577519, baseEnd_4577519] using wordTrace_append hprefix tailTrace_4577519
  have hstable : (prefixWord ++ tailWord_4577519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577519).length < 2 ^ (prefixWord ++ tailWord_4577519).sum := by decide
  have hdescent : baseEnd_4577519 < baseStart_4577519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577526 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_4577526 : Nat := 118140960795 + 4577526 * 2 ^ 59
def prefixEnd_4577526 : Nat := 4983230072969 + 3 ^ 40 * 4577526 * 2
def baseEnd_4577526 : Nat := 2350471046452962642173347

theorem tailTrace_4577526 : CollatzResearch.WordTrace tailWord_4577526 prefixEnd_4577526 2350471046452962642173347 := by
  unfold tailWord_4577526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10434755575900784752830527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111304059476275037363525621 10434755575900784752830527)
  ·
    refine ⟨15652133363851177129245791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10434755575900784752830527 15652133363851177129245791)
    ·
      refine ⟨23478200045776765693868687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15652133363851177129245791 23478200045776765693868687)
      ·
        refine ⟨35217300068665148540803031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23478200045776765693868687 35217300068665148540803031)
        ·
          refine ⟨52825950102997722811204547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35217300068665148540803031 52825950102997722811204547)
          ·
            refine ⟨79238925154496584216806821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52825950102997722811204547 79238925154496584216806821)
            ·
              refine ⟨14857298466468109540651279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79238925154496584216806821 14857298466468109540651279)
              ·
                refine ⟨22285947699702164310976919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14857298466468109540651279 22285947699702164310976919)
                ·
                  refine ⟨33428921549553246466465379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22285947699702164310976919 33428921549553246466465379)
                  ·
                    refine ⟨50143382324329869699698069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33428921549553246466465379 50143382324329869699698069)
                    ·
                      refine ⟨2350471046452962642173347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50143382324329869699698069 2350471046452962642173347)
                      ·
                        rfl

theorem cell23_4577526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_4577526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577526 prefixEnd_4577526 := by exact prefixLift 4577526
  have htrace : WordTrace (prefixWord ++ tailWord_4577526) baseStart_4577526 baseEnd_4577526 := by
    simpa [prefixWord, tailWord_4577526, baseEnd_4577526] using wordTrace_append hprefix tailTrace_4577526
  have hstable : (prefixWord ++ tailWord_4577526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577526).length < 2 ^ (prefixWord ++ tailWord_4577526).sum := by decide
  have hdescent : baseEnd_4577526 < baseStart_4577526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577546 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_4577546 : Nat := 118140960795 + 4577546 * 2 ^ 59
def prefixEnd_4577546 : Nat := 4983230072969 + 3 ^ 40 * 4577546 * 2
def baseEnd_4577546 : Nat := 2350481316066052563923255

theorem tailTrace_4577546 : CollatzResearch.WordTrace tailWord_4577546 prefixEnd_4577546 2350481316066052563923255 := by
  unfold tailWord_4577546
  simp only [CollatzResearch.WordTrace]
  refine ⟨41739204668585024865254123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111304545782893399640677661 41739204668585024865254123)
  ·
    refine ⟨62608807002877537297881185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41739204668585024865254123 62608807002877537297881185)
    ·
      refine ⟨46956605252158152973410889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62608807002877537297881185 46956605252158152973410889)
      ·
        refine ⟨35217453939118614730058167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46956605252158152973410889 35217453939118614730058167)
        ·
          refine ⟨52826180908677922095087251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35217453939118614730058167 52826180908677922095087251)
          ·
            refine ⟨79239271363016883142630877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52826180908677922095087251 79239271363016883142630877)
            ·
              refine ⟨29714726761131331178486579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79239271363016883142630877 29714726761131331178486579)
              ·
                refine ⟨44572090141696996767729869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29714726761131331178486579 44572090141696996767729869)
                ·
                  refine ⟨16714533803136373787898701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44572090141696996767729869 16714533803136373787898701)
                  ·
                    refine ⟨6267950176176140170462013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16714533803136373787898701 6267950176176140170462013)
                    ·
                      refine ⟨2350481316066052563923255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6267950176176140170462013 2350481316066052563923255)
                      ·
                        rfl

theorem cell23_4577546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_4577546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577546 prefixEnd_4577546 := by exact prefixLift 4577546
  have htrace : WordTrace (prefixWord ++ tailWord_4577546) baseStart_4577546 baseEnd_4577546 := by
    simpa [prefixWord, tailWord_4577546, baseEnd_4577546] using wordTrace_append hprefix tailTrace_4577546
  have hstable : (prefixWord ++ tailWord_4577546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577546).length < 2 ^ (prefixWord ++ tailWord_4577546).sum := by decide
  have hdescent : baseEnd_4577546 < baseStart_4577546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577550 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3]
def baseStart_4577550 : Nat := 118140960795 + 4577550 * 2 ^ 59
def prefixEnd_4577550 : Nat := 4983230072969 + 3 ^ 40 * 4577550 * 2
def baseEnd_4577550 : Nat := 2350483369988670548273237

theorem tailTrace_4577550 : CollatzResearch.WordTrace tailWord_4577550 prefixEnd_4577550 2350483369988670548273237 := by
  unfold tailWord_4577550
  simp only [CollatzResearch.WordTrace]
  refine ⟨20869620570790701018020263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111304643044217072096108069 20869620570790701018020263)
  ·
    refine ⟨31304430856186051527030395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20869620570790701018020263 31304430856186051527030395)
    ·
      refine ⟨46956646284279077290545593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31304430856186051527030395 46956646284279077290545593)
      ·
        refine ⟨35217484713209307967909195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46956646284279077290545593 35217484713209307967909195)
        ·
          refine ⟨52826227069813961951863793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35217484713209307967909195 52826227069813961951863793)
          ·
            refine ⟨39619670302360471463897845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52826227069813961951863793 39619670302360471463897845)
            ·
              refine ⟨3714344090846294199740423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39619670302360471463897845 3714344090846294199740423)
              ·
                refine ⟨5571516136269441299610635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3714344090846294199740423 5571516136269441299610635)
                ·
                  refine ⟨8357274204404161949415953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5571516136269441299610635 8357274204404161949415953)
                  ·
                    refine ⟨6267955653303121462061965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8357274204404161949415953 6267955653303121462061965)
                    ·
                      refine ⟨2350483369988670548273237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6267955653303121462061965 2350483369988670548273237)
                      ·
                        rfl

theorem cell23_4577550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_4577550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577550 prefixEnd_4577550 := by exact prefixLift 4577550
  have htrace : WordTrace (prefixWord ++ tailWord_4577550) baseStart_4577550 baseEnd_4577550 := by
    simpa [prefixWord, tailWord_4577550, baseEnd_4577550] using wordTrace_append hprefix tailTrace_4577550
  have hstable : (prefixWord ++ tailWord_4577550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577550).length < 2 ^ (prefixWord ++ tailWord_4577550).sum := by decide
  have hdescent : baseEnd_4577550 < baseStart_4577550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577563 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 2, 1, 3]
def baseStart_4577563 : Nat := 118140960795 + 4577563 * 2 ^ 59
def prefixEnd_4577563 : Nat := 4983230072969 + 3 ^ 40 * 4577563 * 2
def baseEnd_4577563 : Nat := 2350490045237178997410677

theorem tailTrace_4577563 : CollatzResearch.WordTrace tailWord_4577563 prefixEnd_4577563 2350490045237178997410677 := by
  unfold tailWord_4577563
  simp only [CollatzResearch.WordTrace]
  refine ⟨166957438715278511364385343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111304959143519007576256895 166957438715278511364385343)
  ·
    refine ⟨250436158072917767046578015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166957438715278511364385343 250436158072917767046578015)
    ·
      refine ⟨375654237109376650569867023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250436158072917767046578015 375654237109376650569867023)
      ·
        refine ⟨563481355664064975854800535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375654237109376650569867023 563481355664064975854800535)
        ·
          refine ⟨845222033496097463782200803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563481355664064975854800535 845222033496097463782200803)
          ·
            refine ⟨1267833050244146195673301205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845222033496097463782200803 1267833050244146195673301205)
            ·
              refine ⟨29714837115097176461092997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1267833050244146195673301205 29714837115097176461092997)
              ·
                refine ⟨5571531959080720586454937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29714837115097176461092997 5571531959080720586454937)
                ·
                  refine ⟨4178648969310540439841203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5571531959080720586454937 4178648969310540439841203)
                  ·
                    refine ⟨6267973453965810659761805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4178648969310540439841203 6267973453965810659761805)
                    ·
                      refine ⟨2350490045237178997410677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6267973453965810659761805 2350490045237178997410677)
                      ·
                        rfl

theorem cell23_4577563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 1, 3].length) (baseStart_4577563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577563 prefixEnd_4577563 := by exact prefixLift 4577563
  have htrace : WordTrace (prefixWord ++ tailWord_4577563) baseStart_4577563 baseEnd_4577563 := by
    simpa [prefixWord, tailWord_4577563, baseEnd_4577563] using wordTrace_append hprefix tailTrace_4577563
  have hstable : (prefixWord ++ tailWord_4577563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577563).length < 2 ^ (prefixWord ++ tailWord_4577563).sum := by decide
  have hdescent : baseEnd_4577563 < baseStart_4577563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577603 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 1, 4, 2]
def baseStart_4577603 : Nat := 118140960795 + 4577603 * 2 ^ 59
def prefixEnd_4577603 : Nat := 4983230072969 + 3 ^ 40 * 4577603 * 2
def baseEnd_4577603 : Nat := 2350510584463358840910493

theorem tailTrace_4577603 : CollatzResearch.WordTrace tailWord_4577603 prefixEnd_4577603 2350510584463358840910493 := by
  unfold tailWord_4577603
  simp only [CollatzResearch.WordTrace]
  refine ⟨166958897635133598195841463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111305931756755732130560975 166958897635133598195841463)
  ·
    refine ⟨250438346452700397293762195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166958897635133598195841463 250438346452700397293762195)
    ·
      refine ⟨375657519679050595940643293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250438346452700397293762195 375657519679050595940643293)
      ·
        refine ⟨140871569879643973477741235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 375657519679050595940643293 140871569879643973477741235)
        ·
          refine ⟨211307354819465960216611853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140871569879643973477741235 211307354819465960216611853)
          ·
            refine ⟨79240258057299735081229445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211307354819465960216611853 79240258057299735081229445)
            ·
              refine ⟨14857548385743700327730521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79240258057299735081229445 14857548385743700327730521)
              ·
                refine ⟨11143161289307775245797891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14857548385743700327730521 11143161289307775245797891)
                ·
                  refine ⟨16714741933961662868696837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11143161289307775245797891 16714741933961662868696837)
                  ·
                    refine ⟨3134014112617811787880657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16714741933961662868696837 3134014112617811787880657)
                    ·
                      refine ⟨2350510584463358840910493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3134014112617811787880657 2350510584463358840910493)
                      ·
                        rfl

theorem cell23_4577603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_4577603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577603 prefixEnd_4577603 := by exact prefixLift 4577603
  have htrace : WordTrace (prefixWord ++ tailWord_4577603) baseStart_4577603 baseEnd_4577603 := by
    simpa [prefixWord, tailWord_4577603, baseEnd_4577603] using wordTrace_append hprefix tailTrace_4577603
  have hstable : (prefixWord ++ tailWord_4577603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577603).length < 2 ^ (prefixWord ++ tailWord_4577603).sum := by decide
  have hdescent : baseEnd_4577603 < baseStart_4577603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577609 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 11]
def baseStart_4577609 : Nat := 118140960795 + 4577609 * 2 ^ 59
def prefixEnd_4577609 : Nat := 4983230072969 + 3 ^ 40 * 4577609 * 2
def baseEnd_4577609 : Nat := 261168185038587313048385

theorem tailTrace_4577609 : CollatzResearch.WordTrace tailWord_4577609 prefixEnd_4577609 261168185038587313048385 := by
  unfold tailWord_4577609
  simp only [CollatzResearch.WordTrace]
  refine ⟨166959116473111861220559881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111306077648741240813706587 166959116473111861220559881)
  ·
    refine ⟨125219337354833895915419911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166959116473111861220559881 125219337354833895915419911)
    ·
      refine ⟨187829006032250843873129867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125219337354833895915419911 187829006032250843873129867)
      ·
        refine ⟨281743509048376265809694801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187829006032250843873129867 281743509048376265809694801)
        ·
          refine ⟨211307631786282199357271101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281743509048376265809694801 211307631786282199357271101)
          ·
            refine ⟨79240361919855824758976663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211307631786282199357271101 79240361919855824758976663)
            ·
              refine ⟨118860542879783737138464995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79240361919855824758976663 118860542879783737138464995)
              ·
                refine ⟨178290814319675605707697493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118860542879783737138464995 178290814319675605707697493)
                ·
                  refine ⟨261168185038587313048385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 178290814319675605707697493 261168185038587313048385)
                  ·
                    rfl

theorem cell23_4577609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 11].length) (baseStart_4577609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577609 prefixEnd_4577609 := by exact prefixLift 4577609
  have htrace : WordTrace (prefixWord ++ tailWord_4577609) baseStart_4577609 baseEnd_4577609 := by
    simpa [prefixWord, tailWord_4577609, baseEnd_4577609] using wordTrace_append hprefix tailTrace_4577609
  have hstable : (prefixWord ++ tailWord_4577609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577609).length < 2 ^ (prefixWord ++ tailWord_4577609).sum := by decide
  have hdescent : baseEnd_4577609 < baseStart_4577609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577616 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_4577616 : Nat := 118140960795 + 4577616 * 2 ^ 59
def prefixEnd_4577616 : Nat := 4983230072969 + 3 ^ 40 * 4577616 * 2
def baseEnd_4577616 : Nat := 2350517259711867290047933

theorem tailTrace_4577616 : CollatzResearch.WordTrace tailWord_4577616 prefixEnd_4577616 2350517259711867290047933 := by
  unfold tailWord_4577616
  simp only [CollatzResearch.WordTrace]
  refine ⟨83479685892043250708032351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111306247856057667610709801 83479685892043250708032351)
  ·
    refine ⟨125219528838064876062048527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83479685892043250708032351 125219528838064876062048527)
    ·
      refine ⟨187829293257097314093072791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125219528838064876062048527 187829293257097314093072791)
      ·
        refine ⟨281743939885645971139609187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187829293257097314093072791 281743939885645971139609187)
        ·
          refine ⟨422615909828468956709413781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281743939885645971139609187 422615909828468956709413781)
          ·
            refine ⟨19810120773209482345753771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 422615909828468956709413781 19810120773209482345753771)
            ·
              refine ⟨29715181159814223518630657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19810120773209482345753771 29715181159814223518630657)
              ·
                refine ⟨22286385869860667638972993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29715181159814223518630657 22286385869860667638972993)
                ·
                  refine ⟨16714789402395500729229745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22286385869860667638972993 16714789402395500729229745)
                  ·
                    refine ⟨12536092051796625546922309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16714789402395500729229745 12536092051796625546922309)
                    ·
                      refine ⟨2350517259711867290047933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12536092051796625546922309 2350517259711867290047933)
                      ·
                        rfl

theorem cell23_4577616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_4577616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577616 prefixEnd_4577616 := by exact prefixLift 4577616
  have htrace : WordTrace (prefixWord ++ tailWord_4577616) baseStart_4577616 baseEnd_4577616 := by
    simpa [prefixWord, tailWord_4577616, baseEnd_4577616] using wordTrace_append hprefix tailTrace_4577616
  have hstable : (prefixWord ++ tailWord_4577616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577616).length < 2 ^ (prefixWord ++ tailWord_4577616).sum := by decide
  have hdescent : baseEnd_4577616 < baseStart_4577616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577619 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 9]
def baseStart_4577619 : Nat := 118140960795 + 4577619 * 2 ^ 59
def prefixEnd_4577619 : Nat := 4983230072969 + 3 ^ 40 * 4577619 * 2
def baseEnd_4577619 : Nat := 2350518800153830778310419

theorem tailTrace_4577619 : CollatzResearch.WordTrace tailWord_4577619 prefixEnd_4577619 2350518800153830778310419 := by
  unfold tailWord_4577619
  simp only [CollatzResearch.WordTrace]
  refine ⟨166959481203075632928423911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111306320802050421952282607 166959481203075632928423911)
  ·
    refine ⟨250439221804613449392635867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166959481203075632928423911 250439221804613449392635867)
    ·
      refine ⟨375658832706920174088953801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250439221804613449392635867 375658832706920174088953801)
      ·
        refine ⟨281744124530190130566715351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375658832706920174088953801 281744124530190130566715351)
        ·
          refine ⟨422616186795285195850073027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281744124530190130566715351 422616186795285195850073027)
          ·
            refine ⟨633924280192927793775109541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422616186795285195850073027 633924280192927793775109541)
            ·
              refine ⟨118860802536173961332833039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 633924280192927793775109541 118860802536173961332833039)
              ·
                refine ⟨178291203804260941999249559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118860802536173961332833039 178291203804260941999249559)
                ·
                  refine ⟨267436805706391412998874339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178291203804260941999249559 267436805706391412998874339)
                  ·
                    refine ⟨401155208559587119498311509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267436805706391412998874339 401155208559587119498311509)
                    ·
                      refine ⟨2350518800153830778310419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 401155208559587119498311509 2350518800153830778310419)
                      ·
                        rfl

theorem cell23_4577619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_4577619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577619 prefixEnd_4577619 := by exact prefixLift 4577619
  have htrace : WordTrace (prefixWord ++ tailWord_4577619) baseStart_4577619 baseEnd_4577619 := by
    simpa [prefixWord, tailWord_4577619, baseEnd_4577619] using wordTrace_append hprefix tailTrace_4577619
  have hstable : (prefixWord ++ tailWord_4577619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577619).length < 2 ^ (prefixWord ++ tailWord_4577619).sum := by decide
  have hdescent : baseEnd_4577619 < baseStart_4577619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577673 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 2, 5]
def baseStart_4577673 : Nat := 118140960795 + 4577673 * 2 ^ 59
def prefixEnd_4577673 : Nat := 4983230072969 + 3 ^ 40 * 4577673 * 2
def baseEnd_4577673 : Nat := 783515509369724522345057

theorem tailTrace_4577673 : CollatzResearch.WordTrace tailWord_4577673 prefixEnd_4577673 783515509369724522345057 := by
  unfold tailWord_4577673
  simp only [CollatzResearch.WordTrace]
  refine ⟨166961450744880000150889673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111307633829920000100593115 166961450744880000150889673)
  ·
    refine ⟨125221088058660000113167255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166961450744880000150889673 125221088058660000113167255)
    ·
      refine ⟨187831632087990000169750883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125221088058660000113167255 187831632087990000169750883)
      ·
        refine ⟨281747448131985000254626325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187831632087990000169750883 281747448131985000254626325)
        ·
          refine ⟨13206911631186796886935609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 281747448131985000254626325 13206911631186796886935609)
          ·
            refine ⟨9905183723390097665201707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13206911631186796886935609 9905183723390097665201707)
            ·
              refine ⟨14857775585085146497802561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9905183723390097665201707 14857775585085146497802561)
              ·
                refine ⟨11143331688813859873351921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14857775585085146497802561 11143331688813859873351921)
                ·
                  refine ⟨8357498766610394905013941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11143331688813859873351921 8357498766610394905013941)
                  ·
                    refine ⟨783515509369724522345057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8357498766610394905013941 783515509369724522345057)
                    ·
                      rfl

theorem cell23_4577673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_4577673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577673 prefixEnd_4577673 := by exact prefixLift 4577673
  have htrace : WordTrace (prefixWord ++ tailWord_4577673) baseStart_4577673 baseEnd_4577673 := by
    simpa [prefixWord, tailWord_4577673, baseEnd_4577673] using wordTrace_append hprefix tailTrace_4577673
  have hstable : (prefixWord ++ tailWord_4577673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577673).length < 2 ^ (prefixWord ++ tailWord_4577673).sum := by decide
  have hdescent : baseEnd_4577673 < baseStart_4577673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577720 : List Nat := [2, 1, 2, 1, 2, 2, 1, 7, 1, 4]
def baseStart_4577720 : Nat := 118140960795 + 4577720 * 2 ^ 59
def prefixEnd_4577720 : Nat := 4983230072969 + 3 ^ 40 * 4577720 * 2
def baseEnd_4577720 : Nat := 783523553899978294382485

theorem tailTrace_4577720 : CollatzResearch.WordTrace tailWord_4577720 prefixEnd_4577720 783523553899978294382485 := by
  unfold tailWord_4577720
  simp only [CollatzResearch.WordTrace]
  refine ⟨83481582487854863588925307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111308776650473151451900409 83481582487854863588925307)
  ·
    refine ⟨125222373731782295383387961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83481582487854863588925307 125222373731782295383387961)
    ·
      refine ⟨93916780298836721537540971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125222373731782295383387961 93916780298836721537540971)
      ·
        refine ⟨140875170448255082306311457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93916780298836721537540971 140875170448255082306311457)
        ·
          refine ⟨105656377836191311729733593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140875170448255082306311457 105656377836191311729733593)
          ·
            refine ⟨79242283377143483797300195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105656377836191311729733593 79242283377143483797300195)
            ·
              refine ⟨118863425065715225695950293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79242283377143483797300195 118863425065715225695950293)
              ·
                refine ⟨2785861524977700602248835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 118863425065715225695950293 2785861524977700602248835)
                ·
                  refine ⟨4178792287466550903373253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785861524977700602248835 4178792287466550903373253)
                  ·
                    refine ⟨783523553899978294382485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4178792287466550903373253 783523553899978294382485)
                    ·
                      rfl

theorem cell23_4577720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_4577720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577720 prefixEnd_4577720 := by exact prefixLift 4577720
  have htrace : WordTrace (prefixWord ++ tailWord_4577720) baseStart_4577720 baseEnd_4577720 := by
    simpa [prefixWord, tailWord_4577720, baseEnd_4577720] using wordTrace_append hprefix tailTrace_4577720
  have hstable : (prefixWord ++ tailWord_4577720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577720).length < 2 ^ (prefixWord ++ tailWord_4577720).sum := by decide
  have hdescent : baseEnd_4577720 < baseStart_4577720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577737 : List Nat := [1, 2, 1, 1, 2, 1, 8, 2, 1, 4]
def baseStart_4577737 : Nat := 118140960795 + 4577737 * 2 ^ 59
def prefixEnd_4577737 : Nat := 4983230072969 + 3 ^ 40 * 4577737 * 2
def baseEnd_4577737 : Nat := 783526463623687105544959

theorem tailTrace_4577737 : CollatzResearch.WordTrace tailWord_4577737 prefixEnd_4577737 783526463623687105544959 := by
  unfold tailWord_4577737
  simp only [CollatzResearch.WordTrace]
  refine ⟨166963785016648139081219465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111309190011098759387479643 166963785016648139081219465)
  ·
    refine ⟨125222838762486104310914599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166963785016648139081219465 125222838762486104310914599)
    ·
      refine ⟨187834258143729156466371899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125222838762486104310914599 187834258143729156466371899)
      ·
        refine ⟨281751387215593734699557849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187834258143729156466371899 281751387215593734699557849)
        ·
          refine ⟨211313540411695301024668387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281751387215593734699557849 211313540411695301024668387)
          ·
            refine ⟨316970310617542951537002581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211313540411695301024668387 316970310617542951537002581)
            ·
              refine ⟨3714495827549331463324249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 316970310617542951537002581 3714495827549331463324249)
              ·
                refine ⟨2785871870661998597493187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3714495827549331463324249 2785871870661998597493187)
                ·
                  refine ⟨4178807805992997896239781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785871870661998597493187 4178807805992997896239781)
                  ·
                    refine ⟨783526463623687105544959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4178807805992997896239781 783526463623687105544959)
                    ·
                      rfl

theorem cell23_4577737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 1, 4].length) (baseStart_4577737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577737 prefixEnd_4577737 := by exact prefixLift 4577737
  have htrace : WordTrace (prefixWord ++ tailWord_4577737) baseStart_4577737 baseEnd_4577737 := by
    simpa [prefixWord, tailWord_4577737, baseEnd_4577737] using wordTrace_append hprefix tailTrace_4577737
  have hstable : (prefixWord ++ tailWord_4577737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577737).length < 2 ^ (prefixWord ++ tailWord_4577737).sum := by decide
  have hdescent : baseEnd_4577737 < baseStart_4577737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577750 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_4577750 : Nat := 118140960795 + 4577750 * 2 ^ 59
def prefixEnd_4577750 : Nat := 4983230072969 + 3 ^ 40 * 4577750 * 2
def baseEnd_4577750 : Nat := 261176229568841085085813

theorem tailTrace_4577750 : CollatzResearch.WordTrace tailWord_4577750 prefixEnd_4577750 261176229568841085085813 := by
  unfold tailWord_4577750
  simp only [CollatzResearch.WordTrace]
  refine ⟨10435266197850065143840169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111309506110400694867628469 10435266197850065143840169)
  ·
    refine ⟨7826449648387548857880127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10435266197850065143840169 7826449648387548857880127)
    ·
      refine ⟨11739674472581323286820191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7826449648387548857880127 11739674472581323286820191)
      ·
        refine ⟨17609511708871984930230287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11739674472581323286820191 17609511708871984930230287)
        ·
          refine ⟨26414267563307977395345431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17609511708871984930230287 26414267563307977395345431)
          ·
            refine ⟨39621401344961966093018147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26414267563307977395345431 39621401344961966093018147)
            ·
              refine ⟨59432102017442949139527221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39621401344961966093018147 59432102017442949139527221)
              ·
                refine ⟨5571759564135276481830677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59432102017442949139527221 5571759564135276481830677)
                ·
                  refine ⟨261176229568841085085813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5571759564135276481830677 261176229568841085085813)
                  ·
                    rfl

theorem cell23_4577750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_4577750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577750 prefixEnd_4577750 := by exact prefixLift 4577750
  have htrace : WordTrace (prefixWord ++ tailWord_4577750) baseStart_4577750 baseEnd_4577750 := by
    simpa [prefixWord, tailWord_4577750, baseEnd_4577750] using wordTrace_append hprefix tailTrace_4577750
  have hstable : (prefixWord ++ tailWord_4577750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577750).length < 2 ^ (prefixWord ++ tailWord_4577750).sum := by decide
  have hdescent : baseEnd_4577750 < baseStart_4577750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577760 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 3, 1, 3]
def baseStart_4577760 : Nat := 118140960795 + 4577760 * 2 ^ 59
def prefixEnd_4577760 : Nat := 4983230072969 + 3 ^ 40 * 4577760 * 2
def baseEnd_4577760 : Nat := 2350591200926114726647271

theorem tailTrace_4577760 : CollatzResearch.WordTrace tailWord_4577760 prefixEnd_4577760 2350591200926114726647271 := by
  unfold tailWord_4577760
  simp only [CollatzResearch.WordTrace]
  refine ⟨83482311947782407004653367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111309749263709876006204489 83482311947782407004653367)
  ·
    refine ⟨125223467921673610506980051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83482311947782407004653367 125223467921673610506980051)
    ·
      refine ⟨187835201882510415760470077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125223467921673610506980051 187835201882510415760470077)
      ·
        refine ⟨70438200705941405910176279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187835201882510415760470077 70438200705941405910176279)
        ·
          refine ⟨105657301058912108865264419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70438200705941405910176279 105657301058912108865264419)
          ·
            refine ⟨158485951588368163297896629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105657301058912108865264419 158485951588368163297896629)
            ·
              refine ⟨14858057961409515309177809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158485951588368163297896629 14858057961409515309177809)
              ·
                refine ⟨11143543471057136481883357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14858057961409515309177809 11143543471057136481883357)
                ·
                  refine ⟨4178828801646426180706259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11143543471057136481883357 4178828801646426180706259)
                  ·
                    refine ⟨6268243202469639271059389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4178828801646426180706259 6268243202469639271059389)
                    ·
                      refine ⟨2350591200926114726647271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6268243202469639271059389 2350591200926114726647271)
                      ·
                        rfl

theorem cell23_4577760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_4577760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577760 prefixEnd_4577760 := by exact prefixLift 4577760
  have htrace : WordTrace (prefixWord ++ tailWord_4577760) baseStart_4577760 baseEnd_4577760 := by
    simpa [prefixWord, tailWord_4577760, baseEnd_4577760] using wordTrace_append hprefix tailTrace_4577760
  have hstable : (prefixWord ++ tailWord_4577760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577760).length < 2 ^ (prefixWord ++ tailWord_4577760).sum := by decide
  have hdescent : baseEnd_4577760 < baseStart_4577760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577803 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 5]
def baseStart_4577803 : Nat := 118140960795 + 4577803 * 2 ^ 59
def prefixEnd_4577803 : Nat := 4983230072969 + 3 ^ 40 * 4577803 * 2
def baseEnd_4577803 : Nat := 2350613280594258058409573

theorem tailTrace_4577803 : CollatzResearch.WordTrace tailWord_4577803 prefixEnd_4577803 2350613280594258058409573 := by
  unfold tailWord_4577803
  simp only [CollatzResearch.WordTrace]
  refine ⟨166966192234409032353122063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111310794822939354902081375 166966192234409032353122063)
  ·
    refine ⟨250449288351613548529683095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166966192234409032353122063 250449288351613548529683095)
    ·
      refine ⟨375673932527420322794524643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250449288351613548529683095 375673932527420322794524643)
      ·
        refine ⟨563510898791130484191786965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375673932527420322794524643 563510898791130484191786965)
        ·
          refine ⟨13207286690417120723245007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 563510898791130484191786965 13207286690417120723245007)
          ·
            refine ⟨19810930035625681084867511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13207286690417120723245007 19810930035625681084867511)
            ·
              refine ⟨29716395053438521627301267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19810930035625681084867511 29716395053438521627301267)
              ·
                refine ⟨44574592580157782440951901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29716395053438521627301267 44574592580157782440951901)
                ·
                  refine ⟨16715472217559168415356963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44574592580157782440951901 16715472217559168415356963)
                  ·
                    refine ⟨25073208326338752623035445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16715472217559168415356963 25073208326338752623035445)
                    ·
                      refine ⟨2350613280594258058409573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25073208326338752623035445 2350613280594258058409573)
                      ·
                        rfl

theorem cell23_4577803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 5].length) (baseStart_4577803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577803 prefixEnd_4577803 := by exact prefixLift 4577803
  have htrace : WordTrace (prefixWord ++ tailWord_4577803) baseStart_4577803 baseEnd_4577803 := by
    simpa [prefixWord, tailWord_4577803, baseEnd_4577803] using wordTrace_append hprefix tailTrace_4577803
  have hstable : (prefixWord ++ tailWord_4577803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577803).length < 2 ^ (prefixWord ++ tailWord_4577803).sum := by decide
  have hdescent : baseEnd_4577803 < baseStart_4577803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577813 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_4577813 : Nat := 118140960795 + 4577813 * 2 ^ 59
def prefixEnd_4577813 : Nat := 4983230072969 + 3 ^ 40 * 4577813 * 2
def baseEnd_4577813 : Nat := 2350618415400803019284527

theorem tailTrace_4577813 : CollatzResearch.WordTrace tailWord_4577813 prefixEnd_4577813 2350618415400803019284527 := by
  unfold tailWord_4577813
  simp only [CollatzResearch.WordTrace]
  refine ⟨166966556964372804060986093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111311037976248536040657395 166966556964372804060986093)
  ·
    refine ⟨62612458861639801522869785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166966556964372804060986093 62612458861639801522869785)
    ·
      refine ⟨46959344146229851142152339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62612458861639801522869785 46959344146229851142152339)
      ·
        refine ⟨70439016219344776713228509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46959344146229851142152339 70439016219344776713228509)
        ·
          refine ⟨26414631082254291267460691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70439016219344776713228509 26414631082254291267460691)
          ·
            refine ⟨39621946623381436901191037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26414631082254291267460691 39621946623381436901191037)
            ·
              refine ⟨14858229983768038837946639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39621946623381436901191037 14858229983768038837946639)
              ·
                refine ⟨22287344975652058256919959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14858229983768038837946639 22287344975652058256919959)
                ·
                  refine ⟨33431017463478087385379939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22287344975652058256919959 33431017463478087385379939)
                  ·
                    refine ⟨50146526195217131078069909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33431017463478087385379939 50146526195217131078069909)
                    ·
                      refine ⟨2350618415400803019284527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50146526195217131078069909 2350618415400803019284527)
                      ·
                        rfl

theorem cell23_4577813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_4577813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577813 prefixEnd_4577813 := by exact prefixLift 4577813
  have htrace : WordTrace (prefixWord ++ tailWord_4577813) baseStart_4577813 baseEnd_4577813 := by
    simpa [prefixWord, tailWord_4577813, baseEnd_4577813] using wordTrace_append hprefix tailTrace_4577813
  have hstable : (prefixWord ++ tailWord_4577813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577813).length < 2 ^ (prefixWord ++ tailWord_4577813).sum := by decide
  have hdescent : baseEnd_4577813 < baseStart_4577813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577828 : List Nat := [2, 3, 1, 5, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4577828 : Nat := 118140960795 + 4577828 * 2 ^ 59
def prefixEnd_4577828 : Nat := 4983230072969 + 3 ^ 40 * 4577828 * 2
def baseEnd_4577828 : Nat := 2350626117610620460596959

theorem tailTrace_4577828 : CollatzResearch.WordTrace tailWord_4577828 prefixEnd_4577828 2350626117610620460596959 := by
  unfold tailWord_4577828
  simp only [CollatzResearch.WordTrace]
  refine ⟨83483552029659230811391069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111311402706212307748521425 83483552029659230811391069)
  ·
    refine ⟨31306332011122211554271651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83483552029659230811391069 31306332011122211554271651)
    ·
      refine ⟨46959498016683317331407477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31306332011122211554271651 46959498016683317331407477)
      ·
        refine ⟨4402452939064060999819451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46959498016683317331407477 4402452939064060999819451)
        ·
          refine ⟨6603679408596091499729177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4402452939064060999819451 6603679408596091499729177)
          ·
            refine ⟨4952759556447068624796883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6603679408596091499729177 4952759556447068624796883)
            ·
              refine ⟨7429139334670602937195325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4952759556447068624796883 7429139334670602937195325)
              ·
                refine ⟨2785927250501476101448247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7429139334670602937195325 2785927250501476101448247)
                ·
                  refine ⟨4178890875752214152172371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785927250501476101448247 4178890875752214152172371)
                  ·
                    refine ⟨6268336313628321228258557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4178890875752214152172371 6268336313628321228258557)
                    ·
                      refine ⟨2350626117610620460596959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6268336313628321228258557 2350626117610620460596959)
                      ·
                        rfl

theorem cell23_4577828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4577828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577828 prefixEnd_4577828 := by exact prefixLift 4577828
  have htrace : WordTrace (prefixWord ++ tailWord_4577828) baseStart_4577828 baseEnd_4577828 := by
    simpa [prefixWord, tailWord_4577828, baseEnd_4577828] using wordTrace_append hprefix tailTrace_4577828
  have hstable : (prefixWord ++ tailWord_4577828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577828).length < 2 ^ (prefixWord ++ tailWord_4577828).sum := by decide
  have hdescent : baseEnd_4577828 < baseStart_4577828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577920 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 4]
def baseStart_4577920 : Nat := 118140960795 + 4577920 * 2 ^ 59
def prefixEnd_4577920 : Nat := 4983230072969 + 3 ^ 40 * 4577920 * 2
def baseEnd_4577920 : Nat := 2350673357830834100646535

theorem tailTrace_4577920 : CollatzResearch.WordTrace tailWord_4577920 prefixEnd_4577920 2350673357830834100646535 := by
  unfold tailWord_4577920
  simp only [CollatzResearch.WordTrace]
  refine ⟨83485229787492580667565607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111313639716656774223420809 83485229787492580667565607)
  ·
    refine ⟨125227844681238871001348411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83485229787492580667565607 125227844681238871001348411)
    ·
      refine ⟨187841767021858306502022617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125227844681238871001348411 187841767021858306502022617)
      ·
        refine ⟨140881325266393729876516963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187841767021858306502022617 140881325266393729876516963)
        ·
          refine ⟨211321987899590594814775445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140881325266393729876516963 211321987899590594814775445)
          ·
            refine ⟨9905718182793309131942599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211321987899590594814775445 9905718182793309131942599)
            ·
              refine ⟨14858577274189963697913899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9905718182793309131942599 14858577274189963697913899)
              ·
                refine ⟨22287865911284945546870849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14858577274189963697913899 22287865911284945546870849)
                ·
                  refine ⟨16715899433463709160153137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22287865911284945546870849 16715899433463709160153137)
                  ·
                    refine ⟨12536924575097781870114853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16715899433463709160153137 12536924575097781870114853)
                    ·
                      refine ⟨2350673357830834100646535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12536924575097781870114853 2350673357830834100646535)
                      ·
                        rfl

theorem cell23_4577920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_4577920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577920 prefixEnd_4577920 := by exact prefixLift 4577920
  have htrace : WordTrace (prefixWord ++ tailWord_4577920) baseStart_4577920 baseEnd_4577920 := by
    simpa [prefixWord, tailWord_4577920, baseEnd_4577920] using wordTrace_append hprefix tailTrace_4577920
  have hstable : (prefixWord ++ tailWord_4577920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577920).length < 2 ^ (prefixWord ++ tailWord_4577920).sum := by decide
  have hdescent : baseEnd_4577920 < baseStart_4577920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577924 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_4577924 : Nat := 118140960795 + 4577924 * 2 ^ 59
def prefixEnd_4577924 : Nat := 4983230072969 + 3 ^ 40 * 4577924 * 2
def baseEnd_4577924 : Nat := 2350675411753452084996517

theorem tailTrace_4577924 : CollatzResearch.WordTrace tailWord_4577924 prefixEnd_4577924 2350675411753452084996517 := by
  unfold tailWord_4577924
  simp only [CollatzResearch.WordTrace]
  refine ⟨83485302733485335009138413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111313736977980446678851217 83485302733485335009138413)
  ·
    refine ⟨31306988525057000628426905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83485302733485335009138413 31306988525057000628426905)
    ·
      refine ⟨23480241393792750471320179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31306988525057000628426905 23480241393792750471320179)
      ·
        refine ⟨35220362090689125706980269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23480241393792750471320179 35220362090689125706980269)
        ·
          refine ⟨13207635784008422140117601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35220362090689125706980269 13207635784008422140117601)
          ·
            refine ⟨9905726838006316605088201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13207635784008422140117601 9905726838006316605088201)
            ·
              refine ⟨7429295128504737453816151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9905726838006316605088201 7429295128504737453816151)
              ·
                refine ⟨11143942692757106180724227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7429295128504737453816151 11143942692757106180724227)
                ·
                  refine ⟨16715914039135659271086341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11143942692757106180724227 16715914039135659271086341)
                  ·
                    refine ⟨3134233882337936113328689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16715914039135659271086341 3134233882337936113328689)
                    ·
                      refine ⟨2350675411753452084996517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3134233882337936113328689 2350675411753452084996517)
                      ·
                        rfl

theorem cell23_4577924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_4577924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577924 prefixEnd_4577924 := by exact prefixLift 4577924
  have htrace : WordTrace (prefixWord ++ tailWord_4577924) baseStart_4577924 baseEnd_4577924 := by
    simpa [prefixWord, tailWord_4577924, baseEnd_4577924] using wordTrace_append hprefix tailTrace_4577924
  have hstable : (prefixWord ++ tailWord_4577924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577924).length < 2 ^ (prefixWord ++ tailWord_4577924).sum := by decide
  have hdescent : baseEnd_4577924 < baseStart_4577924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577980 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_4577980 : Nat := 118140960795 + 4577980 * 2 ^ 59
def prefixEnd_4577980 : Nat := 4983230072969 + 3 ^ 40 * 4577980 * 2
def baseEnd_4577980 : Nat := 2350704166670103865896259

theorem tailTrace_4577980 : CollatzResearch.WordTrace tailWord_4577980 prefixEnd_4577980 2350704166670103865896259 := by
  unfold tailWord_4577980
  simp only [CollatzResearch.WordTrace]
  refine ⟨83486323977383895791157697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111315098636511861054876929 83486323977383895791157697)
  ·
    refine ⟨62614742983037921843368273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83486323977383895791157697 62614742983037921843368273)
    ·
      refine ⟨46961057237278441382526205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62614742983037921843368273 46961057237278441382526205)
      ·
        refine ⟨17610396463979415518447327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46961057237278441382526205 17610396463979415518447327)
        ·
          refine ⟨26415594695969123277670991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17610396463979415518447327 26415594695969123277670991)
          ·
            refine ⟨39623392043953684916506487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26415594695969123277670991 39623392043953684916506487)
            ·
              refine ⟨59435088065930527374759731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39623392043953684916506487 59435088065930527374759731)
              ·
                refine ⟨89152632098895791062139597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59435088065930527374759731 89152632098895791062139597)
                ·
                  refine ⟨33432237037085921648302349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89152632098895791062139597 33432237037085921648302349)
                  ·
                    refine ⟨12537088888907220618113381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33432237037085921648302349 12537088888907220618113381)
                    ·
                      refine ⟨2350704166670103865896259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12537088888907220618113381 2350704166670103865896259)
                      ·
                        rfl

theorem cell23_4577980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_4577980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577980 prefixEnd_4577980 := by exact prefixLift 4577980
  have htrace : WordTrace (prefixWord ++ tailWord_4577980) baseStart_4577980 baseEnd_4577980 := by
    simpa [prefixWord, tailWord_4577980, baseEnd_4577980] using wordTrace_append hprefix tailTrace_4577980
  have hstable : (prefixWord ++ tailWord_4577980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577980).length < 2 ^ (prefixWord ++ tailWord_4577980).sum := by decide
  have hdescent : baseEnd_4577980 < baseStart_4577980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578017 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_4578017 : Nat := 118140960795 + 4578017 * 2 ^ 59
def prefixEnd_4578017 : Nat := 4983230072969 + 3 ^ 40 * 4578017 * 2
def baseEnd_4578017 : Nat := 2350723165454320221133589

theorem tailTrace_4578017 : CollatzResearch.WordTrace tailWord_4578017 prefixEnd_4578017 2350723165454320221133589 := by
  unfold tailWord_4578017
  simp only [CollatzResearch.WordTrace]
  refine ⟨166973997455633746901412305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111315998303755831267608203 166973997455633746901412305)
  ·
    refine ⟨125230498091725310176059229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166973997455633746901412305 125230498091725310176059229)
    ·
      refine ⟨46961436784396991316022211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125230498091725310176059229 46961436784396991316022211)
      ·
        refine ⟨70442155176595486974033317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46961436784396991316022211 70442155176595486974033317)
        ·
          refine ⟨13207904095611653807631247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70442155176595486974033317 13207904095611653807631247)
          ·
            refine ⟨19811856143417480711446871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13207904095611653807631247 19811856143417480711446871)
            ·
              refine ⟨29717784215126221067170307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19811856143417480711446871 29717784215126221067170307)
              ·
                refine ⟨44576676322689331600755461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29717784215126221067170307 44576676322689331600755461)
                ·
                  refine ⟨8358126810504249675141649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44576676322689331600755461 8358126810504249675141649)
                  ·
                    refine ⟨6268595107878187256356237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8358126810504249675141649 6268595107878187256356237)
                    ·
                      refine ⟨2350723165454320221133589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6268595107878187256356237 2350723165454320221133589)
                      ·
                        rfl

theorem cell23_4578017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_4578017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578017 prefixEnd_4578017 := by exact prefixLift 4578017
  have htrace : WordTrace (prefixWord ++ tailWord_4578017) baseStart_4578017 baseEnd_4578017 := by
    simpa [prefixWord, tailWord_4578017, baseEnd_4578017] using wordTrace_append hprefix tailTrace_4578017
  have hstable : (prefixWord ++ tailWord_4578017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578017).length < 2 ^ (prefixWord ++ tailWord_4578017).sum := by decide
  have hdescent : baseEnd_4578017 < baseStart_4578017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578020 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 8]
def baseStart_4578020 : Nat := 118140960795 + 4578020 * 2 ^ 59
def prefixEnd_4578020 : Nat := 4983230072969 + 3 ^ 40 * 4578020 * 2
def baseEnd_4578020 : Nat := 261191633988475967710675

theorem tailTrace_4578020 : CollatzResearch.WordTrace tailWord_4578020 prefixEnd_4578020 261191633988475967710675 := by
  unfold tailWord_4578020
  simp only [CollatzResearch.WordTrace]
  refine ⟨83487053437311439206885757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111316071249748585609181009 83487053437311439206885757)
  ·
    refine ⟨31307645038991789702582159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83487053437311439206885757 31307645038991789702582159)
    ·
      refine ⟨46961467558487684553873239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31307645038991789702582159 46961467558487684553873239)
      ·
        refine ⟨70442201337731526830809859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46961467558487684553873239 70442201337731526830809859)
        ·
          refine ⟨105663302006597290246214789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70442201337731526830809859 105663302006597290246214789)
          ·
            refine ⟨19811869126236991921165273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105663302006597290246214789 19811869126236991921165273)
            ·
              refine ⟨14858901844677743940873955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19811869126236991921165273 14858901844677743940873955)
              ·
                refine ⟨22288352767016615911310933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14858901844677743940873955 22288352767016615911310933)
                ·
                  refine ⟨261191633988475967710675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22288352767016615911310933 261191633988475967710675)
                  ·
                    rfl

theorem cell23_4578020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_4578020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578020 prefixEnd_4578020 := by exact prefixLift 4578020
  have htrace : WordTrace (prefixWord ++ tailWord_4578020) baseStart_4578020 baseEnd_4578020 := by
    simpa [prefixWord, tailWord_4578020, baseEnd_4578020] using wordTrace_append hprefix tailTrace_4578020
  have hstable : (prefixWord ++ tailWord_4578020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578020).length < 2 ^ (prefixWord ++ tailWord_4578020).sum := by decide
  have hdescent : baseEnd_4578020 < baseStart_4578020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578047 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 5, 1, 3]
def baseStart_4578047 : Nat := 118140960795 + 4578047 * 2 ^ 59
def prefixEnd_4578047 : Nat := 4983230072969 + 3 ^ 40 * 4578047 * 2
def baseEnd_4578047 : Nat := 2350738569873955103758451

theorem tailTrace_4578047 : CollatzResearch.WordTrace tailWord_4578047 prefixEnd_4578047 2350738569873955103758451 := by
  unfold tailWord_4578047
  simp only [CollatzResearch.WordTrace]
  refine ⟨166975091645525062025004395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111316727763683374683336263 166975091645525062025004395)
  ·
    refine ⟨250462637468287593037506593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166975091645525062025004395 250462637468287593037506593)
    ·
      refine ⟨187846978101215694778129945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250462637468287593037506593 187846978101215694778129945)
      ·
        refine ⟨140885233575911771083597459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187846978101215694778129945 140885233575911771083597459)
        ·
          refine ⟨211327850363867656625396189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140885233575911771083597459 211327850363867656625396189)
          ·
            refine ⟨79247943886450371234523571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211327850363867656625396189 79247943886450371234523571)
            ·
              refine ⟨118871915829675556851785357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79247943886450371234523571 118871915829675556851785357)
              ·
                refine ⟨44576968436128333819419509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118871915829675556851785357 44576968436128333819419509)
                ·
                  refine ⟨4179090790887031295570579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44576968436128333819419509 4179090790887031295570579)
                  ·
                    refine ⟨6268636186330546943355869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4179090790887031295570579 6268636186330546943355869)
                    ·
                      refine ⟨2350738569873955103758451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6268636186330546943355869 2350738569873955103758451)
                      ·
                        rfl

theorem cell23_4578047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_4578047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578047 prefixEnd_4578047 := by exact prefixLift 4578047
  have htrace : WordTrace (prefixWord ++ tailWord_4578047) baseStart_4578047 baseEnd_4578047 := by
    simpa [prefixWord, tailWord_4578047, baseEnd_4578047] using wordTrace_append hprefix tailTrace_4578047
  have hstable : (prefixWord ++ tailWord_4578047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578047).length < 2 ^ (prefixWord ++ tailWord_4578047).sum := by decide
  have hdescent : baseEnd_4578047 < baseStart_4578047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578057 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 1, 5, 2]
def baseStart_4578057 : Nat := 118140960795 + 4578057 * 2 ^ 59
def prefixEnd_4578057 : Nat := 4983230072969 + 3 ^ 40 * 4578057 * 2
def baseEnd_4578057 : Nat := 2350743704680500064633405

theorem tailTrace_4578057 : CollatzResearch.WordTrace tailWord_4578057 prefixEnd_4578057 2350743704680500064633405 := by
  unfold tailWord_4578057
  simp only [CollatzResearch.WordTrace]
  refine ⟨166975456375488833732868425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111316970916992555821912283 166975456375488833732868425)
  ·
    refine ⟨125231592281616625299651319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166975456375488833732868425 125231592281616625299651319)
    ·
      refine ⟨187847388422424937949476979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125231592281616625299651319 187847388422424937949476979)
      ·
        refine ⟨281771082633637406924215469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187847388422424937949476979 281771082633637406924215469)
        ·
          refine ⟨105664155987614027596580801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281771082633637406924215469 105664155987614027596580801)
          ·
            refine ⟨79248116990710520697435601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105664155987614027596580801 79248116990710520697435601)
            ·
              refine ⟨59436087743032890523076701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79248116990710520697435601 59436087743032890523076701)
              ·
                refine ⟨22288532903637333946153763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59436087743032890523076701 22288532903637333946153763)
                ·
                  refine ⟨33432799355456000919230645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22288532903637333946153763 33432799355456000919230645)
                  ·
                    refine ⟨3134324939574000086177873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33432799355456000919230645 3134324939574000086177873)
                    ·
                      refine ⟨2350743704680500064633405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3134324939574000086177873 2350743704680500064633405)
                      ·
                        rfl

theorem cell23_4578057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 5, 2].length) (baseStart_4578057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578057 prefixEnd_4578057 := by exact prefixLift 4578057
  have htrace : WordTrace (prefixWord ++ tailWord_4578057) baseStart_4578057 baseEnd_4578057 := by
    simpa [prefixWord, tailWord_4578057, baseEnd_4578057] using wordTrace_append hprefix tailTrace_4578057
  have hstable : (prefixWord ++ tailWord_4578057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578057).length < 2 ^ (prefixWord ++ tailWord_4578057).sum := by decide
  have hdescent : baseEnd_4578057 < baseStart_4578057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578074 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2]
def baseStart_4578074 : Nat := 118140960795 + 4578074 * 2 ^ 59
def prefixEnd_4578074 : Nat := 4983230072969 + 3 ^ 40 * 4578074 * 2
def baseEnd_4578074 : Nat := 2350752433851626498120827

theorem tailTrace_4578074 : CollatzResearch.WordTrace tailWord_4578074 prefixEnd_4578074 2350752433851626498120827 := by
  unfold tailWord_4578074
  simp only [CollatzResearch.WordTrace]
  refine ⟨41744019104106811409059319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111317384277618163757491517 41744019104106811409059319)
  ·
    refine ⟨62616028656160217113588979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41744019104106811409059319 62616028656160217113588979)
    ·
      refine ⟨93924042984240325670383469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62616028656160217113588979 93924042984240325670383469)
      ·
        refine ⟨35221516119090122126393801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93924042984240325670383469 35221516119090122126393801)
        ·
          refine ⟨26416137089317591594795351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35221516119090122126393801 26416137089317591594795351)
          ·
            refine ⟨39624205633976387392193027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26416137089317591594795351 39624205633976387392193027)
            ·
              refine ⟨59436308450964581088289541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39624205633976387392193027 59436308450964581088289541)
              ·
                refine ⟨11144307834555858954054289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59436308450964581088289541 11144307834555858954054289)
                ·
                  refine ⟨8358230875916894215540717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11144307834555858954054289 8358230875916894215540717)
                  ·
                    refine ⟨3134336578468835330827769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8358230875916894215540717 3134336578468835330827769)
                    ·
                      refine ⟨2350752433851626498120827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3134336578468835330827769 2350752433851626498120827)
                      ·
                        rfl

theorem cell23_4578074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_4578074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578074 prefixEnd_4578074 := by exact prefixLift 4578074
  have htrace : WordTrace (prefixWord ++ tailWord_4578074) baseStart_4578074 baseEnd_4578074 := by
    simpa [prefixWord, tailWord_4578074, baseEnd_4578074] using wordTrace_append hprefix tailTrace_4578074
  have hstable : (prefixWord ++ tailWord_4578074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578074).length < 2 ^ (prefixWord ++ tailWord_4578074).sum := by decide
  have hdescent : baseEnd_4578074 < baseStart_4578074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578081 : List Nat := [1, 2, 3, 2, 1, 2, 3, 4, 1, 1, 3]
def baseStart_4578081 : Nat := 118140960795 + 4578081 * 2 ^ 59
def prefixEnd_4578081 : Nat := 4983230072969 + 3 ^ 40 * 4578081 * 2
def baseEnd_4578081 : Nat := 2350756028216207970733295

theorem tailTrace_4578081 : CollatzResearch.WordTrace tailWord_4578081 prefixEnd_4578081 2350756028216207970733295 := by
  unfold tailWord_4578081
  simp only [CollatzResearch.WordTrace]
  refine ⟨166976331727401885831742097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111317554484934590554494731 166976331727401885831742097)
  ·
    refine ⟨125232248795551414373806573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166976331727401885831742097 125232248795551414373806573)
    ·
      refine ⟨46962093298331780390177465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125232248795551414373806573 46962093298331780390177465)
      ·
        refine ⟨35221569973748835292633099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46962093298331780390177465 35221569973748835292633099)
        ·
          refine ⟨52832354960623252938949649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35221569973748835292633099 52832354960623252938949649)
          ·
            refine ⟨39624266220467439704212237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52832354960623252938949649 39624266220467439704212237)
            ·
              refine ⟨14859099832675289889079589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39624266220467439704212237 14859099832675289889079589)
              ·
                refine ⟨2786081218626616854202423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14859099832675289889079589 2786081218626616854202423)
                ·
                  refine ⟨4179121827939925281303635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2786081218626616854202423 4179121827939925281303635)
                  ·
                    refine ⟨6268682741909887921955453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4179121827939925281303635 6268682741909887921955453)
                    ·
                      refine ⟨2350756028216207970733295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6268682741909887921955453 2350756028216207970733295)
                      ·
                        rfl

theorem cell23_4578081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_4578081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578081 prefixEnd_4578081 := by exact prefixLift 4578081
  have htrace : WordTrace (prefixWord ++ tailWord_4578081) baseStart_4578081 baseEnd_4578081 := by
    simpa [prefixWord, tailWord_4578081, baseEnd_4578081] using wordTrace_append hprefix tailTrace_4578081
  have hstable : (prefixWord ++ tailWord_4578081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578081).length < 2 ^ (prefixWord ++ tailWord_4578081).sum := by decide
  have hdescent : baseEnd_4578081 < baseStart_4578081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578097 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 1, 6]
def baseStart_4578097 : Nat := 118140960795 + 4578097 * 2 ^ 59
def prefixEnd_4578097 : Nat := 4983230072969 + 3 ^ 40 * 4578097 * 2
def baseEnd_4578097 : Nat := 783588081302226636044407

theorem tailTrace_4578097 : CollatzResearch.WordTrace tailWord_4578097 prefixEnd_4578097 783588081302226636044407 := by
  unfold tailWord_4578097
  simp only [CollatzResearch.WordTrace]
  refine ⟨166976915295343920564324545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111317943530229280376216363 166976915295343920564324545)
  ·
    refine ⟨125232686471507940423243409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166976915295343920564324545 125232686471507940423243409)
    ·
      refine ⟨93924514853630955317432557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125232686471507940423243409 93924514853630955317432557)
      ·
        refine ⟨35221693070111608244037209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93924514853630955317432557 35221693070111608244037209)
        ·
          refine ⟨26416269802583706183027907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35221693070111608244037209 26416269802583706183027907)
          ·
            refine ⟨39624404703875559274541861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26416269802583706183027907 39624404703875559274541861)
            ·
              refine ⟨7429575881976667363976599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39624404703875559274541861 7429575881976667363976599)
              ·
                refine ⟨11144363822965001045964899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7429575881976667363976599 11144363822965001045964899)
                ·
                  refine ⟨16716545734447501568947349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11144363822965001045964899 16716545734447501568947349)
                  ·
                    refine ⟨783588081302226636044407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16716545734447501568947349 783588081302226636044407)
                    ·
                      rfl

theorem cell23_4578097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_4578097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578097 prefixEnd_4578097 := by exact prefixLift 4578097
  have htrace : WordTrace (prefixWord ++ tailWord_4578097) baseStart_4578097 baseEnd_4578097 := by
    simpa [prefixWord, tailWord_4578097, baseEnd_4578097] using wordTrace_append hprefix tailTrace_4578097
  have hstable : (prefixWord ++ tailWord_4578097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578097).length < 2 ^ (prefixWord ++ tailWord_4578097).sum := by decide
  have hdescent : baseEnd_4578097 < baseStart_4578097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578118 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_4578118 : Nat := 118140960795 + 4578118 * 2 ^ 59
def prefixEnd_4578118 : Nat := 4983230072969 + 3 ^ 40 * 4578118 * 2
def baseEnd_4578118 : Nat := 783591675666808108656875

theorem tailTrace_4578118 : CollatzResearch.WordTrace tailWord_4578118 prefixEnd_4578118 783591675666808108656875 := by
  unfold tailWord_4578118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218052538383370035963719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111318454152178560767226005 5218052538383370035963719)
  ·
    refine ⟨7827078807575055053945579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5218052538383370035963719 7827078807575055053945579)
    ·
      refine ⟨11740618211362582580918369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7827078807575055053945579 11740618211362582580918369)
      ·
        refine ⟨8805463658521936935688777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11740618211362582580918369 8805463658521936935688777)
        ·
          refine ⟨6604097743891452701766583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8805463658521936935688777 6604097743891452701766583)
          ·
            refine ⟨9906146615837179052649875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6604097743891452701766583 9906146615837179052649875)
            ·
              refine ⟨14859219923755768578974813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9906146615837179052649875 14859219923755768578974813)
              ·
                refine ⟨5572207471408413217115555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14859219923755768578974813 5572207471408413217115555)
                ·
                  refine ⟨8358311207112619825673333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5572207471408413217115555 8358311207112619825673333)
                  ·
                    refine ⟨783591675666808108656875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8358311207112619825673333 783591675666808108656875)
                    ·
                      rfl

theorem cell23_4578118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_4578118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578118 prefixEnd_4578118 := by exact prefixLift 4578118
  have htrace : WordTrace (prefixWord ++ tailWord_4578118) baseStart_4578118 baseEnd_4578118 := by
    simpa [prefixWord, tailWord_4578118, baseEnd_4578118] using wordTrace_append hprefix tailTrace_4578118
  have hstable : (prefixWord ++ tailWord_4578118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578118).length < 2 ^ (prefixWord ++ tailWord_4578118).sum := by decide
  have hdescent : baseEnd_4578118 < baseStart_4578118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578121 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 1, 1, 4]
def baseStart_4578121 : Nat := 118140960795 + 4578121 * 2 ^ 59
def prefixEnd_4578121 : Nat := 4983230072969 + 3 ^ 40 * 4578121 * 2
def baseEnd_4578121 : Nat := 2350776567442387814233111

theorem tailTrace_4578121 : CollatzResearch.WordTrace tailWord_4578121 prefixEnd_4578121 2350776567442387814233111 := by
  unfold tailWord_4578121
  simp only [CollatzResearch.WordTrace]
  refine ⟨166977790647256972663198217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111318527098171315108798811 166977790647256972663198217)
  ·
    refine ⟨125233342985442729497398663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166977790647256972663198217 125233342985442729497398663)
    ·
      refine ⟨187850014478164094246097995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125233342985442729497398663 187850014478164094246097995)
      ·
        refine ⟨281775021717246141369146993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187850014478164094246097995 281775021717246141369146993)
        ·
          refine ⟨211331266287934606026860245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281775021717246141369146993 211331266287934606026860245)
          ·
            refine ⟨4953076553623467328754537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 211331266287934606026860245 4953076553623467328754537)
            ·
              refine ⟨3714807415217600496565903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4953076553623467328754537 3714807415217600496565903)
              ·
                refine ⟨5572211122826400744848855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3714807415217600496565903 5572211122826400744848855)
                ·
                  refine ⟨8358316684239601117273283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5572211122826400744848855 8358316684239601117273283)
                  ·
                    refine ⟨12537475026359401675909925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8358316684239601117273283 12537475026359401675909925)
                    ·
                      refine ⟨2350776567442387814233111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12537475026359401675909925 2350776567442387814233111)
                      ·
                        rfl

theorem cell23_4578121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 1, 4].length) (baseStart_4578121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578121 prefixEnd_4578121 := by exact prefixLift 4578121
  have htrace : WordTrace (prefixWord ++ tailWord_4578121) baseStart_4578121 baseEnd_4578121 := by
    simpa [prefixWord, tailWord_4578121, baseEnd_4578121] using wordTrace_append hprefix tailTrace_4578121
  have hstable : (prefixWord ++ tailWord_4578121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578121).length < 2 ^ (prefixWord ++ tailWord_4578121).sum := by decide
  have hdescent : baseEnd_4578121 < baseStart_4578121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578138 : List Nat := [3, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2]
def baseStart_4578138 : Nat := 118140960795 + 4578138 * 2 ^ 59
def prefixEnd_4578138 : Nat := 4983230072969 + 3 ^ 40 * 4578138 * 2
def baseEnd_4578138 : Nat := 2350785296613514247720533

theorem tailTrace_4578138 : CollatzResearch.WordTrace tailWord_4578138 prefixEnd_4578138 2350785296613514247720533 := by
  unfold tailWord_4578138
  simp only [CollatzResearch.WordTrace]
  refine ⟨41744602672048846141641767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111318940458796923044378045 41744602672048846141641767)
  ·
    refine ⟨62616904008073269212462651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41744602672048846141641767 62616904008073269212462651)
    ·
      refine ⟨93925356012109903818693977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62616904008073269212462651 93925356012109903818693977)
      ·
        refine ⟨70444017009082427864020483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93925356012109903818693977 70444017009082427864020483)
        ·
          refine ⟨105666025513623641796030725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70444017009082427864020483 105666025513623641796030725)
          ·
            refine ⟨19812379783804432836755761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105666025513623641796030725 19812379783804432836755761)
            ·
              refine ⟨14859284837853324627566821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19812379783804432836755761 14859284837853324627566821)
              ·
                refine ⟨2786115907097498367668779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14859284837853324627566821 2786115907097498367668779)
                ·
                  refine ⟨4179173860646247551503169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2786115907097498367668779 4179173860646247551503169)
                  ·
                    refine ⟨3134380395484685663627377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4179173860646247551503169 3134380395484685663627377)
                    ·
                      refine ⟨2350785296613514247720533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3134380395484685663627377 2350785296613514247720533)
                      ·
                        rfl

theorem cell23_4578138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_4578138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578138 prefixEnd_4578138 := by exact prefixLift 4578138
  have htrace : WordTrace (prefixWord ++ tailWord_4578138) baseStart_4578138 baseEnd_4578138 := by
    simpa [prefixWord, tailWord_4578138, baseEnd_4578138] using wordTrace_append hprefix tailTrace_4578138
  have hstable : (prefixWord ++ tailWord_4578138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578138).length < 2 ^ (prefixWord ++ tailWord_4578138).sum := by decide
  have hdescent : baseEnd_4578138 < baseStart_4578138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578158 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4578158 : Nat := 118140960795 + 4578158 * 2 ^ 59
def prefixEnd_4578158 : Nat := 4983230072969 + 3 ^ 40 * 4578158 * 2
def baseEnd_4578158 : Nat := 2350795566226604169470441

theorem tailTrace_4578158 : CollatzResearch.WordTrace tailWord_4578158 prefixEnd_4578158 2350795566226604169470441 := by
  unfold tailWord_4578158
  simp only [CollatzResearch.WordTrace]
  refine ⟨20872392518515365997786891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111319426765415285321530085 20872392518515365997786891)
  ·
    refine ⟨31308588777773048996680337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20872392518515365997786891 31308588777773048996680337)
    ·
      refine ⟨23481441583329786747510253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31308588777773048996680337 23481441583329786747510253)
      ·
        refine ⟨8805540593748670030316345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23481441583329786747510253 8805540593748670030316345)
        ·
          refine ⟨6604155445311502522737259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8805540593748670030316345 6604155445311502522737259)
          ·
            refine ⟨9906233167967253784105889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6604155445311502522737259 9906233167967253784105889)
            ·
              refine ⟨7429674875975440338079417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9906233167967253784105889 7429674875975440338079417)
              ·
                refine ⟨5572256156981580253559563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7429674875975440338079417 5572256156981580253559563)
                ·
                  refine ⟨8358384235472370380339345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5572256156981580253559563 8358384235472370380339345)
                  ·
                    refine ⟨6268788176604277785254509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8358384235472370380339345 6268788176604277785254509)
                    ·
                      refine ⟨2350795566226604169470441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6268788176604277785254509 2350795566226604169470441)
                      ·
                        rfl

theorem cell23_4578158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4578158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578158 prefixEnd_4578158 := by exact prefixLift 4578158
  have htrace : WordTrace (prefixWord ++ tailWord_4578158) baseStart_4578158 baseEnd_4578158 := by
    simpa [prefixWord, tailWord_4578158, baseEnd_4578158] using wordTrace_append hprefix tailTrace_4578158
  have hstable : (prefixWord ++ tailWord_4578158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578158).length < 2 ^ (prefixWord ++ tailWord_4578158).sum := by decide
  have hdescent : baseEnd_4578158 < baseStart_4578158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578178 : List Nat := [3, 4, 2, 2, 2, 1, 9]
def baseStart_4578178 : Nat := 118140960795 + 4578178 * 2 ^ 59
def prefixEnd_4578178 : Nat := 4983230072969 + 3 ^ 40 * 4578178 * 2
def baseEnd_4578178 : Nat := 29022294269625852978029

theorem tailTrace_4578178 : CollatzResearch.WordTrace tailWord_4578178 prefixEnd_4578178 29022294269625852978029 := by
  unfold tailWord_4578178
  simp only [CollatzResearch.WordTrace]
  refine ⟨41744967402012617849505797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111319913072033647598682125 41744967402012617849505797)
  ·
    refine ⟨7827181387877365846782337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41744967402012617849505797 7827181387877365846782337)
    ·
      refine ⟨5870386040908024385086753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7827181387877365846782337 5870386040908024385086753)
      ·
        refine ⟨4402789530681018288815065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5870386040908024385086753 4402789530681018288815065)
        ·
          refine ⟨3302092148010763716611299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4402789530681018288815065 3302092148010763716611299)
          ·
            refine ⟨4953138222016145574916949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302092148010763716611299 4953138222016145574916949)
            ·
              refine ⟨29022294269625852978029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4953138222016145574916949 29022294269625852978029)
              ·
                rfl

theorem cell23_4578178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 9].length) (baseStart_4578178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578178 prefixEnd_4578178 := by exact prefixLift 4578178
  have htrace : WordTrace (prefixWord ++ tailWord_4578178) baseStart_4578178 baseEnd_4578178 := by
    simpa [prefixWord, tailWord_4578178, baseEnd_4578178] using wordTrace_append hprefix tailTrace_4578178
  have hstable : (prefixWord ++ tailWord_4578178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578178).length < 2 ^ (prefixWord ++ tailWord_4578178).sum := by decide
  have hdescent : baseEnd_4578178 < baseStart_4578178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578181 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 1, 3, 2]
def baseStart_4578181 : Nat := 118140960795 + 4578181 * 2 ^ 59
def prefixEnd_4578181 : Nat := 4983230072969 + 3 ^ 40 * 4578181 * 2
def baseEnd_4578181 : Nat := 2350807376281657579482835

theorem tailTrace_4578181 : CollatzResearch.WordTrace tailWord_4578181 prefixEnd_4578181 2350807376281657579482835 := by
  unfold tailWord_4578181
  simp only [CollatzResearch.WordTrace]
  refine ⟨166979979027039602910382397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111319986018026401940254931 166979979027039602910382397)
  ·
    refine ⟨62617492135139851091393399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166979979027039602910382397 62617492135139851091393399)
    ·
      refine ⟨93926238202709776637090099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62617492135139851091393399 93926238202709776637090099)
      ·
        refine ⟨140889357304064664955635149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93926238202709776637090099 140889357304064664955635149)
        ·
          refine ⟨52833508989024249358363181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140889357304064664955635149 52833508989024249358363181)
          ·
            refine ⟨19812565870884093509386193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52833508989024249358363181 19812565870884093509386193)
            ·
              refine ⟨14859424403163070132039645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19812565870884093509386193 14859424403163070132039645)
              ·
                refine ⟨5572284151186151299514867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14859424403163070132039645 5572284151186151299514867)
                ·
                  refine ⟨8358426226779226949272301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5572284151186151299514867 8358426226779226949272301)
                  ·
                    refine ⟨3134409835042210105977113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8358426226779226949272301 3134409835042210105977113)
                    ·
                      refine ⟨2350807376281657579482835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3134409835042210105977113 2350807376281657579482835)
                      ·
                        rfl

theorem cell23_4578181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_4578181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578181 prefixEnd_4578181 := by exact prefixLift 4578181
  have htrace : WordTrace (prefixWord ++ tailWord_4578181) baseStart_4578181 baseEnd_4578181 := by
    simpa [prefixWord, tailWord_4578181, baseEnd_4578181] using wordTrace_append hprefix tailTrace_4578181
  have hstable : (prefixWord ++ tailWord_4578181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578181).length < 2 ^ (prefixWord ++ tailWord_4578181).sum := by decide
  have hdescent : baseEnd_4578181 < baseStart_4578181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578215 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_4578215 : Nat := 118140960795 + 4578215 * 2 ^ 59
def prefixEnd_4578215 : Nat := 4983230072969 + 3 ^ 40 * 4578215 * 2
def baseEnd_4578215 : Nat := 2350824834623910446457679

theorem tailTrace_4578215 : CollatzResearch.WordTrace tailWord_4578215 prefixEnd_4578215 2350824834623910446457679 := by
  unfold tailWord_4578215
  simp only [CollatzResearch.WordTrace]
  refine ⟨166981219108916426717120099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111320812739277617811413399 166981219108916426717120099)
  ·
    refine ⟨250471828663374640075680149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166981219108916426717120099 250471828663374640075680149)
    ·
      refine ⟨11740866968595686253547507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 250471828663374640075680149 11740866968595686253547507)
      ·
        refine ⟨17611300452893529380321261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11740866968595686253547507 17611300452893529380321261)
        ·
          refine ⟨6604237669835073517620473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17611300452893529380321261 6604237669835073517620473)
          ·
            refine ⟨4953178252376305138215355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6604237669835073517620473 4953178252376305138215355)
            ·
              refine ⟨7429767378564457707323033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953178252376305138215355 7429767378564457707323033)
              ·
                refine ⟨5572325533923343280492275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7429767378564457707323033 5572325533923343280492275)
                ·
                  refine ⟨8358488300885014920738413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5572325533923343280492275 8358488300885014920738413)
                  ·
                    refine ⟨3134433112831880595276905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8358488300885014920738413 3134433112831880595276905)
                    ·
                      refine ⟨2350824834623910446457679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3134433112831880595276905 2350824834623910446457679)
                      ·
                        rfl

theorem cell23_4578215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_4578215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578215 prefixEnd_4578215 := by exact prefixLift 4578215
  have htrace : WordTrace (prefixWord ++ tailWord_4578215) baseStart_4578215 baseEnd_4578215 := by
    simpa [prefixWord, tailWord_4578215, baseEnd_4578215] using wordTrace_append hprefix tailTrace_4578215
  have hstable : (prefixWord ++ tailWord_4578215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578215).length < 2 ^ (prefixWord ++ tailWord_4578215).sum := by decide
  have hdescent : baseEnd_4578215 < baseStart_4578215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578227 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 3]
def baseStart_4578227 : Nat := 118140960795 + 4578227 * 2 ^ 59
def prefixEnd_4578227 : Nat := 4983230072969 + 3 ^ 40 * 4578227 * 2
def baseEnd_4578227 : Nat := 2350830996391764399507623

theorem tailTrace_4578227 : CollatzResearch.WordTrace tailWord_4578227 prefixEnd_4578227 2350830996391764399507623 := by
  unfold tailWord_4578227
  simp only [CollatzResearch.WordTrace]
  refine ⟨166981656784872952766556935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111321104523248635177704623 166981656784872952766556935)
  ·
    refine ⟨250472485177309429149835403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166981656784872952766556935 250472485177309429149835403)
    ·
      refine ⟨375708727765964143724753105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250472485177309429149835403 375708727765964143724753105)
      ·
        refine ⟨281781545824473107793564829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375708727765964143724753105 281781545824473107793564829)
        ·
          refine ⟨105668079684177415422586811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281781545824473107793564829 105668079684177415422586811)
          ·
            refine ⟨158502119526266123133880217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105668079684177415422586811 158502119526266123133880217)
            ·
              refine ⟨118876589644699592350410163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158502119526266123133880217 118876589644699592350410163)
              ·
                refine ⟨178314884467049388525615245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118876589644699592350410163 178314884467049388525615245)
                ·
                  refine ⟨66868081675143520697105717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178314884467049388525615245 66868081675143520697105717)
                  ·
                    refine ⟨6268882657044705065353661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66868081675143520697105717 6268882657044705065353661)
                    ·
                      refine ⟨2350830996391764399507623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6268882657044705065353661 2350830996391764399507623)
                      ·
                        rfl

theorem cell23_4578227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 3].length) (baseStart_4578227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578227 prefixEnd_4578227 := by exact prefixLift 4578227
  have htrace : WordTrace (prefixWord ++ tailWord_4578227) baseStart_4578227 baseEnd_4578227 := by
    simpa [prefixWord, tailWord_4578227, baseEnd_4578227] using wordTrace_append hprefix tailTrace_4578227
  have hstable : (prefixWord ++ tailWord_4578227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578227).length < 2 ^ (prefixWord ++ tailWord_4578227).sum := by decide
  have hdescent : baseEnd_4578227 < baseStart_4578227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578228 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_4578228 : Nat := 118140960795 + 4578228 * 2 ^ 59
def prefixEnd_4578228 : Nat := 4983230072969 + 3 ^ 40 * 4578228 * 2
def baseEnd_4578228 : Nat := 2350831509872418895595119

theorem tailTrace_4578228 : CollatzResearch.WordTrace tailWord_4578228 prefixEnd_4578228 2350831509872418895595119 := by
  unfold tailWord_4578228
  simp only [CollatzResearch.WordTrace]
  refine ⟨83490846628934664968671669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111321128838579553291562225 83490846628934664968671669)
  ·
    refine ⟨7827266871462624840812969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83490846628934664968671669 7827266871462624840812969)
    ·
      refine ⟨5870450153596968630609727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7827266871462624840812969 5870450153596968630609727)
      ·
        refine ⟨8805675230395452945914591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5870450153596968630609727 8805675230395452945914591)
        ·
          refine ⟨13208512845593179418871887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8805675230395452945914591 13208512845593179418871887)
          ·
            refine ⟨19812769268389769128307831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13208512845593179418871887 19812769268389769128307831)
            ·
              refine ⟨29719153902584653692461747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19812769268389769128307831 29719153902584653692461747)
              ·
                refine ⟨44578730853876980538692621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29719153902584653692461747 44578730853876980538692621)
                ·
                  refine ⟨16717024070203867702009733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44578730853876980538692621 16717024070203867702009733)
                  ·
                    refine ⟨3134442013163225194126825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16717024070203867702009733 3134442013163225194126825)
                    ·
                      refine ⟨2350831509872418895595119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3134442013163225194126825 2350831509872418895595119)
                      ·
                        rfl

theorem cell23_4578228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_4578228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578228 prefixEnd_4578228 := by exact prefixLift 4578228
  have htrace : WordTrace (prefixWord ++ tailWord_4578228) baseStart_4578228 baseEnd_4578228 := by
    simpa [prefixWord, tailWord_4578228, baseEnd_4578228] using wordTrace_append hprefix tailTrace_4578228
  have hstable : (prefixWord ++ tailWord_4578228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578228).length < 2 ^ (prefixWord ++ tailWord_4578228).sum := by decide
  have hdescent : baseEnd_4578228 < baseStart_4578228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578234 : List Nat := [3, 1, 1, 1, 2, 1, 4, 5, 5]
def baseStart_4578234 : Nat := 118140960795 + 4578234 * 2 ^ 59
def prefixEnd_4578234 : Nat := 4983230072969 + 3 ^ 40 * 4578234 * 2
def baseEnd_4578234 : Nat := 261203843417371763568899

theorem tailTrace_4578234 : CollatzResearch.WordTrace tailWord_4578234 prefixEnd_4578234 261203843417371763568899 := by
  unfold tailWord_4578234
  simp only [CollatzResearch.WordTrace]
  refine ⟨41745478023961898240515439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111321274730565061974707837 41745478023961898240515439)
  ·
    refine ⟨62618217035942847360773159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41745478023961898240515439 62618217035942847360773159)
    ·
      refine ⟨93927325553914271041159739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62618217035942847360773159 93927325553914271041159739)
      ·
        refine ⟨140890988330871406561739609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93927325553914271041159739 140890988330871406561739609)
        ·
          refine ⟨105668241248153554921304707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140890988330871406561739609 105668241248153554921304707)
          ·
            refine ⟨158502361872230332381957061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105668241248153554921304707 158502361872230332381957061)
            ·
              refine ⟨29719192851043187321616949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158502361872230332381957061 29719192851043187321616949)
              ·
                refine ⟨2786174329785298811401589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29719192851043187321616949 2786174329785298811401589)
                ·
                  refine ⟨261203843417371763568899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2786174329785298811401589 261203843417371763568899)
                  ·
                    rfl

theorem cell23_4578234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_4578234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578234 prefixEnd_4578234 := by exact prefixLift 4578234
  have htrace : WordTrace (prefixWord ++ tailWord_4578234) baseStart_4578234 baseEnd_4578234 := by
    simpa [prefixWord, tailWord_4578234, baseEnd_4578234] using wordTrace_append hprefix tailTrace_4578234
  have hstable : (prefixWord ++ tailWord_4578234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578234).length < 2 ^ (prefixWord ++ tailWord_4578234).sum := by decide
  have hdescent : baseEnd_4578234 < baseStart_4578234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578251 : List Nat := [1, 1, 1, 1, 3, 5, 4, 2, 5]
def baseStart_4578251 : Nat := 118140960795 + 4578251 * 2 ^ 59
def prefixEnd_4578251 : Nat := 4983230072969 + 3 ^ 40 * 4578251 * 2
def baseEnd_4578251 : Nat := 261204813325274700623057

theorem tailTrace_4578251 : CollatzResearch.WordTrace tailWord_4578251 prefixEnd_4578251 261204813325274700623057 := by
  unfold tailWord_4578251
  simp only [CollatzResearch.WordTrace]
  refine ⟨166982532136786004865430607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111321688091190669910287071 166982532136786004865430607)
  ·
    refine ⟨250473798205179007298145911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166982532136786004865430607 250473798205179007298145911)
    ·
      refine ⟨375710697307768510947218867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250473798205179007298145911 375710697307768510947218867)
      ·
        refine ⟨563566045961652766420828301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375710697307768510947218867 563566045961652766420828301)
        ·
          refine ⟨211337267235619787407810613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 563566045961652766420828301 211337267235619787407810613)
          ·
            refine ⟨19812868803339355069482245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211337267235619787407810613 19812868803339355069482245)
            ·
              refine ⟨3714912900626129075527921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19812868803339355069482245 3714912900626129075527921)
              ·
                refine ⟨2786184675469596806645941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3714912900626129075527921 2786184675469596806645941)
                ·
                  refine ⟨261204813325274700623057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2786184675469596806645941 261204813325274700623057)
                  ·
                    rfl

theorem cell23_4578251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 5].length) (baseStart_4578251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578251 prefixEnd_4578251 := by exact prefixLift 4578251
  have htrace : WordTrace (prefixWord ++ tailWord_4578251) baseStart_4578251 baseEnd_4578251 := by
    simpa [prefixWord, tailWord_4578251, baseEnd_4578251] using wordTrace_append hprefix tailTrace_4578251
  have hstable : (prefixWord ++ tailWord_4578251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578251).length < 2 ^ (prefixWord ++ tailWord_4578251).sum := by decide
  have hdescent : baseEnd_4578251 < baseStart_4578251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578257 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_4578257 : Nat := 118140960795 + 4578257 * 2 ^ 59
def prefixEnd_4578257 : Nat := 4983230072969 + 3 ^ 40 * 4578257 * 2
def baseEnd_4578257 : Nat := 2350846400811399282132485

theorem tailTrace_4578257 : CollatzResearch.WordTrace tailWord_4578257 prefixEnd_4578257 2350846400811399282132485 := by
  unfold tailWord_4578257
  simp only [CollatzResearch.WordTrace]
  refine ⟨166982750974764267890149025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111321833983176178593432683 166982750974764267890149025)
  ·
    refine ⟨125237063231073200917611769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166982750974764267890149025 125237063231073200917611769)
    ·
      refine ⟨93927797423304900688208827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125237063231073200917611769 93927797423304900688208827)
      ·
        refine ⟨140891696134957351032313241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93927797423304900688208827 140891696134957351032313241)
        ·
          refine ⟨105668772101218013274234931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140891696134957351032313241 105668772101218013274234931)
          ·
            refine ⟨158503158151827019911352397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105668772101218013274234931 158503158151827019911352397)
            ·
              refine ⟨59438684306935132466757149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158503158151827019911352397 59438684306935132466757149)
              ·
                refine ⟨22289506615100674675033931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59438684306935132466757149 22289506615100674675033931)
                ·
                  refine ⟨33434259922651012012550897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22289506615100674675033931 33434259922651012012550897)
                  ·
                    refine ⟨25075694941988259009413173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33434259922651012012550897 25075694941988259009413173)
                    ·
                      refine ⟨2350846400811399282132485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25075694941988259009413173 2350846400811399282132485)
                      ·
                        rfl

theorem cell23_4578257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_4578257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578257 prefixEnd_4578257 := by exact prefixLift 4578257
  have htrace : WordTrace (prefixWord ++ tailWord_4578257) baseStart_4578257 baseEnd_4578257 := by
    simpa [prefixWord, tailWord_4578257, baseEnd_4578257] using wordTrace_append hprefix tailTrace_4578257
  have hstable : (prefixWord ++ tailWord_4578257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578257).length < 2 ^ (prefixWord ++ tailWord_4578257).sum := by decide
  have hdescent : baseEnd_4578257 < baseStart_4578257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578261 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_4578261 : Nat := 118140960795 + 4578261 * 2 ^ 59
def prefixEnd_4578261 : Nat := 4983230072969 + 3 ^ 40 * 4578261 * 2
def baseEnd_4578261 : Nat := 2350848454734017266482467

theorem tailTrace_4578261 : CollatzResearch.WordTrace tailWord_4578261 prefixEnd_4578261 2350848454734017266482467 := by
  unfold tailWord_4578261
  simp only [CollatzResearch.WordTrace]
  refine ⟨166982896866749776573294637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111321931244499851048863091 166982896866749776573294637)
  ·
    refine ⟨62618586325031166214985489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166982896866749776573294637 62618586325031166214985489)
    ·
      refine ⟨46963939743773374661239117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62618586325031166214985489 46963939743773374661239117)
      ·
        refine ⟨17611477403915015497964669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46963939743773374661239117 17611477403915015497964669)
        ·
          refine ⟨6604304026468130811736751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17611477403915015497964669 6604304026468130811736751)
          ·
            refine ⟨9906456039702196217605127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6604304026468130811736751 9906456039702196217605127)
            ·
              refine ⟨14859684059553294326407691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9906456039702196217605127 14859684059553294326407691)
              ·
                refine ⟨22289526089329941489611537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14859684059553294326407691 22289526089329941489611537)
                ·
                  refine ⟨16717144566997456117208653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22289526089329941489611537 16717144566997456117208653)
                  ·
                    refine ⟨6268929212624046043953245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16717144566997456117208653 6268929212624046043953245)
                    ·
                      refine ⟨2350848454734017266482467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6268929212624046043953245 2350848454734017266482467)
                      ·
                        rfl

theorem cell23_4578261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_4578261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578261 prefixEnd_4578261 := by exact prefixLift 4578261
  have htrace : WordTrace (prefixWord ++ tailWord_4578261) baseStart_4578261 baseEnd_4578261 := by
    simpa [prefixWord, tailWord_4578261, baseEnd_4578261] using wordTrace_append hprefix tailTrace_4578261
  have hstable : (prefixWord ++ tailWord_4578261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578261).length < 2 ^ (prefixWord ++ tailWord_4578261).sum := by decide
  have hdescent : baseEnd_4578261 < baseStart_4578261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578297 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_4578297 : Nat := 118140960795 + 4578297 * 2 ^ 59
def prefixEnd_4578297 : Nat := 4983230072969 + 3 ^ 40 * 4578297 * 2
def baseEnd_4578297 : Nat := 2350866940037579125632301

theorem tailTrace_4578297 : CollatzResearch.WordTrace tailWord_4578297 prefixEnd_4578297 2350866940037579125632301 := by
  unfold tailWord_4578297
  simp only [CollatzResearch.WordTrace]
  refine ⟨166984209894619354721605145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111322806596412903147736763 166984209894619354721605145)
  ·
    refine ⟨125238157420964516041203859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166984209894619354721605145 125238157420964516041203859)
    ·
      refine ⟨187857236131446774061805789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125238157420964516041203859 187857236131446774061805789)
      ·
        refine ⟨70446463549292540273177171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187857236131446774061805789 70446463549292540273177171)
        ·
          refine ⟨105669695323938810409765757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70446463549292540273177171 105669695323938810409765757)
          ·
            refine ⟨39626135746477053903662159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105669695323938810409765757 39626135746477053903662159)
            ·
              refine ⟨59439203619715580855493239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39626135746477053903662159 59439203619715580855493239)
              ·
                refine ⟨89158805429573371283239859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59439203619715580855493239 89158805429573371283239859)
                ·
                  refine ⟨133738208144360056924859789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89158805429573371283239859 133738208144360056924859789)
                  ·
                    refine ⟨50151828054135021346822421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133738208144360056924859789 50151828054135021346822421)
                    ·
                      refine ⟨2350866940037579125632301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50151828054135021346822421 2350866940037579125632301)
                      ·
                        rfl

theorem cell23_4578297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_4578297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578297 prefixEnd_4578297 := by exact prefixLift 4578297
  have htrace : WordTrace (prefixWord ++ tailWord_4578297) baseStart_4578297 baseEnd_4578297 := by
    simpa [prefixWord, tailWord_4578297, baseEnd_4578297] using wordTrace_append hprefix tailTrace_4578297
  have hstable : (prefixWord ++ tailWord_4578297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578297).length < 2 ^ (prefixWord ++ tailWord_4578297).sum := by decide
  have hdescent : baseEnd_4578297 < baseStart_4578297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578311 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 3, 4]
def baseStart_4578311 : Nat := 118140960795 + 4578311 * 2 ^ 59
def prefixEnd_4578311 : Nat := 4983230072969 + 3 ^ 40 * 4578311 * 2
def baseEnd_4578311 : Nat := 783624709588914023619079

theorem tailTrace_4578311 : CollatzResearch.WordTrace tailWord_4578311 prefixEnd_4578311 783624709588914023619079 := by
  unfold tailWord_4578311
  simp only [CollatzResearch.WordTrace]
  refine ⟨166984720516568635112614787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111323147011045756741743191 166984720516568635112614787)
  ·
    refine ⟨250477080774852952668922181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166984720516568635112614787 250477080774852952668922181)
    ·
      refine ⟨46964452645284928625422909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250477080774852952668922181 46964452645284928625422909)
      ·
        refine ⟨17611669741981848234533591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46964452645284928625422909 17611669741981848234533591)
        ·
          refine ⟨26417504612972772351800387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17611669741981848234533591 26417504612972772351800387)
          ·
            refine ⟨39626256919459158527700581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26417504612972772351800387 39626256919459158527700581)
            ·
              refine ⟨7429923172398592223943859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39626256919459158527700581 7429923172398592223943859)
              ·
                refine ⟨11144884758597888335915789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7429923172398592223943859 11144884758597888335915789)
                ·
                  refine ⟨4179331784474208125968421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11144884758597888335915789 4179331784474208125968421)
                  ·
                    refine ⟨783624709588914023619079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4179331784474208125968421 783624709588914023619079)
                    ·
                      rfl

theorem cell23_4578311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_4578311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578311 prefixEnd_4578311 := by exact prefixLift 4578311
  have htrace : WordTrace (prefixWord ++ tailWord_4578311) baseStart_4578311 baseEnd_4578311 := by
    simpa [prefixWord, tailWord_4578311, baseEnd_4578311] using wordTrace_append hprefix tailTrace_4578311
  have hstable : (prefixWord ++ tailWord_4578311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578311).length < 2 ^ (prefixWord ++ tailWord_4578311).sum := by decide
  have hdescent : baseEnd_4578311 < baseStart_4578311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578414 : List Nat := [4, 1, 2, 2, 1, 13]
def baseStart_4578414 : Nat := 118140960795 + 4578414 * 2 ^ 59
def prefixEnd_4578414 : Nat := 4983230072969 + 3 ^ 40 * 4578414 * 2
def baseEnd_4578414 : Nat := 9674596778905988345141

theorem tailTrace_4578414 : CollatzResearch.WordTrace tailWord_4578414 prefixEnd_4578414 9674596778905988345141 := by
  unfold tailWord_4578414
  simp only [CollatzResearch.WordTrace]
  refine ⟨20873559654399435462951787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111325651490130322469076197 20873559654399435462951787)
  ·
    refine ⟨31310339481599153194427681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20873559654399435462951787 31310339481599153194427681)
    ·
      refine ⟨23482754611199364895820761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31310339481599153194427681 23482754611199364895820761)
      ·
        refine ⟨17612065958399523671865571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23482754611199364895820761 17612065958399523671865571)
        ·
          refine ⟨26418098937599285507798357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17612065958399523671865571 26418098937599285507798357)
          ·
            refine ⟨9674596778905988345141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 26418098937599285507798357 9674596778905988345141)
            ·
              rfl

theorem cell23_4578414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 13].length) (baseStart_4578414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578414 prefixEnd_4578414 := by exact prefixLift 4578414
  have htrace : WordTrace (prefixWord ++ tailWord_4578414) baseStart_4578414 baseEnd_4578414 := by
    simpa [prefixWord, tailWord_4578414, baseEnd_4578414] using wordTrace_append hprefix tailTrace_4578414
  have hstable : (prefixWord ++ tailWord_4578414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578414).length < 2 ^ (prefixWord ++ tailWord_4578414).sum := by decide
  have hdescent : baseEnd_4578414 < baseStart_4578414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578418 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_4578418 : Nat := 118140960795 + 4578418 * 2 ^ 59
def prefixEnd_4578418 : Nat := 4983230072969 + 3 ^ 40 * 4578418 * 2
def baseEnd_4578418 : Nat := 783643023732257717406415

theorem tailTrace_4578418 : CollatzResearch.WordTrace tailWord_4578418 prefixEnd_4578418 783643023732257717406415 := by
  unfold tailWord_4578418
  simp only [CollatzResearch.WordTrace]
  refine ⟨41747155781795248096689977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111325748751453994924506605 41747155781795248096689977)
  ·
    refine ⟨31310366836346436072517483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41747155781795248096689977 31310366836346436072517483)
    ·
      refine ⟨46965550254519654108776225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31310366836346436072517483 46965550254519654108776225)
      ·
        refine ⟨35224162690889740581582169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46965550254519654108776225 35224162690889740581582169)
        ·
          refine ⟨26418122018167305436186627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35224162690889740581582169 26418122018167305436186627)
          ·
            refine ⟨39627183027250958154279941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26418122018167305436186627 39627183027250958154279941)
            ·
              refine ⟨7430096817609554653927489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39627183027250958154279941 7430096817609554653927489)
              ·
                refine ⟨5572572613207165990445617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7430096817609554653927489 5572572613207165990445617)
                ·
                  refine ⟨4179429459905374492834213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5572572613207165990445617 4179429459905374492834213)
                  ·
                    refine ⟨783643023732257717406415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4179429459905374492834213 783643023732257717406415)
                    ·
                      rfl

theorem cell23_4578418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_4578418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578418 prefixEnd_4578418 := by exact prefixLift 4578418
  have htrace : WordTrace (prefixWord ++ tailWord_4578418) baseStart_4578418 baseEnd_4578418 := by
    simpa [prefixWord, tailWord_4578418, baseEnd_4578418] using wordTrace_append hprefix tailTrace_4578418
  have hstable : (prefixWord ++ tailWord_4578418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578418).length < 2 ^ (prefixWord ++ tailWord_4578418).sum := by decide
  have hdescent : baseEnd_4578418 < baseStart_4578418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578441 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 1, 3, 3]
def baseStart_4578441 : Nat := 118140960795 + 4578441 * 2 ^ 59
def prefixEnd_4578441 : Nat := 4983230072969 + 3 ^ 40 * 4578441 * 2
def baseEnd_4578441 : Nat := 2350940881251826562231639

theorem tailTrace_4578441 : CollatzResearch.WordTrace tailWord_4578441 prefixEnd_4578441 2350940881251826562231639 := by
  unfold tailWord_4578441
  simp only [CollatzResearch.WordTrace]
  refine ⟨166989462006097667314847177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111326308004065111543231451 166989462006097667314847177)
  ·
    refine ⟨125242096504573250486135383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166989462006097667314847177 125242096504573250486135383)
    ·
      refine ⟨187863144756859875729203075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125242096504573250486135383 187863144756859875729203075)
      ·
        refine ⟨281794717135289813593804613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187863144756859875729203075 281794717135289813593804613)
        ·
          refine ⟨52836509462866840048838365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 281794717135289813593804613 52836509462866840048838365)
          ·
            refine ⟨19813691048575065018314387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52836509462866840048838365 19813691048575065018314387)
            ·
              refine ⟨29720536572862597527471581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19813691048575065018314387 29720536572862597527471581)
              ·
                refine ⟨11145201214823474072801843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29720536572862597527471581 11145201214823474072801843)
                ·
                  refine ⟨16717801822235211109202765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11145201214823474072801843 16717801822235211109202765)
                  ·
                    refine ⟨6269175683338204165951037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16717801822235211109202765 6269175683338204165951037)
                    ·
                      refine ⟨2350940881251826562231639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269175683338204165951037 2350940881251826562231639)
                      ·
                        rfl

theorem cell23_4578441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3, 3].length) (baseStart_4578441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578441 prefixEnd_4578441 := by exact prefixLift 4578441
  have htrace : WordTrace (prefixWord ++ tailWord_4578441) baseStart_4578441 baseEnd_4578441 := by
    simpa [prefixWord, tailWord_4578441, baseEnd_4578441] using wordTrace_append hprefix tailTrace_4578441
  have hstable : (prefixWord ++ tailWord_4578441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578441).length < 2 ^ (prefixWord ++ tailWord_4578441).sum := by decide
  have hdescent : baseEnd_4578441 < baseStart_4578441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578458 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4578458 : Nat := 118140960795 + 4578458 * 2 ^ 59
def prefixEnd_4578458 : Nat := 4983230072969 + 3 ^ 40 * 4578458 * 2
def baseEnd_4578458 : Nat := 2350949610422952995719061

theorem tailTrace_4578458 : CollatzResearch.WordTrace tailWord_4578458 prefixEnd_4578458 2350949610422952995719061 := by
  unfold tailWord_4578458
  simp only [CollatzResearch.WordTrace]
  refine ⟨41747520511759019804554007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111326721364690719478810685 41747520511759019804554007)
  ·
    refine ⟨62621280767638529706831011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41747520511759019804554007 62621280767638529706831011)
    ·
      refine ⟨93931921151457794560246517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62621280767638529706831011 93931921151457794560246517)
      ·
        refine ⟨8806117607949168240023111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93931921151457794560246517 8806117607949168240023111)
        ·
          refine ⟨13209176411923752360034667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8806117607949168240023111 13209176411923752360034667)
          ·
            refine ⟨19813764617885628540052001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13209176411923752360034667 19813764617885628540052001)
            ·
              refine ⟨14860323463414221405039001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19813764617885628540052001 14860323463414221405039001)
              ·
                refine ⟨11145242597560666053779251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14860323463414221405039001 11145242597560666053779251)
                ·
                  refine ⟨16717863896340999080668877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11145242597560666053779251 16717863896340999080668877)
                  ·
                    refine ⟨6269198961127874655250829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16717863896340999080668877 6269198961127874655250829)
                    ·
                      refine ⟨2350949610422952995719061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269198961127874655250829 2350949610422952995719061)
                      ·
                        rfl

theorem cell23_4578458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4578458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578458 prefixEnd_4578458 := by exact prefixLift 4578458
  have htrace : WordTrace (prefixWord ++ tailWord_4578458) baseStart_4578458 baseEnd_4578458 := by
    simpa [prefixWord, tailWord_4578458, baseEnd_4578458] using wordTrace_append hprefix tailTrace_4578458
  have hstable : (prefixWord ++ tailWord_4578458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578458).length < 2 ^ (prefixWord ++ tailWord_4578458).sum := by decide
  have hdescent : baseEnd_4578458 < baseStart_4578458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578462 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_4578462 : Nat := 118140960795 + 4578462 * 2 ^ 59
def prefixEnd_4578462 : Nat := 4983230072969 + 3 ^ 40 * 4578462 * 2
def baseEnd_4578462 : Nat := 2350951664345570980069043

theorem tailTrace_4578462 : CollatzResearch.WordTrace tailWord_4578462 prefixEnd_4578462 2350951664345570980069043 := by
  unfold tailWord_4578462
  simp only [CollatzResearch.WordTrace]
  refine ⟨20873778492377698487670205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111326818626014391934241093 20873778492377698487670205)
  ·
    refine ⟨7827666934641636932876327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20873778492377698487670205 7827666934641636932876327)
    ·
      refine ⟨11741500401962455399314491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7827666934641636932876327 11741500401962455399314491)
      ·
        refine ⟨17612250602943683098971737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11741500401962455399314491 17612250602943683098971737)
        ·
          refine ⟨13209187952207762324228803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17612250602943683098971737 13209187952207762324228803)
          ·
            refine ⟨19813781928311643486343205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13209187952207762324228803 19813781928311643486343205)
            ·
              refine ⟨3715084111558433153689351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19813781928311643486343205 3715084111558433153689351)
              ·
                refine ⟨5572626167337649730534027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715084111558433153689351 5572626167337649730534027)
                ·
                  refine ⟨8358939251006474595801041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5572626167337649730534027 8358939251006474595801041)
                  ·
                    refine ⟨6269204438254855946850781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8358939251006474595801041 6269204438254855946850781)
                    ·
                      refine ⟨2350951664345570980069043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269204438254855946850781 2350951664345570980069043)
                      ·
                        rfl

theorem cell23_4578462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_4578462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578462 prefixEnd_4578462 := by exact prefixLift 4578462
  have htrace : WordTrace (prefixWord ++ tailWord_4578462) baseStart_4578462 baseEnd_4578462 := by
    simpa [prefixWord, tailWord_4578462, baseEnd_4578462] using wordTrace_append hprefix tailTrace_4578462
  have hstable : (prefixWord ++ tailWord_4578462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578462).length < 2 ^ (prefixWord ++ tailWord_4578462).sum := by decide
  have hdescent : baseEnd_4578462 < baseStart_4578462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578492 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 2, 1, 3]
def baseStart_4578492 : Nat := 118140960795 + 4578492 * 2 ^ 59
def prefixEnd_4578492 : Nat := 4983230072969 + 3 ^ 40 * 4578492 * 2
def baseEnd_4578492 : Nat := 2350967068765205862693905

theorem tailTrace_4578492 : CollatzResearch.WordTrace tailWord_4578492 prefixEnd_4578492 2350967068765205862693905 := by
  unfold tailWord_4578492
  simp only [CollatzResearch.WordTrace]
  refine ⟨83495661064456451512476865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111327548085941935349969153 83495661064456451512476865)
  ·
    refine ⟨62621745798342338634357649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83495661064456451512476865 62621745798342338634357649)
    ·
      refine ⟨46966309348756753975768237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62621745798342338634357649 46966309348756753975768237)
      ·
        refine ⟨17612366005783782740913089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46966309348756753975768237 17612366005783782740913089)
        ·
          refine ⟨13209274504337837055684817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17612366005783782740913089 13209274504337837055684817)
          ·
            refine ⟨9906955878253377791763613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13209274504337837055684817 9906955878253377791763613)
            ·
              refine ⟨3715108454345016671911355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9906955878253377791763613 3715108454345016671911355)
              ·
                refine ⟨5572662681517525007867033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715108454345016671911355 5572662681517525007867033)
                ·
                  refine ⟨4179497011138143755900275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5572662681517525007867033 4179497011138143755900275)
                  ·
                    refine ⟨6269245516707215633850413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4179497011138143755900275 6269245516707215633850413)
                    ·
                      refine ⟨2350967068765205862693905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269245516707215633850413 2350967068765205862693905)
                      ·
                        rfl

theorem cell23_4578492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_4578492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578492 prefixEnd_4578492 := by exact prefixLift 4578492
  have htrace : WordTrace (prefixWord ++ tailWord_4578492) baseStart_4578492 baseEnd_4578492 := by
    simpa [prefixWord, tailWord_4578492, baseEnd_4578492] using wordTrace_append hprefix tailTrace_4578492
  have hstable : (prefixWord ++ tailWord_4578492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578492).length < 2 ^ (prefixWord ++ tailWord_4578492).sum := by decide
  have hdescent : baseEnd_4578492 < baseStart_4578492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578538 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 7]
def baseStart_4578538 : Nat := 118140960795 + 4578538 * 2 ^ 59
def prefixEnd_4578538 : Nat := 4983230072969 + 3 ^ 40 * 4578538 * 2
def baseEnd_4578538 : Nat := 261221187652812520302077

theorem tailTrace_4578538 : CollatzResearch.WordTrace tailWord_4578538 prefixEnd_4578538 261221187652812520302077 := by
  unfold tailWord_4578538
  simp only [CollatzResearch.WordTrace]
  refine ⟨41748249971686563220282067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111328666591164168587418845 41748249971686563220282067)
  ·
    refine ⟨62622374957529844830423101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41748249971686563220282067 62622374957529844830423101)
    ·
      refine ⟨23483390609073691811408663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62622374957529844830423101 23483390609073691811408663)
      ·
        refine ⟨35225085913610537717112995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23483390609073691811408663 35225085913610537717112995)
        ·
          refine ⟨52837628870415806575669493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35225085913610537717112995 52837628870415806575669493)
          ·
            refine ⟨4953527706601481866469015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52837628870415806575669493 4953527706601481866469015)
            ·
              refine ⟨7430291559902222799703523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953527706601481866469015 7430291559902222799703523)
              ·
                refine ⟨11145437339853334199555285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7430291559902222799703523 11145437339853334199555285)
                ·
                  refine ⟨261221187652812520302077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11145437339853334199555285 261221187652812520302077)
                  ·
                    rfl

theorem cell23_4578538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_4578538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578538 prefixEnd_4578538 := by exact prefixLift 4578538
  have htrace : WordTrace (prefixWord ++ tailWord_4578538) baseStart_4578538 baseEnd_4578538 := by
    simpa [prefixWord, tailWord_4578538, baseEnd_4578538] using wordTrace_append hprefix tailTrace_4578538
  have hstable : (prefixWord ++ tailWord_4578538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578538).length < 2 ^ (prefixWord ++ tailWord_4578538).sum := by decide
  have hdescent : baseEnd_4578538 < baseStart_4578538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578588 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_4578588 : Nat := 118140960795 + 4578588 * 2 ^ 59
def prefixEnd_4578588 : Nat := 4983230072969 + 3 ^ 40 * 4578588 * 2
def baseEnd_4578588 : Nat := 2351016362908037487093463

theorem tailTrace_4578588 : CollatzResearch.WordTrace tailWord_4578588 prefixEnd_4578588 2351016362908037487093463 := by
  unfold tailWord_4578588
  simp only [CollatzResearch.WordTrace]
  refine ⟨83497411768282555710224209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111329882357710074280298945 83497411768282555710224209)
  ·
    refine ⟨62623058826211916782668157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83497411768282555710224209 62623058826211916782668157)
    ·
      refine ⟨23483647059829468793500559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62623058826211916782668157 23483647059829468793500559)
      ·
        refine ⟨35225470589744203190250839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23483647059829468793500559 35225470589744203190250839)
        ·
          refine ⟨52838205884616304785376259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35225470589744203190250839 52838205884616304785376259)
          ·
            refine ⟨79257308826924457178064389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52838205884616304785376259 79257308826924457178064389)
            ·
              refine ⟨14860745405048335720887073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79257308826924457178064389 14860745405048335720887073)
              ·
                refine ⟨11145559053786251790665305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14860745405048335720887073 11145559053786251790665305)
                ·
                  refine ⟨8359169290339688842998979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11145559053786251790665305 8359169290339688842998979)
                  ·
                    refine ⟨12538753935509533264498469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8359169290339688842998979 12538753935509533264498469)
                    ·
                      refine ⟨2351016362908037487093463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12538753935509533264498469 2351016362908037487093463)
                      ·
                        rfl

theorem cell23_4578588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_4578588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578588 prefixEnd_4578588 := by exact prefixLift 4578588
  have htrace : WordTrace (prefixWord ++ tailWord_4578588) baseStart_4578588 baseEnd_4578588 := by
    simpa [prefixWord, tailWord_4578588, baseEnd_4578588] using wordTrace_append hprefix tailTrace_4578588
  have hstable : (prefixWord ++ tailWord_4578588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578588).length < 2 ^ (prefixWord ++ tailWord_4578588).sum := by decide
  have hdescent : baseEnd_4578588 < baseStart_4578588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578625 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4578625 : Nat := 118140960795 + 4578625 * 2 ^ 59
def prefixEnd_4578625 : Nat := 4983230072969 + 3 ^ 40 * 4578625 * 2
def baseEnd_4578625 : Nat := 2351035361692253842330793

theorem tailTrace_4578625 : CollatzResearch.WordTrace tailWord_4578625 prefixEnd_4578625 2351035361692253842330793 := by
  unfold tailWord_4578625
  simp only [CollatzResearch.WordTrace]
  refine ⟨166996173037431066739545329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111330782024954044493030219 166996173037431066739545329)
  ·
    refine ⟨125247129778073300054658997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166996173037431066739545329 125247129778073300054658997)
    ·
      refine ⟨11741918416694371880124281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125247129778073300054658997 11741918416694371880124281)
      ·
        refine ⟨8806438812520778910093211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11741918416694371880124281 8806438812520778910093211)
        ·
          refine ⟨13209658218781168365139817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8806438812520778910093211 13209658218781168365139817)
          ·
            refine ⟨9907243664085876273854863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13209658218781168365139817 9907243664085876273854863)
            ·
              refine ⟨14860865496128814410782295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9907243664085876273854863 14860865496128814410782295)
              ·
                refine ⟨22291298244193221616173443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14860865496128814410782295 22291298244193221616173443)
                ·
                  refine ⟨33436947366289832424260165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22291298244193221616173443 33436947366289832424260165)
                  ·
                    refine ⟨6269427631179343579548781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33436947366289832424260165 6269427631179343579548781)
                    ·
                      refine ⟨2351035361692253842330793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269427631179343579548781 2351035361692253842330793)
                      ·
                        rfl

theorem cell23_4578625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4578625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578625 prefixEnd_4578625 := by exact prefixLift 4578625
  have htrace : WordTrace (prefixWord ++ tailWord_4578625) baseStart_4578625 baseEnd_4578625 := by
    simpa [prefixWord, tailWord_4578625, baseEnd_4578625] using wordTrace_append hprefix tailTrace_4578625
  have hstable : (prefixWord ++ tailWord_4578625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578625).length < 2 ^ (prefixWord ++ tailWord_4578625).sum := by decide
  have hdescent : baseEnd_4578625 < baseStart_4578625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578645 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 6]
def baseStart_4578645 : Nat := 118140960795 + 4578645 * 2 ^ 59
def prefixEnd_4578645 : Nat := 4983230072969 + 3 ^ 40 * 4578645 * 2
def baseEnd_4578645 : Nat := 261227292367260418231189

theorem tailTrace_4578645 : CollatzResearch.WordTrace tailWord_4578645 prefixEnd_4578645 261227292367260418231189 := by
  unfold tailWord_4578645
  simp only [CollatzResearch.WordTrace]
  refine ⟨166996902497358610155273389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111331268331572406770182259 166996902497358610155273389)
  ·
    refine ⟨62623838436509478808227521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166996902497358610155273389 62623838436509478808227521)
    ·
      refine ⟨46967878827382109106170641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62623838436509478808227521 46967878827382109106170641)
      ·
        refine ⟨35225909120536581829627981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46967878827382109106170641 35225909120536581829627981)
        ·
          refine ⟨13209715920201218186110493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35225909120536581829627981 13209715920201218186110493)
          ·
            refine ⟨4953643470075456819791435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13209715920201218186110493 4953643470075456819791435)
            ·
              refine ⟨7430465205113185229687153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953643470075456819791435 7430465205113185229687153)
              ·
                refine ⟨5572848903834888922265365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7430465205113185229687153 5572848903834888922265365)
                ·
                  refine ⟨261227292367260418231189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5572848903834888922265365 261227292367260418231189)
                  ·
                    rfl

theorem cell23_4578645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_4578645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578645 prefixEnd_4578645 := by exact prefixLift 4578645
  have htrace : WordTrace (prefixWord ++ tailWord_4578645) baseStart_4578645 baseEnd_4578645 := by
    simpa [prefixWord, tailWord_4578645, baseEnd_4578645] using wordTrace_append hprefix tailTrace_4578645
  have hstable : (prefixWord ++ tailWord_4578645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578645).length < 2 ^ (prefixWord ++ tailWord_4578645).sum := by decide
  have hdescent : baseEnd_4578645 < baseStart_4578645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578695 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_4578695 : Nat := 118140960795 + 4578695 * 2 ^ 59
def prefixEnd_4578695 : Nat := 4983230072969 + 3 ^ 40 * 4578695 * 2
def baseEnd_4578695 : Nat := 2351071305338068568455471

theorem tailTrace_4578695 : CollatzResearch.WordTrace tailWord_4578695 prefixEnd_4578695 2351071305338068568455471 := by
  unfold tailWord_4578695
  simp only [CollatzResearch.WordTrace]
  refine ⟨166998726147177468694593539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111332484098118312463062359 166998726147177468694593539)
  ·
    refine ⟨250498089220766203041890309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166998726147177468694593539 250498089220766203041890309)
    ·
      refine ⟨46968391728893663070354433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250498089220766203041890309 46968391728893663070354433)
      ·
        refine ⟨35226293796670247302765825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46968391728893663070354433 35226293796670247302765825)
        ·
          refine ⟨26419720347502685477074369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35226293796670247302765825 26419720347502685477074369)
          ·
            refine ⟨19814790260627014107805777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26419720347502685477074369 19814790260627014107805777)
            ·
              refine ⟨14861092695470260580854333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19814790260627014107805777 14861092695470260580854333)
              ·
                refine ⟨5572909760801347717820375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14861092695470260580854333 5572909760801347717820375)
                ·
                  refine ⟨8359364641202021576730563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5572909760801347717820375 8359364641202021576730563)
                  ·
                    refine ⟨12539046961803032365095845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8359364641202021576730563 12539046961803032365095845)
                    ·
                      refine ⟨2351071305338068568455471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12539046961803032365095845 2351071305338068568455471)
                      ·
                        rfl

theorem cell23_4578695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_4578695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578695 prefixEnd_4578695 := by exact prefixLift 4578695
  have htrace : WordTrace (prefixWord ++ tailWord_4578695) baseStart_4578695 baseEnd_4578695 := by
    simpa [prefixWord, tailWord_4578695, baseEnd_4578695] using wordTrace_append hprefix tailTrace_4578695
  have hstable : (prefixWord ++ tailWord_4578695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578695).length < 2 ^ (prefixWord ++ tailWord_4578695).sum := by decide
  have hdescent : baseEnd_4578695 < baseStart_4578695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578706 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4578706 : Nat := 118140960795 + 4578706 * 2 ^ 59
def prefixEnd_4578706 : Nat := 4983230072969 + 3 ^ 40 * 4578706 * 2
def baseEnd_4578706 : Nat := 2351076953625268025417921

theorem tailTrace_4578706 : CollatzResearch.WordTrace tailWord_4578706 prefixEnd_4578706 2351076953625268025417921 := by
  unfold tailWord_4578706
  simp only [CollatzResearch.WordTrace]
  refine ⟨41749781837534404393310993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111332751566758411715495981 41749781837534404393310993)
  ·
    refine ⟨31312336378150803294983245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41749781837534404393310993 31312336378150803294983245)
    ·
      refine ⟨11742126141806551235618717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31312336378150803294983245 11742126141806551235618717)
      ·
        refine ⟨4403297303177456713357019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11742126141806551235618717 4403297303177456713357019)
        ·
          refine ⟨6604945954766185070035529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4403297303177456713357019 6604945954766185070035529)
          ·
            refine ⟨4953709466074638802526647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6604945954766185070035529 4953709466074638802526647)
            ·
              refine ⟨7430564199111958203789971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953709466074638802526647 7430564199111958203789971)
              ·
                refine ⟨11145846298667937305684957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7430564199111958203789971 11145846298667937305684957)
                ·
                  refine ⟨4179692362000476489631859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11145846298667937305684957 4179692362000476489631859)
                  ·
                    refine ⟨6269538543000714734447789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4179692362000476489631859 6269538543000714734447789)
                    ·
                      refine ⟨2351076953625268025417921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269538543000714734447789 2351076953625268025417921)
                      ·
                        rfl

theorem cell23_4578706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4578706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578706 prefixEnd_4578706 := by exact prefixLift 4578706
  have htrace : WordTrace (prefixWord ++ tailWord_4578706) baseStart_4578706 baseEnd_4578706 := by
    simpa [prefixWord, tailWord_4578706, baseEnd_4578706] using wordTrace_append hprefix tailTrace_4578706
  have hstable : (prefixWord ++ tailWord_4578706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578706).length < 2 ^ (prefixWord ++ tailWord_4578706).sum := by decide
  have hdescent : baseEnd_4578706 < baseStart_4578706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578722 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_4578722 : Nat := 118140960795 + 4578722 * 2 ^ 59
def prefixEnd_4578722 : Nat := 4983230072969 + 3 ^ 40 * 4578722 * 2
def baseEnd_4578722 : Nat := 783695056438579987605949

theorem tailTrace_4578722 : CollatzResearch.WordTrace tailWord_4578722 prefixEnd_4578722 783695056438579987605949 := by
  unfold tailWord_4578722
  simp only [CollatzResearch.WordTrace]
  refine ⟨41749927729519913076456605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111333140612053101537217613 41749927729519913076456605)
  ·
    refine ⟨15656222898569967403671227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41749927729519913076456605 15656222898569967403671227)
    ·
      refine ⟨23484334347854951105506841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15656222898569967403671227 23484334347854951105506841)
      ·
        refine ⟨17613250760891213329130131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23484334347854951105506841 17613250760891213329130131)
        ·
          refine ⟨26419876141336819993695197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17613250760891213329130131 26419876141336819993695197)
          ·
            refine ⟨9907453553001307497635699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26419876141336819993695197 9907453553001307497635699)
            ·
              refine ⟨14861180329501961246453549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9907453553001307497635699 14861180329501961246453549)
              ·
                refine ⟨5572942623563235467420081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14861180329501961246453549 5572942623563235467420081)
                ·
                  refine ⟨4179706967672426600565061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5572942623563235467420081 4179706967672426600565061)
                  ·
                    refine ⟨783695056438579987605949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4179706967672426600565061 783695056438579987605949)
                    ·
                      rfl

theorem cell23_4578722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_4578722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578722 prefixEnd_4578722 := by exact prefixLift 4578722
  have htrace : WordTrace (prefixWord ++ tailWord_4578722) baseStart_4578722 baseEnd_4578722 := by
    simpa [prefixWord, tailWord_4578722, baseEnd_4578722] using wordTrace_append hprefix tailTrace_4578722
  have hstable : (prefixWord ++ tailWord_4578722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578722).length < 2 ^ (prefixWord ++ tailWord_4578722).sum := by decide
  have hdescent : baseEnd_4578722 < baseStart_4578722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578762 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_4578762 : Nat := 118140960795 + 4578762 * 2 ^ 59
def prefixEnd_4578762 : Nat := 4983230072969 + 3 ^ 40 * 4578762 * 2
def baseEnd_4578762 : Nat := 2351105708541919806317663

theorem tailTrace_4578762 : CollatzResearch.WordTrace tailWord_4578762 prefixEnd_4578762 2351105708541919806317663 := by
  unfold tailWord_4578762
  simp only [CollatzResearch.WordTrace]
  refine ⟨41750292459483684784320635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111334113225289826091521693 41750292459483684784320635)
  ·
    refine ⟨62625438689225527176480953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41750292459483684784320635 62625438689225527176480953)
    ·
      refine ⟨46969079016919145382360715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62625438689225527176480953 46969079016919145382360715)
      ·
        refine ⟨70453618525378718073541073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46969079016919145382360715 70453618525378718073541073)
        ·
          refine ⟨52840213894034038555155805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70453618525378718073541073 52840213894034038555155805)
          ·
            refine ⟨19815080210262764458183427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52840213894034038555155805 19815080210262764458183427)
            ·
              refine ⟨29722620315394146687275141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19815080210262764458183427 29722620315394146687275141)
              ·
                refine ⟨5572991309136402503864089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29722620315394146687275141 5572991309136402503864089)
                ·
                  refine ⟨4179743481852301877898067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5572991309136402503864089 4179743481852301877898067)
                  ·
                    refine ⟨6269615222778452816847101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4179743481852301877898067 6269615222778452816847101)
                    ·
                      refine ⟨2351105708541919806317663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269615222778452816847101 2351105708541919806317663)
                      ·
                        rfl

theorem cell23_4578762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_4578762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578762 prefixEnd_4578762 := by exact prefixLift 4578762
  have htrace : WordTrace (prefixWord ++ tailWord_4578762) baseStart_4578762 baseEnd_4578762 := by
    simpa [prefixWord, tailWord_4578762, baseEnd_4578762] using wordTrace_append hprefix tailTrace_4578762
  have hstable : (prefixWord ++ tailWord_4578762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578762).length < 2 ^ (prefixWord ++ tailWord_4578762).sum := by decide
  have hdescent : baseEnd_4578762 < baseStart_4578762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578778 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_4578778 : Nat := 118140960795 + 4578778 * 2 ^ 59
def prefixEnd_4578778 : Nat := 4983230072969 + 3 ^ 40 * 4578778 * 2
def baseEnd_4578778 : Nat := 783704641410797247905863

theorem tailTrace_4578778 : CollatzResearch.WordTrace tailWord_4578778 prefixEnd_4578778 783704641410797247905863 := by
  unfold tailWord_4578778
  simp only [CollatzResearch.WordTrace]
  refine ⟨41750438351469193467466247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111334502270584515913243325 41750438351469193467466247)
  ·
    refine ⟨62625657527203790201199371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41750438351469193467466247 62625657527203790201199371)
    ·
      refine ⟨93938486290805685301799057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62625657527203790201199371 93938486290805685301799057)
      ·
        refine ⟨70453864718104263976349293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93938486290805685301799057 70453864718104263976349293)
        ·
          refine ⟨26420199269289098991130985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70453864718104263976349293 26420199269289098991130985)
          ·
            refine ⟨19815149451966824243348239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26420199269289098991130985 19815149451966824243348239)
            ·
              refine ⟨29722724177950236365022359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19815149451966824243348239 29722724177950236365022359)
              ·
                refine ⟨44584086266925354547533539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29722724177950236365022359 44584086266925354547533539)
                ·
                  refine ⟨66876129400388031821300309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44584086266925354547533539 66876129400388031821300309)
                  ·
                    refine ⟨783704641410797247905863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66876129400388031821300309 783704641410797247905863)
                    ·
                      rfl

theorem cell23_4578778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_4578778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578778 prefixEnd_4578778 := by exact prefixLift 4578778
  have htrace : WordTrace (prefixWord ++ tailWord_4578778) baseStart_4578778 baseEnd_4578778 := by
    simpa [prefixWord, tailWord_4578778, baseEnd_4578778] using wordTrace_append hprefix tailTrace_4578778
  have hstable : (prefixWord ++ tailWord_4578778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578778).length < 2 ^ (prefixWord ++ tailWord_4578778).sum := by decide
  have hdescent : baseEnd_4578778 < baseStart_4578778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578788 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_4578788 : Nat := 118140960795 + 4578788 * 2 ^ 59
def prefixEnd_4578788 : Nat := 4983230072969 + 3 ^ 40 * 4578788 * 2
def baseEnd_4578788 : Nat := 2351119059038936704592543

theorem tailTrace_4578788 : CollatzResearch.WordTrace tailWord_4578788 prefixEnd_4578788 2351119059038936704592543 := by
  unfold tailWord_4578788
  simp only [CollatzResearch.WordTrace]
  refine ⟨83501059067920272788864509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111334745423893697051819345 83501059067920272788864509)
  ·
    refine ⟨31312897150470102295824191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83501059067920272788864509 31312897150470102295824191)
    ·
      refine ⟨46969345725705153443736287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31312897150470102295824191 46969345725705153443736287)
      ·
        refine ⟨70454018588557730165604431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46969345725705153443736287 70454018588557730165604431)
        ·
          refine ⟨105681027882836595248406647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70454018588557730165604431 105681027882836595248406647)
          ·
            refine ⟨158521541824254892872609971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105681027882836595248406647 158521541824254892872609971)
            ·
              refine ⟨237782312736382339308914957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158521541824254892872609971 237782312736382339308914957)
              ·
                refine ⟨89168367276143377240843109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237782312736382339308914957 89168367276143377240843109)
                ·
                  refine ⟨16719068864276883232658083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89168367276143377240843109 16719068864276883232658083)
                  ·
                    refine ⟨25078603296415324848987125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16719068864276883232658083 25078603296415324848987125)
                    ·
                      refine ⟨2351119059038936704592543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25078603296415324848987125 2351119059038936704592543)
                      ·
                        rfl

theorem cell23_4578788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_4578788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578788 prefixEnd_4578788 := by exact prefixLift 4578788
  have htrace : WordTrace (prefixWord ++ tailWord_4578788) baseStart_4578788 baseEnd_4578788 := by
    simpa [prefixWord, tailWord_4578788, baseEnd_4578788] using wordTrace_append hprefix tailTrace_4578788
  have hstable : (prefixWord ++ tailWord_4578788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578788).length < 2 ^ (prefixWord ++ tailWord_4578788).sum := by decide
  have hdescent : baseEnd_4578788 < baseStart_4578788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578806 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_4578806 : Nat := 118140960795 + 4578806 * 2 ^ 59
def prefixEnd_4578806 : Nat := 4983230072969 + 3 ^ 40 * 4578806 * 2
def baseEnd_4578806 : Nat := 2351128301690717634167461

theorem tailTrace_4578806 : CollatzResearch.WordTrace tailWord_4578806 prefixEnd_4578806 2351128301690717634167461 := by
  unfold tailWord_4578806
  simp only [CollatzResearch.WordTrace]
  refine ⟨10437673415610958415742767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111335183099850223101256181 10437673415610958415742767)
  ·
    refine ⟨15656510123416437623614151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10437673415610958415742767 15656510123416437623614151)
    ·
      refine ⟨23484765185124656435421227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15656510123416437623614151 23484765185124656435421227)
      ·
        refine ⟨35227147777686984653131841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23484765185124656435421227 35227147777686984653131841)
        ·
          refine ⟨26420360833265238489848881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35227147777686984653131841 26420360833265238489848881)
          ·
            refine ⟨19815270624948928867386661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26420360833265238489848881 19815270624948928867386661)
            ·
              refine ⟨3715363242177924162634999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19815270624948928867386661 3715363242177924162634999)
              ·
                refine ⟨5573044863266886243952499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715363242177924162634999 5573044863266886243952499)
                ·
                  refine ⟨8359567294900329365928749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5573044863266886243952499 8359567294900329365928749)
                  ·
                    refine ⟨3134837735587623512223281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8359567294900329365928749 3134837735587623512223281)
                    ·
                      refine ⟨2351128301690717634167461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3134837735587623512223281 2351128301690717634167461)
                      ·
                        rfl

theorem cell23_4578806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_4578806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578806 prefixEnd_4578806 := by exact prefixLift 4578806
  have htrace : WordTrace (prefixWord ++ tailWord_4578806) baseStart_4578806 baseEnd_4578806 := by
    simpa [prefixWord, tailWord_4578806, baseEnd_4578806] using wordTrace_append hprefix tailTrace_4578806
  have hstable : (prefixWord ++ tailWord_4578806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578806).length < 2 ^ (prefixWord ++ tailWord_4578806).sum := by decide
  have hdescent : baseEnd_4578806 < baseStart_4578806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578825 : List Nat := [1, 2, 1, 1, 3, 1, 3, 6, 5]
def baseStart_4578825 : Nat := 118140960795 + 4578825 * 2 ^ 59
def prefixEnd_4578825 : Nat := 4983230072969 + 3 ^ 40 * 4578825 * 2
def baseEnd_4578825 : Nat := 261237561980350339981097

theorem tailTrace_4578825 : CollatzResearch.WordTrace tailWord_4578825 prefixEnd_4578825 261237561980350339981097 := by
  unfold tailWord_4578825
  simp only [CollatzResearch.WordTrace]
  refine ⟨167003467636706500896825929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111335645091137667264550619 167003467636706500896825929)
  ·
    refine ⟨125252600727529875672619447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167003467636706500896825929 125252600727529875672619447)
    ·
      refine ⟨187878901091294813508929171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125252600727529875672619447 187878901091294813508929171)
      ·
        refine ⟨281818351636942220263393757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187878901091294813508929171 281818351636942220263393757)
        ·
          refine ⟨105681881863853332598772659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281818351636942220263393757 105681881863853332598772659)
          ·
            refine ⟨158522822795779998898158989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105681881863853332598772659 158522822795779998898158989)
            ·
              refine ⟨59446058548417499586809621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158522822795779998898158989 59446058548417499586809621)
              ·
                refine ⟨2786533994457070293131701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59446058548417499586809621 2786533994457070293131701)
                ·
                  refine ⟨261237561980350339981097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2786533994457070293131701 261237561980350339981097)
                  ·
                    rfl

theorem cell23_4578825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 5].length) (baseStart_4578825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578825 prefixEnd_4578825 := by exact prefixLift 4578825
  have htrace : WordTrace (prefixWord ++ tailWord_4578825) baseStart_4578825 baseEnd_4578825 := by
    simpa [prefixWord, tailWord_4578825, baseEnd_4578825] using wordTrace_append hprefix tailTrace_4578825
  have hstable : (prefixWord ++ tailWord_4578825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578825).length < 2 ^ (prefixWord ++ tailWord_4578825).sum := by decide
  have hdescent : baseEnd_4578825 < baseStart_4578825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578835 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 3]
def baseStart_4578835 : Nat := 118140960795 + 4578835 * 2 ^ 59
def prefixEnd_4578835 : Nat := 4983230072969 + 3 ^ 40 * 4578835 * 2
def baseEnd_4578835 : Nat := 2351143192629698020704827

theorem tailTrace_4578835 : CollatzResearch.WordTrace tailWord_4578835 prefixEnd_4578835 2351143192629698020704827 := by
  unfold tailWord_4578835
  simp only [CollatzResearch.WordTrace]
  refine ⟨167003832366670272604689959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111335888244446848403126639 167003832366670272604689959)
  ·
    refine ⟨250505748550005408907034939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167003832366670272604689959 250505748550005408907034939)
    ·
      refine ⟨375758622825008113360552409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250505748550005408907034939 375758622825008113360552409)
      ·
        refine ⟨281818967118756085020414307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375758622825008113360552409 281818967118756085020414307)
        ·
          refine ⟨422728450678134127530621461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281818967118756085020414307 422728450678134127530621461)
          ·
            refine ⟨19815396125537537227997881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 422728450678134127530621461 19815396125537537227997881)
            ·
              refine ⟨14861547094153152920998411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19815396125537537227997881 14861547094153152920998411)
              ·
                refine ⟨22292320641229729381497617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14861547094153152920998411 22292320641229729381497617)
                ·
                  refine ⟨16719240480922297036123213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22292320641229729381497617 16719240480922297036123213)
                  ·
                    refine ⟨6269715180345861388546205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16719240480922297036123213 6269715180345861388546205)
                    ·
                      refine ⟨2351143192629698020704827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269715180345861388546205 2351143192629698020704827)
                      ·
                        rfl

theorem cell23_4578835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 3].length) (baseStart_4578835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578835 prefixEnd_4578835 := by exact prefixLift 4578835
  have htrace : WordTrace (prefixWord ++ tailWord_4578835) baseStart_4578835 baseEnd_4578835 := by
    simpa [prefixWord, tailWord_4578835, baseEnd_4578835] using wordTrace_append hprefix tailTrace_4578835
  have hstable : (prefixWord ++ tailWord_4578835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578835).length < 2 ^ (prefixWord ++ tailWord_4578835).sum := by decide
  have hdescent : baseEnd_4578835 < baseStart_4578835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578895 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 3]
def baseStart_4578895 : Nat := 118140960795 + 4578895 * 2 ^ 59
def prefixEnd_4578895 : Nat := 4983230072969 + 3 ^ 40 * 4578895 * 2
def baseEnd_4578895 : Nat := 2351174001468967785954551

theorem tailTrace_4578895 : CollatzResearch.WordTrace tailWord_4578895 prefixEnd_4578895 2351174001468967785954551 := by
  unfold tailWord_4578895
  simp only [CollatzResearch.WordTrace]
  refine ⟨167006020746452902851874139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111337347164301935234582759 167006020746452902851874139)
  ·
    refine ⟨250509031119679354277811209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167006020746452902851874139 250509031119679354277811209)
    ·
      refine ⟨187881773339759515708358407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250509031119679354277811209 187881773339759515708358407)
      ·
        refine ⟨281822660009639273562537611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187881773339759515708358407 281822660009639273562537611)
        ·
          refine ⟨422733990014458910343806417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281822660009639273562537611 422733990014458910343806417)
          ·
            refine ⟨317050492510844182757854813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422733990014458910343806417 317050492510844182757854813)
            ·
              refine ⟨118893934691566568534195555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317050492510844182757854813 118893934691566568534195555)
              ·
                refine ⟨178340902037349852801293333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118893934691566568534195555 178340902037349852801293333)
                ·
                  refine ⟨8359729783000774350060625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 178340902037349852801293333 8359729783000774350060625)
                  ·
                    refine ⟨6269797337250580762545469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8359729783000774350060625 6269797337250580762545469)
                    ·
                      refine ⟨2351174001468967785954551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269797337250580762545469 2351174001468967785954551)
                      ·
                        rfl

theorem cell23_4578895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 3].length) (baseStart_4578895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578895 prefixEnd_4578895 := by exact prefixLift 4578895
  have htrace : WordTrace (prefixWord ++ tailWord_4578895) baseStart_4578895 baseEnd_4578895 := by
    simpa [prefixWord, tailWord_4578895, baseEnd_4578895] using wordTrace_append hprefix tailTrace_4578895
  have hstable : (prefixWord ++ tailWord_4578895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578895).length < 2 ^ (prefixWord ++ tailWord_4578895).sum := by decide
  have hdescent : baseEnd_4578895 < baseStart_4578895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578976 : List Nat := [2, 1, 1, 4, 3, 1, 1, 5, 1, 1, 3]
def baseStart_4578976 : Nat := 118140960795 + 4578976 * 2 ^ 59
def prefixEnd_4578976 : Nat := 4983230072969 + 3 ^ 40 * 4578976 * 2
def baseEnd_4578976 : Nat := 2351215593401981969041679

theorem tailTrace_4578976 : CollatzResearch.WordTrace tailWord_4578976 prefixEnd_4578976 2351215593401981969041679 := by
  unfold tailWord_4578976
  simp only [CollatzResearch.WordTrace]
  refine ⟨83504487529579726842786391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111339316706106302457048521 83504487529579726842786391)
  ·
    refine ⟨125256731294369590264179587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83504487529579726842786391 125256731294369590264179587)
    ·
      refine ⟨187885096941554385396269381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125256731294369590264179587 187885096941554385396269381)
      ·
        refine ⟨35228455676541447261800509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187885096941554385396269381 35228455676541447261800509)
        ·
          refine ⟨13210670878703042723175191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35228455676541447261800509 13210670878703042723175191)
          ·
            refine ⟨19816006318054564084762787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13210670878703042723175191 19816006318054564084762787)
            ·
              refine ⟨29724009477081846127144181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19816006318054564084762787 29724009477081846127144181)
              ·
                refine ⟨2786625888476423074419767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29724009477081846127144181 2786625888476423074419767)
                ·
                  refine ⟨4179938832714634611629651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2786625888476423074419767 4179938832714634611629651)
                  ·
                    refine ⟨6269908249071951917444477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4179938832714634611629651 6269908249071951917444477)
                    ·
                      refine ⟨2351215593401981969041679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269908249071951917444477 2351215593401981969041679)
                      ·
                        rfl

theorem cell23_4578976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_4578976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578976 prefixEnd_4578976 := by exact prefixLift 4578976
  have htrace : WordTrace (prefixWord ++ tailWord_4578976) baseStart_4578976 baseEnd_4578976 := by
    simpa [prefixWord, tailWord_4578976, baseEnd_4578976] using wordTrace_append hprefix tailTrace_4578976
  have hstable : (prefixWord ++ tailWord_4578976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578976).length < 2 ^ (prefixWord ++ tailWord_4578976).sum := by decide
  have hdescent : baseEnd_4578976 < baseStart_4578976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578985 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 8, 3]
def baseStart_4578985 : Nat := 118140960795 + 4578985 * 2 ^ 59
def prefixEnd_4578985 : Nat := 4983230072969 + 3 ^ 40 * 4578985 * 2
def baseEnd_4578985 : Nat := 2351220214727872433829137

theorem tailTrace_4578985 : CollatzResearch.WordTrace tailWord_4578985 prefixEnd_4578985 2351220214727872433829137 := by
  unfold tailWord_4578985
  simp only [CollatzResearch.WordTrace]
  refine ⟨167009303316126848222650409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111339535544084565481766939 167009303316126848222650409)
  ·
    refine ⟨125256977487095136166987807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167009303316126848222650409 125256977487095136166987807)
    ·
      refine ⟨187885466230642704250481711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125256977487095136166987807 187885466230642704250481711)
      ·
        refine ⟨281828199345964056375722567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187885466230642704250481711 281828199345964056375722567)
        ·
          refine ⟨422742299018946084563583851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281828199345964056375722567 422742299018946084563583851)
          ·
            refine ⟨634113448528419126845375777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422742299018946084563583851 634113448528419126845375777)
            ·
              refine ⟨475585086396314345134031833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 634113448528419126845375777 475585086396314345134031833)
              ·
                refine ⟨356688814797235758850523875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475585086396314345134031833 356688814797235758850523875)
                ·
                  refine ⟨535033222195853638275785813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356688814797235758850523875 535033222195853638275785813)
                  ·
                    refine ⟨6269920572607659823544365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 535033222195853638275785813 6269920572607659823544365)
                    ·
                      refine ⟨2351220214727872433829137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269920572607659823544365 2351220214727872433829137)
                      ·
                        rfl

theorem cell23_4578985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8, 3].length) (baseStart_4578985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578985 prefixEnd_4578985 := by exact prefixLift 4578985
  have htrace : WordTrace (prefixWord ++ tailWord_4578985) baseStart_4578985 baseEnd_4578985 := by
    simpa [prefixWord, tailWord_4578985, baseEnd_4578985] using wordTrace_append hprefix tailTrace_4578985
  have hstable : (prefixWord ++ tailWord_4578985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578985).length < 2 ^ (prefixWord ++ tailWord_4578985).sum := by decide
  have hdescent : baseEnd_4578985 < baseStart_4578985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578995 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 6]
def baseStart_4578995 : Nat := 118140960795 + 4578995 * 2 ^ 59
def prefixEnd_4578995 : Nat := 4983230072969 + 3 ^ 40 * 4578995 * 2
def baseEnd_4578995 : Nat := 2351225349534417394704091

theorem tailTrace_4578995 : CollatzResearch.WordTrace tailWord_4578995 prefixEnd_4578995 2351225349534417394704091 := by
  unfold tailWord_4578995
  simp only [CollatzResearch.WordTrace]
  refine ⟨167009668046090619930514439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111339778697393746620342959 167009668046090619930514439)
  ·
    refine ⟨250514502069135929895771659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167009668046090619930514439 250514502069135929895771659)
    ·
      refine ⟨375771753103703894843657489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250514502069135929895771659 375771753103703894843657489)
      ·
        refine ⟨281828814827777921132743117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375771753103703894843657489 281828814827777921132743117)
        ·
          refine ⟨105685805560416720424778669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281828814827777921132743117 105685805560416720424778669)
          ·
            refine ⟨39632177085156270159292001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105685805560416720424778669 39632177085156270159292001)
            ·
              refine ⟨29724132813867202619469001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39632177085156270159292001 29724132813867202619469001)
              ·
                refine ⟨22293099610400401964601751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29724132813867202619469001 22293099610400401964601751)
                ·
                  refine ⟨33439649415600602946902627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22293099610400401964601751 33439649415600602946902627)
                  ·
                    refine ⟨50159474123400904420353941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33439649415600602946902627 50159474123400904420353941)
                    ·
                      refine ⟨2351225349534417394704091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50159474123400904420353941 2351225349534417394704091)
                      ·
                        rfl

theorem cell23_4578995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_4578995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4578995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4578995 prefixEnd_4578995 := by exact prefixLift 4578995
  have htrace : WordTrace (prefixWord ++ tailWord_4578995) baseStart_4578995 baseEnd_4578995 := by
    simpa [prefixWord, tailWord_4578995, baseEnd_4578995] using wordTrace_append hprefix tailTrace_4578995
  have hstable : (prefixWord ++ tailWord_4578995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578995).length < 2 ^ (prefixWord ++ tailWord_4578995).sum := by decide
  have hdescent : baseEnd_4578995 < baseStart_4578995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579002 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_4579002 : Nat := 118140960795 + 4579002 * 2 ^ 59
def prefixEnd_4579002 : Nat := 4983230072969 + 3 ^ 40 * 4579002 * 2
def baseEnd_4579002 : Nat := 2351228943898998867316559

theorem tailTrace_4579002 : CollatzResearch.WordTrace tailWord_4579002 prefixEnd_4579002 2351228943898998867316559 := by
  unfold tailWord_4579002
  simp only [CollatzResearch.WordTrace]
  refine ⟨41752480839266315031504815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111339948904710173417346173 41752480839266315031504815)
  ·
    refine ⟨62628721258899472547257223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41752480839266315031504815 62628721258899472547257223)
    ·
      refine ⟨93943081888349208820885835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62628721258899472547257223 93943081888349208820885835)
      ·
        refine ⟨140914622832523813231328753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93943081888349208820885835 140914622832523813231328753)
        ·
          refine ⟨105685967124392859923496565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140914622832523813231328753 105685967124392859923496565)
          ·
            refine ⟨9908059417911830617827803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105685967124392859923496565 9908059417911830617827803)
            ·
              refine ⟨14862089126867745926741705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9908059417911830617827803 14862089126867745926741705)
              ·
                refine ⟨11146566845150809445056279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14862089126867745926741705 11146566845150809445056279)
                ·
                  refine ⟨16719850267726214167584419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11146566845150809445056279 16719850267726214167584419)
                  ·
                    refine ⟨25079775401589321251376629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16719850267726214167584419 25079775401589321251376629)
                    ·
                      refine ⟨2351228943898998867316559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25079775401589321251376629 2351228943898998867316559)
                      ·
                        rfl

theorem cell23_4579002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_4579002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579002 prefixEnd_4579002 := by exact prefixLift 4579002
  have htrace : WordTrace (prefixWord ++ tailWord_4579002) baseStart_4579002 baseEnd_4579002 := by
    simpa [prefixWord, tailWord_4579002, baseEnd_4579002] using wordTrace_append hprefix tailTrace_4579002
  have hstable : (prefixWord ++ tailWord_4579002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579002).length < 2 ^ (prefixWord ++ tailWord_4579002).sum := by decide
  have hdescent : baseEnd_4579002 < baseStart_4579002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579005 : List Nat := [1, 4, 1, 2, 1, 2, 2, 10]
def baseStart_4579005 : Nat := 118140960795 + 4579005 * 2 ^ 59
def prefixEnd_4579005 : Nat := 4983230072969 + 3 ^ 40 * 4579005 * 2
def baseEnd_4579005 : Nat := 87082610531146753910335

theorem tailTrace_4579005 : CollatzResearch.WordTrace tailWord_4579005 prefixEnd_4579005 87082610531146753910335 := by
  unfold tailWord_4579005
  simp only [CollatzResearch.WordTrace]
  refine ⟨167010032776054391638378469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111340021850702927758918979 167010032776054391638378469)
  ·
    refine ⟨31314381145510198432195963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167010032776054391638378469 31314381145510198432195963)
    ·
      refine ⟨46971571718265297648293945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31314381145510198432195963 46971571718265297648293945)
      ·
        refine ⟨35228678788698973236220459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46971571718265297648293945 35228678788698973236220459)
        ·
          refine ⟨52843018183048459854330689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35228678788698973236220459 52843018183048459854330689)
          ·
            refine ⟨39632263637286344890748017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52843018183048459854330689 39632263637286344890748017)
            ·
              refine ⟨29724197727964758668061013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39632263637286344890748017 29724197727964758668061013)
              ·
                refine ⟨87082610531146753910335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29724197727964758668061013 87082610531146753910335)
                ·
                  rfl

theorem cell23_4579005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 10].length) (baseStart_4579005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579005 prefixEnd_4579005 := by exact prefixLift 4579005
  have htrace : WordTrace (prefixWord ++ tailWord_4579005) baseStart_4579005 baseEnd_4579005 := by
    simpa [prefixWord, tailWord_4579005, baseEnd_4579005] using wordTrace_append hprefix tailTrace_4579005
  have hstable : (prefixWord ++ tailWord_4579005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579005).length < 2 ^ (prefixWord ++ tailWord_4579005).sum := by decide
  have hdescent : baseEnd_4579005 < baseStart_4579005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579012 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_4579012 : Nat := 118140960795 + 4579012 * 2 ^ 59
def prefixEnd_4579012 : Nat := 4983230072969 + 3 ^ 40 * 4579012 * 2
def baseEnd_4579012 : Nat := 2351234078705543828191513

theorem tailTrace_4579012 : CollatzResearch.WordTrace tailWord_4579012 prefixEnd_4579012 2351234078705543828191513 := by
  unfold tailWord_4579012
  simp only [CollatzResearch.WordTrace]
  refine ⟨83505144043514515916941645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111340192058019354555922193 83505144043514515916941645)
  ·
    refine ⟨31314429016317943468853117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83505144043514515916941645 31314429016317943468853117)
    ·
      refine ⟨11742910881119228800819919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31314429016317943468853117 11742910881119228800819919)
      ·
        refine ⟨17614366321678843201229879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11742910881119228800819919 17614366321678843201229879)
        ·
          refine ⟨26421549482518264801844819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17614366321678843201229879 26421549482518264801844819)
          ·
            refine ⟨39632324223777397202767229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26421549482518264801844819 39632324223777397202767229)
            ·
              refine ⟨14862121583916523951037711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39632324223777397202767229 14862121583916523951037711)
              ·
                refine ⟨22293182375874785926556567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14862121583916523951037711 22293182375874785926556567)
                ·
                  refine ⟨33439773563812178889834851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22293182375874785926556567 33439773563812178889834851)
                  ·
                    refine ⟨50159660345718268334752277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33439773563812178889834851 50159660345718268334752277)
                    ·
                      refine ⟨2351234078705543828191513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50159660345718268334752277 2351234078705543828191513)
                      ·
                        rfl

theorem cell23_4579012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_4579012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579012 prefixEnd_4579012 := by exact prefixLift 4579012
  have htrace : WordTrace (prefixWord ++ tailWord_4579012) baseStart_4579012 baseEnd_4579012 := by
    simpa [prefixWord, tailWord_4579012, baseEnd_4579012] using wordTrace_append hprefix tailTrace_4579012
  have hstable : (prefixWord ++ tailWord_4579012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579012).length < 2 ^ (prefixWord ++ tailWord_4579012).sum := by decide
  have hdescent : baseEnd_4579012 < baseStart_4579012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579032 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 3, 3, 3]
def baseStart_4579032 : Nat := 118140960795 + 4579032 * 2 ^ 59
def prefixEnd_4579032 : Nat := 4983230072969 + 3 ^ 40 * 4579032 * 2
def baseEnd_4579032 : Nat := 2351244348318633749941421

theorem tailTrace_4579032 : CollatzResearch.WordTrace tailWord_4579032 prefixEnd_4579032 2351244348318633749941421 := by
  unfold tailWord_4579032
  simp only [CollatzResearch.WordTrace]
  refine ⟨83505508773478287624805675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111340678364637716833074233 83505508773478287624805675)
  ·
    refine ⟨125258263160217431437208513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83505508773478287624805675 125258263160217431437208513)
    ·
      refine ⟨93943697370163073577906385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125258263160217431437208513 93943697370163073577906385)
      ·
        refine ⟨70457773027622305183429789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93943697370163073577906385 70457773027622305183429789)
        ·
          refine ⟨26421664885358364443786171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70457773027622305183429789 26421664885358364443786171)
          ·
            refine ⟨39632497328037546665679257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26421664885358364443786171 39632497328037546665679257)
            ·
              refine ⟨29724372996028159999259443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39632497328037546665679257 29724372996028159999259443)
              ·
                refine ⟨44586559494042239998889165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29724372996028159999259443 44586559494042239998889165)
                ·
                  refine ⟨16719959810265839999583437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44586559494042239998889165 16719959810265839999583437)
                  ·
                    refine ⟨6269984928849689999843789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16719959810265839999583437 6269984928849689999843789)
                    ·
                      refine ⟨2351244348318633749941421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6269984928849689999843789 2351244348318633749941421)
                      ·
                        rfl

theorem cell23_4579032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_4579032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579032 prefixEnd_4579032 := by exact prefixLift 4579032
  have htrace : WordTrace (prefixWord ++ tailWord_4579032) baseStart_4579032 baseEnd_4579032 := by
    simpa [prefixWord, tailWord_4579032, baseEnd_4579032] using wordTrace_append hprefix tailTrace_4579032
  have hstable : (prefixWord ++ tailWord_4579032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579032).length < 2 ^ (prefixWord ++ tailWord_4579032).sum := by decide
  have hdescent : baseEnd_4579032 < baseStart_4579032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579033 : List Nat := [1, 2, 1, 2, 3, 3, 3, 3, 1, 2, 2]
def baseStart_4579033 : Nat := 118140960795 + 4579033 * 2 ^ 59
def prefixEnd_4579033 : Nat := 4983230072969 + 3 ^ 40 * 4579033 * 2
def baseEnd_4579033 : Nat := 2351244861799288246028917

theorem tailTrace_4579033 : CollatzResearch.WordTrace tailWord_4579033 prefixEnd_4579033 2351244861799288246028917 := by
  unfold tailWord_4579033
  simp only [CollatzResearch.WordTrace]
  refine ⟨167011054019952952420397753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111340702679968634946931835 167011054019952952420397753)
  ·
    refine ⟨125258290514964714315298315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167011054019952952420397753 125258290514964714315298315)
    ·
      refine ⟨187887435772447071472947473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125258290514964714315298315 187887435772447071472947473)
      ·
        refine ⟨140915576829335303604710605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187887435772447071472947473 140915576829335303604710605)
        ·
          refine ⟨52843341311000738851766477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140915576829335303604710605 52843341311000738851766477)
          ·
            refine ⟨19816252991625277069412429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52843341311000738851766477 19816252991625277069412429)
            ·
              refine ⟨7431094871859478901029661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19816252991625277069412429 7431094871859478901029661)
              ·
                refine ⟨2786660576947304587886123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7431094871859478901029661 2786660576947304587886123)
                ·
                  refine ⟨4179990865420956881829185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2786660576947304587886123 4179990865420956881829185)
                  ·
                    refine ⟨3134993149065717661371889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4179990865420956881829185 3134993149065717661371889)
                    ·
                      refine ⟨2351244861799288246028917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3134993149065717661371889 2351244861799288246028917)
                      ·
                        rfl

theorem cell23_4579033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 1, 2, 2].length) (baseStart_4579033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579033 prefixEnd_4579033 := by exact prefixLift 4579033
  have htrace : WordTrace (prefixWord ++ tailWord_4579033) baseStart_4579033 baseEnd_4579033 := by
    simpa [prefixWord, tailWord_4579033, baseEnd_4579033] using wordTrace_append hprefix tailTrace_4579033
  have hstable : (prefixWord ++ tailWord_4579033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579033).length < 2 ^ (prefixWord ++ tailWord_4579033).sum := by decide
  have hdescent : baseEnd_4579033 < baseStart_4579033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579036 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4579036 : Nat := 118140960795 + 4579036 * 2 ^ 59
def prefixEnd_4579036 : Nat := 4983230072969 + 3 ^ 40 * 4579036 * 2
def baseEnd_4579036 : Nat := 2351246402241251734291403

theorem tailTrace_4579036 : CollatzResearch.WordTrace tailWord_4579036 prefixEnd_4579036 2351246402241251734291403 := by
  unfold tailWord_4579036
  simp only [CollatzResearch.WordTrace]
  refine ⟨83505581719471041966378481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111340775625961389288504641 83505581719471041966378481)
  ·
    refine ⟨62629186289603281474783861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83505581719471041966378481 62629186289603281474783861)
    ·
      refine ⟨5871486214650307638260987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62629186289603281474783861 5871486214650307638260987)
      ·
        refine ⟨8807229321975461457391481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5871486214650307638260987 8807229321975461457391481)
        ·
          refine ⟨6605421991481596093043611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8807229321975461457391481 6605421991481596093043611)
          ·
            refine ⟨9908132987222394139565417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6605421991481596093043611 9908132987222394139565417)
            ·
              refine ⟨7431099740416795604674063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9908132987222394139565417 7431099740416795604674063)
              ·
                refine ⟨11146649610625193407011095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7431099740416795604674063 11146649610625193407011095)
                ·
                  refine ⟨16719974415937790110516643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11146649610625193407011095 16719974415937790110516643)
                  ·
                    refine ⟨25079961623906685165774965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16719974415937790110516643 25079961623906685165774965)
                    ·
                      refine ⟨2351246402241251734291403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25079961623906685165774965 2351246402241251734291403)
                      ·
                        rfl

theorem cell23_4579036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4579036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579036 prefixEnd_4579036 := by exact prefixLift 4579036
  have htrace : WordTrace (prefixWord ++ tailWord_4579036) baseStart_4579036 baseEnd_4579036 := by
    simpa [prefixWord, tailWord_4579036, baseEnd_4579036] using wordTrace_append hprefix tailTrace_4579036
  have hstable : (prefixWord ++ tailWord_4579036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579036).length < 2 ^ (prefixWord ++ tailWord_4579036).sum := by decide
  have hdescent : baseEnd_4579036 < baseStart_4579036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579049 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 2, 1, 3]
def baseStart_4579049 : Nat := 118140960795 + 4579049 * 2 ^ 59
def prefixEnd_4579049 : Nat := 4983230072969 + 3 ^ 40 * 4579049 * 2
def baseEnd_4579049 : Nat := 2351253077489760183428843

theorem tailTrace_4579049 : CollatzResearch.WordTrace tailWord_4579049 prefixEnd_4579049 2351253077489760183428843 := by
  unfold tailWord_4579049
  simp only [CollatzResearch.WordTrace]
  refine ⟨167011637587894987152980201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111341091725263324768653467 167011637587894987152980201)
  ·
    refine ⟨125258728190921240364735151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167011637587894987152980201 125258728190921240364735151)
    ·
      refine ⟨187888092286381860547102727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125258728190921240364735151 187888092286381860547102727)
      ·
        refine ⟨281832138429572790820654091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187888092286381860547102727 281832138429572790820654091)
        ·
          refine ⟨422748207644359186230981137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281832138429572790820654091 422748207644359186230981137)
          ·
            refine ⟨317061155733269389673235853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422748207644359186230981137 317061155733269389673235853)
            ·
              refine ⟨118897933399976021127463445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317061155733269389673235853 118897933399976021127463445)
              ·
                refine ⟨5573340628123875990349849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118897933399976021127463445 5573340628123875990349849)
                ·
                  refine ⟨4180005471092906992762387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5573340628123875990349849 4180005471092906992762387)
                  ·
                    refine ⟨6270008206639360489143581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4180005471092906992762387 6270008206639360489143581)
                    ·
                      refine ⟨2351253077489760183428843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6270008206639360489143581 2351253077489760183428843)
                      ·
                        rfl

theorem cell23_4579049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 1, 3].length) (baseStart_4579049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579049 prefixEnd_4579049 := by exact prefixLift 4579049
  have htrace : WordTrace (prefixWord ++ tailWord_4579049) baseStart_4579049 baseEnd_4579049 := by
    simpa [prefixWord, tailWord_4579049, baseEnd_4579049] using wordTrace_append hprefix tailTrace_4579049
  have hstable : (prefixWord ++ tailWord_4579049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579049).length < 2 ^ (prefixWord ++ tailWord_4579049).sum := by decide
  have hdescent : baseEnd_4579049 < baseStart_4579049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579060 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_4579060 : Nat := 118140960795 + 4579060 * 2 ^ 59
def prefixEnd_4579060 : Nat := 4983230072969 + 3 ^ 40 * 4579060 * 2
def baseEnd_4579060 : Nat := 783752908592319880130431

theorem tailTrace_4579060 : CollatzResearch.WordTrace tailWord_4579060 prefixEnd_4579060 783752908592319880130431 := by
  unfold tailWord_4579060
  simp only [CollatzResearch.WordTrace]
  refine ⟨83506019395427568015815317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111341359193903424021087089 83506019395427568015815317)
  ·
    refine ⟨3914344659160667250741343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83506019395427568015815317 3914344659160667250741343)
    ·
      refine ⟨5871516988741000876112015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3914344659160667250741343 5871516988741000876112015)
      ·
        refine ⟨8807275483111501314168023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5871516988741000876112015 8807275483111501314168023)
        ·
          refine ⟨13210913224667251971252035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8807275483111501314168023 13210913224667251971252035)
          ·
            refine ⟨19816369837000877956878053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13210913224667251971252035 19816369837000877956878053)
            ·
              refine ⟨3715569344437664616914635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19816369837000877956878053 3715569344437664616914635)
              ·
                refine ⟨5573354016656496925371953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715569344437664616914635 5573354016656496925371953)
                ·
                  refine ⟨4180015512492372694028965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5573354016656496925371953 4180015512492372694028965)
                  ·
                    refine ⟨783752908592319880130431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4180015512492372694028965 783752908592319880130431)
                    ·
                      rfl

theorem cell23_4579060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_4579060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579060 prefixEnd_4579060 := by exact prefixLift 4579060
  have htrace : WordTrace (prefixWord ++ tailWord_4579060) baseStart_4579060 baseEnd_4579060 := by
    simpa [prefixWord, tailWord_4579060, baseEnd_4579060] using wordTrace_append hprefix tailTrace_4579060
  have hstable : (prefixWord ++ tailWord_4579060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579060).length < 2 ^ (prefixWord ++ tailWord_4579060).sum := by decide
  have hdescent : baseEnd_4579060 < baseStart_4579060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579070 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_4579070 : Nat := 118140960795 + 4579070 * 2 ^ 59
def prefixEnd_4579070 : Nat := 4983230072969 + 3 ^ 40 * 4579070 * 2
def baseEnd_4579070 : Nat := 2351263860583504601266247

theorem tailTrace_4579070 : CollatzResearch.WordTrace tailWord_4579070 prefixEnd_4579070 2351263860583504601266247 := by
  unfold tailWord_4579070
  simp only [CollatzResearch.WordTrace]
  refine ⟨20876550440102363467436833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111341602347212605159663109 20876550440102363467436833)
  ·
    refine ⟨15657412830076772600577625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20876550440102363467436833 15657412830076772600577625)
    ·
      refine ⟨11743059622557579450433219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15657412830076772600577625 11743059622557579450433219)
      ·
        refine ⟨17614589433836369175649829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11743059622557579450433219 17614589433836369175649829)
        ·
          refine ⟨3302735518844319220434343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17614589433836369175649829 3302735518844319220434343)
          ·
            refine ⟨4954103278266478830651515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302735518844319220434343 4954103278266478830651515)
            ·
              refine ⟨7431154917399718245977273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4954103278266478830651515 7431154917399718245977273)
              ·
                refine ⟨5573366188049788684482955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7431154917399718245977273 5573366188049788684482955)
                ·
                  refine ⟨8360049282074683026724433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5573366188049788684482955 8360049282074683026724433)
                  ·
                    refine ⟨6270036961556012270043325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8360049282074683026724433 6270036961556012270043325)
                    ·
                      refine ⟨2351263860583504601266247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6270036961556012270043325 2351263860583504601266247)
                      ·
                        rfl

theorem cell23_4579070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_4579070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579070 prefixEnd_4579070 := by exact prefixLift 4579070
  have htrace : WordTrace (prefixWord ++ tailWord_4579070) baseStart_4579070 baseEnd_4579070 := by
    simpa [prefixWord, tailWord_4579070, baseEnd_4579070] using wordTrace_append hprefix tailTrace_4579070
  have hstable : (prefixWord ++ tailWord_4579070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579070).length < 2 ^ (prefixWord ++ tailWord_4579070).sum := by decide
  have hdescent : baseEnd_4579070 < baseStart_4579070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579076 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_4579076 : Nat := 118140960795 + 4579076 * 2 ^ 59
def prefixEnd_4579076 : Nat := 4983230072969 + 3 ^ 40 * 4579076 * 2
def baseEnd_4579076 : Nat := 2351266941467431577791219

theorem tailTrace_4579076 : CollatzResearch.WordTrace tailWord_4579076 prefixEnd_4579076 2351266941467431577791219 := by
  unfold tailWord_4579076
  simp only [CollatzResearch.WordTrace]
  refine ⟨83506311179398585382106541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111341748239198113842808721 83506311179398585382106541)
  ·
    refine ⟨31314866692274469518289953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83506311179398585382106541 31314866692274469518289953)
    ·
      refine ⟨23486150019205852138717465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31314866692274469518289953 23486150019205852138717465)
      ·
        refine ⟨17614612514404389104038099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23486150019205852138717465 17614612514404389104038099)
        ·
          refine ⟨26421918771606583656057149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17614612514404389104038099 26421918771606583656057149)
          ·
            refine ⟨9908219539352468871021431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26421918771606583656057149 9908219539352468871021431)
            ·
              refine ⟨14862329309028703306532147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9908219539352468871021431 14862329309028703306532147)
              ·
                refine ⟨22293493963543054959798221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14862329309028703306532147 22293493963543054959798221)
                ·
                  refine ⟨8360060236328645609924333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22293493963543054959798221 8360060236328645609924333)
                  ·
                    refine ⟨3135022588623242103721625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8360060236328645609924333 3135022588623242103721625)
                    ·
                      refine ⟨2351266941467431577791219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135022588623242103721625 2351266941467431577791219)
                      ·
                        rfl

theorem cell23_4579076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_4579076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579076 prefixEnd_4579076 := by exact prefixLift 4579076
  have htrace : WordTrace (prefixWord ++ tailWord_4579076) baseStart_4579076 baseEnd_4579076 := by
    simpa [prefixWord, tailWord_4579076, baseEnd_4579076] using wordTrace_append hprefix tailTrace_4579076
  have hstable : (prefixWord ++ tailWord_4579076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579076).length < 2 ^ (prefixWord ++ tailWord_4579076).sum := by decide
  have hdescent : baseEnd_4579076 < baseStart_4579076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579093 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 1, 3, 2]
def baseStart_4579093 : Nat := 118140960795 + 4579093 * 2 ^ 59
def prefixEnd_4579093 : Nat := 4983230072969 + 3 ^ 40 * 4579093 * 2
def baseEnd_4579093 : Nat := 2351275670638558011278641

theorem tailTrace_4579093 : CollatzResearch.WordTrace tailWord_4579093 prefixEnd_4579093 2351275670638558011278641 := by
  unfold tailWord_4579093
  simp only [CollatzResearch.WordTrace]
  refine ⟨167013242399735582667581933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111342161599823721778387955 167013242399735582667581933)
  ·
    refine ⟨62629965899900843500343225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167013242399735582667581933 62629965899900843500343225)
    ·
      refine ⟨46972474424925632625257419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62629965899900843500343225 46972474424925632625257419)
      ·
        refine ⟨70458711637388448937886129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46972474424925632625257419 70458711637388448937886129)
        ·
          refine ⟨52844033728041336703414597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70458711637388448937886129 52844033728041336703414597)
          ·
            refine ⟨9908256324007750631890237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52844033728041336703414597 9908256324007750631890237)
            ·
              refine ⟨3715596121502906486958839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9908256324007750631890237 3715596121502906486958839)
              ·
                refine ⟨5573394182254359730438259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715596121502906486958839 5573394182254359730438259)
                ·
                  refine ⟨8360091273381539595657389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5573394182254359730438259 8360091273381539595657389)
                  ·
                    refine ⟨3135034227518077348371521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8360091273381539595657389 3135034227518077348371521)
                    ·
                      refine ⟨2351275670638558011278641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135034227518077348371521 2351275670638558011278641)
                      ·
                        rfl

theorem cell23_4579093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_4579093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579093 prefixEnd_4579093 := by exact prefixLift 4579093
  have htrace : WordTrace (prefixWord ++ tailWord_4579093) baseStart_4579093 baseEnd_4579093 := by
    simpa [prefixWord, tailWord_4579093, baseEnd_4579093] using wordTrace_append hprefix tailTrace_4579093
  have hstable : (prefixWord ++ tailWord_4579093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579093).length < 2 ^ (prefixWord ++ tailWord_4579093).sum := by decide
  have hdescent : baseEnd_4579093 < baseStart_4579093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579199 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 3]
def baseStart_4579199 : Nat := 118140960795 + 4579199 * 2 ^ 59
def prefixEnd_4579199 : Nat := 4983230072969 + 3 ^ 40 * 4579199 * 2
def baseEnd_4579199 : Nat := 2351330099587934596553153

theorem tailTrace_4579199 : CollatzResearch.WordTrace tailWord_4579199 prefixEnd_4579199 2351330099587934596553153 := by
  unfold tailWord_4579199
  simp only [CollatzResearch.WordTrace]
  refine ⟨167017108537351562770940651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111344739024901041847293767 167017108537351562770940651)
  ·
    refine ⟨250525662806027344156410977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167017108537351562770940651 250525662806027344156410977)
    ·
      refine ⟨187894247104520508117308233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250525662806027344156410977 187894247104520508117308233)
      ·
        refine ⟨140920685328390381087981175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187894247104520508117308233 140920685328390381087981175)
        ·
          refine ⟨211381027992585571631971763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140920685328390381087981175 211381027992585571631971763)
          ·
            refine ⟨317071541988878357447957645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211381027992585571631971763 317071541988878357447957645)
            ·
              refine ⟨118901828245829384042984117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317071541988878357447957645 118901828245829384042984117)
              ·
                refine ⟨11147046398046504754029761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118901828245829384042984117 11147046398046504754029761)
                ·
                  refine ⟨8360284798534878565522321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11147046398046504754029761 8360284798534878565522321)
                  ·
                    refine ⟨6270213598901158924141741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8360284798534878565522321 6270213598901158924141741)
                    ·
                      refine ⟨2351330099587934596553153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6270213598901158924141741 2351330099587934596553153)
                      ·
                        rfl

theorem cell23_4579199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_4579199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579199 prefixEnd_4579199 := by exact prefixLift 4579199
  have htrace : WordTrace (prefixWord ++ tailWord_4579199) baseStart_4579199 baseEnd_4579199 := by
    simpa [prefixWord, tailWord_4579199, baseEnd_4579199] using wordTrace_append hprefix tailTrace_4579199
  have hstable : (prefixWord ++ tailWord_4579199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579199).length < 2 ^ (prefixWord ++ tailWord_4579199).sum := by decide
  have hdescent : baseEnd_4579199 < baseStart_4579199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579232 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 2, 9]
def baseStart_4579232 : Nat := 118140960795 + 4579232 * 2 ^ 59
def prefixEnd_4579232 : Nat := 4983230072969 + 3 ^ 40 * 4579232 * 2
def baseEnd_4579232 : Nat := 783782348149844322480167

theorem tailTrace_4579232 : CollatzResearch.WordTrace tailWord_4579232 prefixEnd_4579232 783782348149844322480167 := by
  unfold tailWord_4579232
  simp only [CollatzResearch.WordTrace]
  refine ⟨83509156073116004703445975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111345541430821339604594633 83509156073116004703445975)
  ·
    refine ⟨125263734109674007055168963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83509156073116004703445975 125263734109674007055168963)
    ·
      refine ⟨187895601164511010582753445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125263734109674007055168963 187895601164511010582753445)
      ·
        refine ⟨35230425218345814484266271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187895601164511010582753445 35230425218345814484266271)
        ·
          refine ⟨52845637827518721726399407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35230425218345814484266271 52845637827518721726399407)
          ·
            refine ⟨79268456741278082589599111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52845637827518721726399407 79268456741278082589599111)
            ·
              refine ⟨118902685111917123884398667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79268456741278082589599111 118902685111917123884398667)
              ·
                refine ⟨178354027667875685826598001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118902685111917123884398667 178354027667875685826598001)
                ·
                  refine ⟨133765520750906764369948501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178354027667875685826598001 133765520750906764369948501)
                  ·
                    refine ⟨783782348149844322480167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 133765520750906764369948501 783782348149844322480167)
                    ·
                      rfl

theorem cell23_4579232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_4579232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579232 prefixEnd_4579232 := by exact prefixLift 4579232
  have htrace : WordTrace (prefixWord ++ tailWord_4579232) baseStart_4579232 baseEnd_4579232 := by
    simpa [prefixWord, tailWord_4579232, baseEnd_4579232] using wordTrace_append hprefix tailTrace_4579232
  have hstable : (prefixWord ++ tailWord_4579232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579232).length < 2 ^ (prefixWord ++ tailWord_4579232).sum := by decide
  have hdescent : baseEnd_4579232 < baseStart_4579232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579236 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 6]
def baseStart_4579236 : Nat := 118140960795 + 4579236 * 2 ^ 59
def prefixEnd_4579236 : Nat := 4983230072969 + 3 ^ 40 * 4579236 * 2
def baseEnd_4579236 : Nat := 261261010930238994643387

theorem tailTrace_4579236 : CollatzResearch.WordTrace tailWord_4579236 prefixEnd_4579236 261261010930238994643387 := by
  unfold tailWord_4579236
  simp only [CollatzResearch.WordTrace]
  refine ⟨83509229019108759045018781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111345638692145012060025041 83509229019108759045018781)
  ·
    refine ⟨31315960882165784641882043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83509229019108759045018781 31315960882165784641882043)
    ·
      refine ⟨46973941323248676962823065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31315960882165784641882043 46973941323248676962823065)
      ·
        refine ⟨35230455992436507722117299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46973941323248676962823065 35230455992436507722117299)
        ·
          refine ⟨52845683988654761583175949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35230455992436507722117299 52845683988654761583175949)
          ·
            refine ⟨19817131495745535593690981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52845683988654761583175949 19817131495745535593690981)
            ·
              refine ⟨3715712155452287923817059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19817131495745535593690981 3715712155452287923817059)
              ·
                refine ⟨5573568233178431885725589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715712155452287923817059 5573568233178431885725589)
                ·
                  refine ⟨261261010930238994643387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5573568233178431885725589 261261010930238994643387)
                  ·
                    rfl

theorem cell23_4579236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_4579236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579236 prefixEnd_4579236 := by exact prefixLift 4579236
  have htrace : WordTrace (prefixWord ++ tailWord_4579236) baseStart_4579236 baseEnd_4579236 := by
    simpa [prefixWord, tailWord_4579236, baseEnd_4579236] using wordTrace_append hprefix tailTrace_4579236
  have hstable : (prefixWord ++ tailWord_4579236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579236).length < 2 ^ (prefixWord ++ tailWord_4579236).sum := by decide
  have hdescent : baseEnd_4579236 < baseStart_4579236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579263 : List Nat := [1, 1, 2, 2, 2, 1, 4, 5, 1, 1, 3]
def baseStart_4579263 : Nat := 118140960795 + 4579263 * 2 ^ 59
def prefixEnd_4579263 : Nat := 4983230072969 + 3 ^ 40 * 4579263 * 2
def baseEnd_4579263 : Nat := 2351362962349822346152859

theorem tailTrace_4579263 : CollatzResearch.WordTrace tailWord_4579263 prefixEnd_4579263 2351362962349822346152859 := by
  unfold tailWord_4579263
  simp only [CollatzResearch.WordTrace]
  refine ⟨167019442809119701701270443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111346295206079801134180295 167019442809119701701270443)
  ·
    refine ⟨250529164213679552551905665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167019442809119701701270443 250529164213679552551905665)
    ·
      refine ⟨187896873160259664413929249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250529164213679552551905665 187896873160259664413929249)
      ·
        refine ⟨140922654870194748310446937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187896873160259664413929249 140922654870194748310446937)
        ·
          refine ⟨105691991152646061232835203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140922654870194748310446937 105691991152646061232835203)
          ·
            refine ⟨158537986728969091849252805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105691991152646061232835203 158537986728969091849252805)
            ·
              refine ⟨29725872511681704721734901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158537986728969091849252805 29725872511681704721734901)
              ·
                refine ⟨2786800547970159817662647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29725872511681704721734901 2786800547970159817662647)
                ·
                  refine ⟨4180200821955239726493971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2786800547970159817662647 4180200821955239726493971)
                  ·
                    refine ⟨6270301232932859589740957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4180200821955239726493971 6270301232932859589740957)
                    ·
                      refine ⟨2351362962349822346152859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6270301232932859589740957 2351362962349822346152859)
                      ·
                        rfl

theorem cell23_4579263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 1, 1, 3].length) (baseStart_4579263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579263 prefixEnd_4579263 := by exact prefixLift 4579263
  have htrace : WordTrace (prefixWord ++ tailWord_4579263) baseStart_4579263 baseEnd_4579263 := by
    simpa [prefixWord, tailWord_4579263, baseEnd_4579263] using wordTrace_append hprefix tailTrace_4579263
  have hstable : (prefixWord ++ tailWord_4579263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579263).length < 2 ^ (prefixWord ++ tailWord_4579263).sum := by decide
  have hdescent : baseEnd_4579263 < baseStart_4579263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579280 : List Nat := [2, 1, 1, 1, 1, 2, 8, 2, 1, 1, 3]
def baseStart_4579280 : Nat := 118140960795 + 4579280 * 2 ^ 59
def prefixEnd_4579280 : Nat := 4983230072969 + 3 ^ 40 * 4579280 * 2
def baseEnd_4579280 : Nat := 2351371691520948779640281

theorem tailTrace_4579280 : CollatzResearch.WordTrace tailWord_4579280 prefixEnd_4579280 2351371691520948779640281 := by
  unfold tailWord_4579280
  simp only [CollatzResearch.WordTrace]
  refine ⟨83510031425029056802319647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111346708566705409069759529 83510031425029056802319647)
  ·
    refine ⟨125265047137543585203479471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83510031425029056802319647 125265047137543585203479471)
    ·
      refine ⟨187897570706315377805219207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125265047137543585203479471 187897570706315377805219207)
      ·
        refine ⟨281846356059473066707828811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187897570706315377805219207 281846356059473066707828811)
        ·
          refine ⟨422769534089209600061743217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281846356059473066707828811 422769534089209600061743217)
          ·
            refine ⟨317077150566907200046307413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422769534089209600061743217 317077150566907200046307413)
            ·
              refine ⟨3715747858205943750542665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 317077150566907200046307413 3715747858205943750542665)
              ·
                refine ⟨2786810893654457812906999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3715747858205943750542665 2786810893654457812906999)
                ·
                  refine ⟨4180216340481686719360499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2786810893654457812906999 4180216340481686719360499)
                  ·
                    refine ⟨6270324510722530079040749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4180216340481686719360499 6270324510722530079040749)
                    ·
                      refine ⟨2351371691520948779640281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6270324510722530079040749 2351371691520948779640281)
                      ·
                        rfl

theorem cell23_4579280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 1, 1, 3].length) (baseStart_4579280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579280 prefixEnd_4579280 := by exact prefixLift 4579280
  have htrace : WordTrace (prefixWord ++ tailWord_4579280) baseStart_4579280 baseEnd_4579280 := by
    simpa [prefixWord, tailWord_4579280, baseEnd_4579280] using wordTrace_append hprefix tailTrace_4579280
  have hstable : (prefixWord ++ tailWord_4579280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579280).length < 2 ^ (prefixWord ++ tailWord_4579280).sum := by decide
  have hdescent : baseEnd_4579280 < baseStart_4579280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579306 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_4579306 : Nat := 118140960795 + 4579306 * 2 ^ 59
def prefixEnd_4579306 : Nat := 4983230072969 + 3 ^ 40 * 4579306 * 2
def baseEnd_4579306 : Nat := 2351385042017965677915161

theorem tailTrace_4579306 : CollatzResearch.WordTrace tailWord_4579306 prefixEnd_4579306 2351385042017965677915161 := by
  unfold tailWord_4579306
  simp only [CollatzResearch.WordTrace]
  refine ⟨41755252786990980011271443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111347340765309280030057181 41755252786990980011271443)
  ·
    refine ⟨62632879180486470016907165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41755252786990980011271443 62632879180486470016907165)
    ·
      refine ⟨23487329692682426256340187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62632879180486470016907165 23487329692682426256340187)
      ·
        refine ⟨35230994539023639384510281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23487329692682426256340187 35230994539023639384510281)
        ·
          refine ⟨26423245904267729538382711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35230994539023639384510281 26423245904267729538382711)
          ·
            refine ⟨39634868856401594307574067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26423245904267729538382711 39634868856401594307574067)
            ·
              refine ⟨59452303284602391461361101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39634868856401594307574067 59452303284602391461361101)
              ·
                refine ⟨22294613731725896798010413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59452303284602391461361101 22294613731725896798010413)
                ·
                  refine ⟨8360480149397211299253905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22294613731725896798010413 8360480149397211299253905)
                  ·
                    refine ⟨6270360112047908474440429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8360480149397211299253905 6270360112047908474440429)
                    ·
                      refine ⟨2351385042017965677915161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6270360112047908474440429 2351385042017965677915161)
                      ·
                        rfl

theorem cell23_4579306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_4579306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579306 prefixEnd_4579306 := by exact prefixLift 4579306
  have htrace : WordTrace (prefixWord ++ tailWord_4579306) baseStart_4579306 baseEnd_4579306 := by
    simpa [prefixWord, tailWord_4579306, baseEnd_4579306] using wordTrace_append hprefix tailTrace_4579306
  have hstable : (prefixWord ++ tailWord_4579306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579306).length < 2 ^ (prefixWord ++ tailWord_4579306).sum := by decide
  have hdescent : baseEnd_4579306 < baseStart_4579306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579320 : List Nat := [2, 1, 2, 1, 1, 3, 3, 5, 1, 2, 2]
def baseStart_4579320 : Nat := 118140960795 + 4579320 * 2 ^ 59
def prefixEnd_4579320 : Nat := 4983230072969 + 3 ^ 40 * 4579320 * 2
def baseEnd_4579320 : Nat := 2351392230747128623140097

theorem tailTrace_4579320 : CollatzResearch.WordTrace tailWord_4579320 prefixEnd_4579320 2351392230747128623140097 := by
  unfold tailWord_4579320
  simp only [CollatzResearch.WordTrace]
  refine ⟨83510760884956600218047707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111347681179942133624063609 83510760884956600218047707)
  ·
    refine ⟨125266141327434900327071561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83510760884956600218047707 125266141327434900327071561)
    ·
      refine ⟨93949605995576175245303671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125266141327434900327071561 93949605995576175245303671)
      ·
        refine ⟨140924408993364262867955507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93949605995576175245303671 140924408993364262867955507)
        ·
          refine ⟨211386613490046394301933261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140924408993364262867955507 211386613490046394301933261)
          ·
            refine ⟨79269980058767397863224973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211386613490046394301933261 79269980058767397863224973)
            ·
              refine ⟨29726242522037774198709365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79269980058767397863224973 29726242522037774198709365)
              ·
                refine ⟨2786835236441041331129003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29726242522037774198709365 2786835236441041331129003)
                ·
                  refine ⟨4180252854661561996693505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2786835236441041331129003 4180252854661561996693505)
                  ·
                    refine ⟨3135189640996171497520129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4180252854661561996693505 3135189640996171497520129)
                    ·
                      refine ⟨2351392230747128623140097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135189640996171497520129 2351392230747128623140097)
                      ·
                        rfl

theorem cell23_4579320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 1, 2, 2].length) (baseStart_4579320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579320 prefixEnd_4579320 := by exact prefixLift 4579320
  have htrace : WordTrace (prefixWord ++ tailWord_4579320) baseStart_4579320 baseEnd_4579320 := by
    simpa [prefixWord, tailWord_4579320, baseEnd_4579320] using wordTrace_append hprefix tailTrace_4579320
  have hstable : (prefixWord ++ tailWord_4579320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579320).length < 2 ^ (prefixWord ++ tailWord_4579320).sum := by decide
  have hdescent : baseEnd_4579320 < baseStart_4579320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579323 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 1, 2, 3]
def baseStart_4579323 : Nat := 118140960795 + 4579323 * 2 ^ 59
def prefixEnd_4579323 : Nat := 4983230072969 + 3 ^ 40 * 4579323 * 2
def baseEnd_4579323 : Nat := 2351393771189092111402583

theorem tailTrace_4579323 : CollatzResearch.WordTrace tailWord_4579323 prefixEnd_4579323 2351393771189092111402583 := by
  unfold tailWord_4579323
  simp only [CollatzResearch.WordTrace]
  refine ⟨167021631188902331948454623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111347754125934887965636415 167021631188902331948454623)
  ·
    refine ⟨250532446783353497922681935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167021631188902331948454623 250532446783353497922681935)
    ·
      refine ⟨375798670175030246884022903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250532446783353497922681935 375798670175030246884022903)
      ·
        refine ⟨563698005262545370326034355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375798670175030246884022903 563698005262545370326034355)
        ·
          refine ⟨845547007893818055489051533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563698005262545370326034355 845547007893818055489051533)
          ·
            refine ⟨317080127960181770808394325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 845547007893818055489051533 317080127960181770808394325)
            ·
              refine ⟨3715782749533380126660871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 317080127960181770808394325 3715782749533380126660871)
              ·
                refine ⟨5573674124300070189991307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715782749533380126660871 5573674124300070189991307)
                ·
                  refine ⟨8360511186450105284986961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5573674124300070189991307 8360511186450105284986961)
                  ·
                    refine ⟨6270383389837578963740221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8360511186450105284986961 6270383389837578963740221)
                    ·
                      refine ⟨2351393771189092111402583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6270383389837578963740221 2351393771189092111402583)
                      ·
                        rfl

theorem cell23_4579323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 2, 3].length) (baseStart_4579323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579323 prefixEnd_4579323 := by exact prefixLift 4579323
  have htrace : WordTrace (prefixWord ++ tailWord_4579323) baseStart_4579323 baseEnd_4579323 := by
    simpa [prefixWord, tailWord_4579323, baseEnd_4579323] using wordTrace_append hprefix tailTrace_4579323
  have hstable : (prefixWord ++ tailWord_4579323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579323).length < 2 ^ (prefixWord ++ tailWord_4579323).sum := by decide
  have hdescent : baseEnd_4579323 < baseStart_4579323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579326 : List Nat := [4, 2, 2, 2, 1, 2, 10]
def baseStart_4579326 : Nat := 118140960795 + 4579326 * 2 ^ 59
def prefixEnd_4579326 : Nat := 4983230072969 + 3 ^ 40 * 4579326 * 2
def baseEnd_4579326 : Nat := 29029571748531550613149

theorem tailTrace_4579326 : CollatzResearch.WordTrace tailWord_4579326 prefixEnd_4579326 29029571748531550613149 := by
  unfold tailWord_4579326
  simp only [CollatzResearch.WordTrace]
  refine ⟨20877717575986432932601729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111347827071927642307209221 20877717575986432932601729)
  ·
    refine ⟨15658288181989824699451297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20877717575986432932601729 15658288181989824699451297)
    ·
      refine ⟨11743716136492368524588473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15658288181989824699451297 11743716136492368524588473)
      ·
        refine ⟨8807787102369276393441355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11743716136492368524588473 8807787102369276393441355)
        ·
          refine ⟨13211680653553914590162033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8807787102369276393441355 13211680653553914590162033)
          ·
            refine ⟨9908760490165435942621525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13211680653553914590162033 9908760490165435942621525)
            ·
              refine ⟨29029571748531550613149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9908760490165435942621525 29029571748531550613149)
              ·
                rfl

theorem cell23_4579326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 10].length) (baseStart_4579326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579326 prefixEnd_4579326 := by exact prefixLift 4579326
  have htrace : WordTrace (prefixWord ++ tailWord_4579326) baseStart_4579326 baseEnd_4579326 := by
    simpa [prefixWord, tailWord_4579326, baseEnd_4579326] using wordTrace_append hprefix tailTrace_4579326
  have hstable : (prefixWord ++ tailWord_4579326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579326).length < 2 ^ (prefixWord ++ tailWord_4579326).sum := by decide
  have hdescent : baseEnd_4579326 < baseStart_4579326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579379 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 5]
def baseStart_4579379 : Nat := 118140960795 + 4579379 * 2 ^ 59
def prefixEnd_4579379 : Nat := 4983230072969 + 3 ^ 40 * 4579379 * 2
def baseEnd_4579379 : Nat := 2351422526105743892302325

theorem tailTrace_4579379 : CollatzResearch.WordTrace tailWord_4579379 prefixEnd_4579379 2351422526105743892302325 := by
  unfold tailWord_4579379
  simp only [CollatzResearch.WordTrace]
  refine ⟨167023673676699453512493191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111349115784466302341662127 167023673676699453512493191)
  ·
    refine ⟨250535510515049180268739787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167023673676699453512493191 250535510515049180268739787)
    ·
      refine ⟨375803265772573770403109681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250535510515049180268739787 375803265772573770403109681)
      ·
        refine ⟨281852449329430327802332261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375803265772573770403109681 281852449329430327802332261)
        ·
          refine ⟨52847334249268186462937299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 281852449329430327802332261 52847334249268186462937299)
          ·
            refine ⟨79271001373902279694405949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52847334249268186462937299 79271001373902279694405949)
            ·
              refine ⟨29726625515213354885402231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79271001373902279694405949 29726625515213354885402231)
              ·
                refine ⟨44589938272820032328103347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29726625515213354885402231 44589938272820032328103347)
                ·
                  refine ⟨66884907409230048492155021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44589938272820032328103347 66884907409230048492155021)
                  ·
                    refine ⟨25081840278461268184558133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66884907409230048492155021 25081840278461268184558133)
                    ·
                      refine ⟨2351422526105743892302325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25081840278461268184558133 2351422526105743892302325)
                      ·
                        rfl

theorem cell23_4579379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_4579379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579379 prefixEnd_4579379 := by exact prefixLift 4579379
  have htrace : WordTrace (prefixWord ++ tailWord_4579379) baseStart_4579379 baseEnd_4579379 := by
    simpa [prefixWord, tailWord_4579379, baseEnd_4579379] using wordTrace_append hprefix tailTrace_4579379
  have hstable : (prefixWord ++ tailWord_4579379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579379).length < 2 ^ (prefixWord ++ tailWord_4579379).sum := by decide
  have hdescent : baseEnd_4579379 < baseStart_4579379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579414 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_4579414 : Nat := 118140960795 + 4579414 * 2 ^ 59
def prefixEnd_4579414 : Nat := 4983230072969 + 3 ^ 40 * 4579414 * 2
def baseEnd_4579414 : Nat := 2351440497928651255364665

theorem tailTrace_4579414 : CollatzResearch.WordTrace tailWord_4579414 prefixEnd_4579414 2351440497928651255364665 := by
  unfold tailWord_4579414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10439059389473290905626081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111349966821048436326678197 10439059389473290905626081)
  ·
    refine ⟨7829294542104968179219561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10439059389473290905626081 7829294542104968179219561)
    ·
      refine ⟨5871970906578726134414671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7829294542104968179219561 5871970906578726134414671)
      ·
        refine ⟨8807956359868089201622007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5871970906578726134414671 8807956359868089201622007)
        ·
          refine ⟨13211934539802133802433011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8807956359868089201622007 13211934539802133802433011)
          ·
            refine ⟨19817901809703200703649517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13211934539802133802433011 19817901809703200703649517)
            ·
              refine ⟨7431713178638700263868569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19817901809703200703649517 7431713178638700263868569)
              ·
                refine ⟨5573784883979025197901427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7431713178638700263868569 5573784883979025197901427)
                ·
                  refine ⟨8360677325968537796852141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5573784883979025197901427 8360677325968537796852141)
                  ·
                    refine ⟨3135253997238201673819553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8360677325968537796852141 3135253997238201673819553)
                    ·
                      refine ⟨2351440497928651255364665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135253997238201673819553 2351440497928651255364665)
                      ·
                        rfl

theorem cell23_4579414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_4579414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579414 prefixEnd_4579414 := by exact prefixLift 4579414
  have htrace : WordTrace (prefixWord ++ tailWord_4579414) baseStart_4579414 baseEnd_4579414 := by
    simpa [prefixWord, tailWord_4579414, baseEnd_4579414] using wordTrace_append hprefix tailTrace_4579414
  have hstable : (prefixWord ++ tailWord_4579414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579414).length < 2 ^ (prefixWord ++ tailWord_4579414).sum := by decide
  have hdescent : baseEnd_4579414 < baseStart_4579414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579453 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 2, 5, 2]
def baseStart_4579453 : Nat := 118140960795 + 4579453 * 2 ^ 59
def prefixEnd_4579453 : Nat := 4983230072969 + 3 ^ 40 * 4579453 * 2
def baseEnd_4579453 : Nat := 2351460523674176602776985

theorem tailTrace_4579453 : CollatzResearch.WordTrace tailWord_4579453 prefixEnd_4579453 2351460523674176602776985 := by
  unfold tailWord_4579453
  simp only [CollatzResearch.WordTrace]
  refine ⟨167026372678431364150687013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111350915118954242767124675 167026372678431364150687013)
  ·
    refine ⟨31317444877205880778253815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167026372678431364150687013 31317444877205880778253815)
    ·
      refine ⟨46976167315808821167380723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31317444877205880778253815 46976167315808821167380723)
      ·
        refine ⟨70464250973713231751071085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46976167315808821167380723 70464250973713231751071085)
        ·
          refine ⟨26424094115142461906651657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70464250973713231751071085 26424094115142461906651657)
          ·
            refine ⟨19818070586356846429988743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26424094115142461906651657 19818070586356846429988743)
            ·
              refine ⟨29727105879535269644983115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19818070586356846429988743 29727105879535269644983115)
              ·
                refine ⟨44590658819302904467474673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29727105879535269644983115 44590658819302904467474673)
                ·
                  refine ⟨33442994114477178350606005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44590658819302904467474673 33442994114477178350606005)
                  ·
                    refine ⟨3135280698232235470369313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33442994114477178350606005 3135280698232235470369313)
                    ·
                      refine ⟨2351460523674176602776985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135280698232235470369313 2351460523674176602776985)
                      ·
                        rfl

theorem cell23_4579453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_4579453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579453 prefixEnd_4579453 := by exact prefixLift 4579453
  have htrace : WordTrace (prefixWord ++ tailWord_4579453) baseStart_4579453 baseEnd_4579453 := by
    simpa [prefixWord, tailWord_4579453, baseEnd_4579453] using wordTrace_append hprefix tailTrace_4579453
  have hstable : (prefixWord ++ tailWord_4579453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579453).length < 2 ^ (prefixWord ++ tailWord_4579453).sum := by decide
  have hdescent : baseEnd_4579453 < baseStart_4579453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579480 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 2, 5]
def baseStart_4579480 : Nat := 118140960795 + 4579480 * 2 ^ 59
def prefixEnd_4579480 : Nat := 4983230072969 + 3 ^ 40 * 4579480 * 2
def baseEnd_4579480 : Nat := 783824795883949332379787

theorem tailTrace_4579480 : CollatzResearch.WordTrace tailWord_4579480 prefixEnd_4579480 783824795883949332379787 := by
  unfold tailWord_4579480
  simp only [CollatzResearch.WordTrace]
  refine ⟨83513678724666773880959947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111351571632889031841279929 83513678724666773880959947)
  ·
    refine ⟨125270518087000160821439921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83513678724666773880959947 125270518087000160821439921)
    ·
      refine ⟨93952888565250120616079941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125270518087000160821439921 93952888565250120616079941)
      ·
        refine ⟨17616166605984397615514989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93952888565250120616079941 17616166605984397615514989)
        ·
          refine ⟨6606062477244149105818121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17616166605984397615514989 6606062477244149105818121)
          ·
            refine ⟨4954546857933111829363591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6606062477244149105818121 4954546857933111829363591)
            ·
              refine ⟨7431820286899667744045387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4954546857933111829363591 7431820286899667744045387)
              ·
                refine ⟨11147730430349501616068081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7431820286899667744045387 11147730430349501616068081)
                ·
                  refine ⟨8360797822762126212051061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11147730430349501616068081 8360797822762126212051061)
                  ·
                    refine ⟨783824795883949332379787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8360797822762126212051061 783824795883949332379787)
                    ·
                      rfl

theorem cell23_4579480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_4579480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579480 prefixEnd_4579480 := by exact prefixLift 4579480
  have htrace : WordTrace (prefixWord ++ tailWord_4579480) baseStart_4579480 baseEnd_4579480 := by
    simpa [prefixWord, tailWord_4579480, baseEnd_4579480] using wordTrace_append hprefix tailTrace_4579480
  have hstable : (prefixWord ++ tailWord_4579480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579480).length < 2 ^ (prefixWord ++ tailWord_4579480).sum := by decide
  have hdescent : baseEnd_4579480 < baseStart_4579480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579506 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 8]
def baseStart_4579506 : Nat := 118140960795 + 4579506 * 2 ^ 59
def prefixEnd_4579506 : Nat := 4983230072969 + 3 ^ 40 * 4579506 * 2
def baseEnd_4579506 : Nat := 261276415349873877268249

theorem tailTrace_4579506 : CollatzResearch.WordTrace tailWord_4579506 prefixEnd_4579506 261276415349873877268249 := by
  unfold tailWord_4579506
  simp only [CollatzResearch.WordTrace]
  refine ⟨41757076436809838550591593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111352203831492902801577581 41757076436809838550591593)
  ·
    refine ⟨31317807327607378912943695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41757076436809838550591593 31317807327607378912943695)
    ·
      refine ⟨46976710991411068369415543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31317807327607378912943695 46976710991411068369415543)
      ·
        refine ⟨70465066487116602554123315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46976710991411068369415543 70465066487116602554123315)
        ·
          refine ⟨105697599730674903831184973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70465066487116602554123315 105697599730674903831184973)
          ·
            refine ⟨39636599899003088936694365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105697599730674903831184973 39636599899003088936694365)
            ·
              refine ⟨14863724962126158351260387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39636599899003088936694365 14863724962126158351260387)
              ·
                refine ⟨22295587443189237526890581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14863724962126158351260387 22295587443189237526890581)
                ·
                  refine ⟨261276415349873877268249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22295587443189237526890581 261276415349873877268249)
                  ·
                    rfl

theorem cell23_4579506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_4579506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579506 prefixEnd_4579506 := by exact prefixLift 4579506
  have htrace : WordTrace (prefixWord ++ tailWord_4579506) baseStart_4579506 baseEnd_4579506 := by
    simpa [prefixWord, tailWord_4579506, baseEnd_4579506] using wordTrace_append hprefix tailTrace_4579506
  have hstable : (prefixWord ++ tailWord_4579506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579506).length < 2 ^ (prefixWord ++ tailWord_4579506).sum := by decide
  have hdescent : baseEnd_4579506 < baseStart_4579506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579553 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 1, 5]
def baseStart_4579553 : Nat := 118140960795 + 4579553 * 2 ^ 59
def prefixEnd_4579553 : Nat := 4983230072969 + 3 ^ 40 * 4579553 * 2
def baseEnd_4579553 : Nat := 783837290579875403842175

theorem tailTrace_4579553 : CollatzResearch.WordTrace tailWord_4579553 prefixEnd_4579553 783837290579875403842175 := by
  unfold tailWord_4579553
  simp only [CollatzResearch.WordTrace]
  refine ⟨167030019978069081229327313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111353346652046054152884875 167030019978069081229327313)
  ·
    refine ⟨125272514983551810921995485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167030019978069081229327313 125272514983551810921995485)
    ·
      refine ⟨46977193118831929095748307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125272514983551810921995485 46977193118831929095748307)
      ·
        refine ⟨70465789678247893643622461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46977193118831929095748307 70465789678247893643622461)
        ·
          refine ⟨26424671129342960116358423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70465789678247893643622461 26424671129342960116358423)
          ·
            refine ⟨39637006694014440174537635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26424671129342960116358423 39637006694014440174537635)
            ·
              refine ⟨59455510041021660261806453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39637006694014440174537635 59455510041021660261806453)
              ·
                refine ⟨5573954066345780649544355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59455510041021660261806453 5573954066345780649544355)
                ·
                  refine ⟨8360931099518670974316533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5573954066345780649544355 8360931099518670974316533)
                  ·
                    refine ⟨783837290579875403842175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8360931099518670974316533 783837290579875403842175)
                    ·
                      rfl

theorem cell23_4579553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_4579553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579553 prefixEnd_4579553 := by exact prefixLift 4579553
  have htrace : WordTrace (prefixWord ++ tailWord_4579553) baseStart_4579553 baseEnd_4579553 := by
    simpa [prefixWord, tailWord_4579553, baseEnd_4579553] using wordTrace_append hprefix tailTrace_4579553
  have hstable : (prefixWord ++ tailWord_4579553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579553).length < 2 ^ (prefixWord ++ tailWord_4579553).sum := by decide
  have hdescent : baseEnd_4579553 < baseStart_4579553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579560 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_4579560 : Nat := 118140960795 + 4579560 * 2 ^ 59
def prefixEnd_4579560 : Nat := 4983230072969 + 3 ^ 40 * 4579560 * 2
def baseEnd_4579560 : Nat := 2351515466104207684138993

theorem tailTrace_4579560 : CollatzResearch.WordTrace tailWord_4579560 prefixEnd_4579560 2351515466104207684138993 := by
  unfold tailWord_4579560
  simp only [CollatzResearch.WordTrace]
  refine ⟨83515137644521860712416067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111353516859362480949888089 83515137644521860712416067)
  ·
    refine ⟨125272706466782791068624101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83515137644521860712416067 125272706466782791068624101)
    ·
      refine ⟨23488632462521773325367019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125272706466782791068624101 23488632462521773325367019)
      ·
        refine ⟨35232948693782659988050529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23488632462521773325367019 35232948693782659988050529)
        ·
          refine ⟨26424711520336994991037897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35232948693782659988050529 26424711520336994991037897)
          ·
            refine ⟨19818533640252746243278423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26424711520336994991037897 19818533640252746243278423)
            ·
              refine ⟨29727800460379119364917635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19818533640252746243278423 29727800460379119364917635)
              ·
                refine ⟨44591700690568679047376453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29727800460379119364917635 44591700690568679047376453)
                ·
                  refine ⟨8360943879481627321383085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44591700690568679047376453 8360943879481627321383085)
                  ·
                    refine ⟨3135353954805610245518657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8360943879481627321383085 3135353954805610245518657)
                    ·
                      refine ⟨2351515466104207684138993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135353954805610245518657 2351515466104207684138993)
                      ·
                        rfl

theorem cell23_4579560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_4579560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579560 prefixEnd_4579560 := by exact prefixLift 4579560
  have htrace : WordTrace (prefixWord ++ tailWord_4579560) baseStart_4579560 baseEnd_4579560 := by
    simpa [prefixWord, tailWord_4579560, baseEnd_4579560] using wordTrace_append hprefix tailTrace_4579560
  have hstable : (prefixWord ++ tailWord_4579560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579560).length < 2 ^ (prefixWord ++ tailWord_4579560).sum := by decide
  have hdescent : baseEnd_4579560 < baseStart_4579560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579567 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 3, 1, 3]
def baseStart_4579567 : Nat := 118140960795 + 4579567 * 2 ^ 59
def prefixEnd_4579567 : Nat := 4983230072969 + 3 ^ 40 * 4579567 * 2
def baseEnd_4579567 : Nat := 2351519060468789156751461

theorem tailTrace_4579567 : CollatzResearch.WordTrace tailWord_4579567 prefixEnd_4579567 2351519060468789156751461 := by
  unfold tailWord_4579567
  simp only [CollatzResearch.WordTrace]
  refine ⟨167030530600018361620336955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111353687066678907746891303 167030530600018361620336955)
  ·
    refine ⟨250545795900027542430505433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167030530600018361620336955 250545795900027542430505433)
    ·
      refine ⟨187909346925020656822879075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250545795900027542430505433 187909346925020656822879075)
      ·
        refine ⟨281864020387530985234318613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187909346925020656822879075 281864020387530985234318613)
        ·
          refine ⟨13212375955665514932858685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 281864020387530985234318613 13212375955665514932858685)
          ·
            refine ⟨4954640983374568099822007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13212375955665514932858685 4954640983374568099822007)
            ·
              refine ⟨7431961475061852149733011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4954640983374568099822007 7431961475061852149733011)
              ·
                refine ⟨11147942212592778224599517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7431961475061852149733011 11147942212592778224599517)
                ·
                  refine ⟨4180478329722291834224819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11147942212592778224599517 4180478329722291834224819)
                  ·
                    refine ⟨6270717494583437751337229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4180478329722291834224819 6270717494583437751337229)
                    ·
                      refine ⟨2351519060468789156751461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6270717494583437751337229 2351519060468789156751461)
                      ·
                        rfl

theorem cell23_4579567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 1, 3].length) (baseStart_4579567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579567 prefixEnd_4579567 := by exact prefixLift 4579567
  have htrace : WordTrace (prefixWord ++ tailWord_4579567) baseStart_4579567 baseEnd_4579567 := by
    simpa [prefixWord, tailWord_4579567, baseEnd_4579567] using wordTrace_append hprefix tailTrace_4579567
  have hstable : (prefixWord ++ tailWord_4579567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579567).length < 2 ^ (prefixWord ++ tailWord_4579567).sum := by decide
  have hdescent : baseEnd_4579567 < baseStart_4579567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579596 : List Nat := [2, 2, 1, 2, 2, 2, 1, 11]
def baseStart_4579596 : Nat := 118140960795 + 4579596 * 2 ^ 59
def prefixEnd_4579596 : Nat := 4983230072969 + 3 ^ 40 * 4579596 * 2
def baseEnd_4579596 : Nat := 87093850052139612714401

theorem tailTrace_4579596 : CollatzResearch.WordTrace tailWord_4579596 prefixEnd_4579596 87093850052139612714401 := by
  unfold tailWord_4579596
  simp only [CollatzResearch.WordTrace]
  refine ⟨83515794158456649786571321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111354392211275533048761761 83515794158456649786571321)
  ·
    refine ⟨62636845618842487339928491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83515794158456649786571321 62636845618842487339928491)
    ·
      refine ⟨93955268428263731009892737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62636845618842487339928491 93955268428263731009892737)
      ·
        refine ⟨70466451321197798257419553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93955268428263731009892737 70466451321197798257419553)
        ·
          refine ⟨52849838490898348693064665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70466451321197798257419553 52849838490898348693064665)
          ·
            refine ⟨39637378868173761519798499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52849838490898348693064665 39637378868173761519798499)
            ·
              refine ⟨59456068302260642279697749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39637378868173761519798499 59456068302260642279697749)
              ·
                refine ⟨87093850052139612714401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 59456068302260642279697749 87093850052139612714401)
                ·
                  rfl

theorem cell23_4579596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 11].length) (baseStart_4579596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579596 prefixEnd_4579596 := by exact prefixLift 4579596
  have htrace : WordTrace (prefixWord ++ tailWord_4579596) baseStart_4579596 baseEnd_4579596 := by
    simpa [prefixWord, tailWord_4579596, baseEnd_4579596] using wordTrace_append hprefix tailTrace_4579596
  have hstable : (prefixWord ++ tailWord_4579596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579596).length < 2 ^ (prefixWord ++ tailWord_4579596).sum := by decide
  have hdescent : baseEnd_4579596 < baseStart_4579596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579607 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 1, 1, 4]
def baseStart_4579607 : Nat := 118140960795 + 4579607 * 2 ^ 59
def prefixEnd_4579607 : Nat := 4983230072969 + 3 ^ 40 * 4579607 * 2
def baseEnd_4579607 : Nat := 2351539599694969000251277

theorem tailTrace_4579607 : CollatzResearch.WordTrace tailWord_4579607 prefixEnd_4579607 2351539599694969000251277 := by
  unfold tailWord_4579607
  simp only [CollatzResearch.WordTrace]
  refine ⟨167031989519873448451793075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111354659679915632301195383 167031989519873448451793075)
  ·
    refine ⟨250547984279810172677689613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167031989519873448451793075 250547984279810172677689613)
    ·
      refine ⟨93955494104928814754133605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250547984279810172677689613 93955494104928814754133605)
      ·
        refine ⟨17616655144674152766400051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93955494104928814754133605 17616655144674152766400051)
        ·
          refine ⟨26424982717011229149600077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17616655144674152766400051 26424982717011229149600077)
          ·
            refine ⟨9909368518879210931100029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26424982717011229149600077 9909368518879210931100029)
            ·
              refine ⟨3716013194579704099162511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9909368518879210931100029 3716013194579704099162511)
              ·
                refine ⟨5574019791869556148743767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3716013194579704099162511 5574019791869556148743767)
                ·
                  refine ⟨8361029687804334223115651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5574019791869556148743767 8361029687804334223115651)
                  ·
                    refine ⟨12541544531706501334673477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8361029687804334223115651 12541544531706501334673477)
                    ·
                      refine ⟨2351539599694969000251277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12541544531706501334673477 2351539599694969000251277)
                      ·
                        rfl

theorem cell23_4579607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_4579607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579607 prefixEnd_4579607 := by exact prefixLift 4579607
  have htrace : WordTrace (prefixWord ++ tailWord_4579607) baseStart_4579607 baseEnd_4579607 := by
    simpa [prefixWord, tailWord_4579607, baseEnd_4579607] using wordTrace_append hprefix tailTrace_4579607
  have hstable : (prefixWord ++ tailWord_4579607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579607).length < 2 ^ (prefixWord ++ tailWord_4579607).sum := by decide
  have hdescent : baseEnd_4579607 < baseStart_4579607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579613 : List Nat := [1, 4, 2, 3, 2, 11]
def baseStart_4579613 : Nat := 118140960795 + 4579613 * 2 ^ 59
def prefixEnd_4579613 : Nat := 4983230072969 + 3 ^ 40 * 4579613 * 2
def baseEnd_4579613 : Nat := 9677130372752658340643

theorem tailTrace_4579613 : CollatzResearch.WordTrace tailWord_4579613 prefixEnd_4579613 9677130372752658340643 := by
  unfold tailWord_4579613
  simp only [CollatzResearch.WordTrace]
  refine ⟨167032208357851711476511493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111354805571901140984340995 167032208357851711476511493)
  ·
    refine ⟨31318539067097195901845905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167032208357851711476511493 31318539067097195901845905)
    ·
      refine ⟨23488904300322896926384429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31318539067097195901845905 23488904300322896926384429)
      ·
        refine ⟨8808339112621086347394161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23488904300322896926384429 8808339112621086347394161)
        ·
          refine ⟨6606254334465814760545621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8808339112621086347394161 6606254334465814760545621)
          ·
            refine ⟨9677130372752658340643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6606254334465814760545621 9677130372752658340643)
            ·
              rfl

theorem cell23_4579613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 11].length) (baseStart_4579613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579613 prefixEnd_4579613 := by exact prefixLift 4579613
  have htrace : WordTrace (prefixWord ++ tailWord_4579613) baseStart_4579613 baseEnd_4579613 := by
    simpa [prefixWord, tailWord_4579613, baseEnd_4579613] using wordTrace_append hprefix tailTrace_4579613
  have hstable : (prefixWord ++ tailWord_4579613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579613).length < 2 ^ (prefixWord ++ tailWord_4579613).sum := by decide
  have hdescent : baseEnd_4579613 < baseStart_4579613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579690 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_4579690 : Nat := 118140960795 + 4579690 * 2 ^ 59
def prefixEnd_4579690 : Nat := 4983230072969 + 3 ^ 40 * 4579690 * 2
def baseEnd_4579690 : Nat := 783860739529764058504465

theorem tailTrace_4579690 : CollatzResearch.WordTrace tailWord_4579690 prefixEnd_4579690 783860739529764058504465 := by
  unfold tailWord_4579690
  simp only [CollatzResearch.WordTrace]
  refine ⟨41758754194643188406766131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111356677852381835751376349 41758754194643188406766131)
  ·
    refine ⟨62638131291964782610149197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41758754194643188406766131 62638131291964782610149197)
    ·
      refine ⟨23489299234486793478805949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62638131291964782610149197 23489299234486793478805949)
      ·
        refine ⟨8808487212932547554552231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23489299234486793478805949 8808487212932547554552231)
        ·
          refine ⟨13212730819398821331828347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8808487212932547554552231 13212730819398821331828347)
          ·
            refine ⟨19819096229098231997742521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13212730819398821331828347 19819096229098231997742521)
            ·
              refine ⟨14864322171823673998306891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19819096229098231997742521 14864322171823673998306891)
              ·
                refine ⟨22296483257735510997460337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14864322171823673998306891 22296483257735510997460337)
                ·
                  refine ⟨16722362443301633248095253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22296483257735510997460337 16722362443301633248095253)
                  ·
                    refine ⟨783860739529764058504465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16722362443301633248095253 783860739529764058504465)
                    ·
                      rfl

theorem cell23_4579690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_4579690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579690 prefixEnd_4579690 := by exact prefixLift 4579690
  have htrace : WordTrace (prefixWord ++ tailWord_4579690) baseStart_4579690 baseEnd_4579690 := by
    simpa [prefixWord, tailWord_4579690, baseEnd_4579690] using wordTrace_append hprefix tailTrace_4579690
  have hstable : (prefixWord ++ tailWord_4579690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579690).length < 2 ^ (prefixWord ++ tailWord_4579690).sum := by decide
  have hdescent : baseEnd_4579690 < baseStart_4579690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579737 : List Nat := [1, 2, 1, 2, 1, 4, 5, 2, 5]
def baseStart_4579737 : Nat := 118140960795 + 4579737 * 2 ^ 59
def prefixEnd_4579737 : Nat := 4983230072969 + 3 ^ 40 * 4579737 * 2
def baseEnd_4579737 : Nat := 261289594686672610180631

theorem tailTrace_4579737 : CollatzResearch.WordTrace tailWord_4579737 prefixEnd_4579737 261289594686672610180631 := by
  unfold tailWord_4579737
  simp only [CollatzResearch.WordTrace]
  refine ⟨167036731009402480654025465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111357820672934987102683643 167036731009402480654025465)
  ·
    refine ⟨125277548257051860490519099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167036731009402480654025465 125277548257051860490519099)
    ·
      refine ⟨187916322385577790735778649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125277548257051860490519099 187916322385577790735778649)
      ·
        refine ⟨140937241789183343051833987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187916322385577790735778649 140937241789183343051833987)
        ·
          refine ⟨211405862683775014577750981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140937241789183343051833987 211405862683775014577750981)
          ·
            refine ⟨39638599253207815233328309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211405862683775014577750981 39638599253207815233328309)
            ·
              refine ⟨3716118679988232678124529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39638599253207815233328309 3716118679988232678124529)
              ·
                refine ⟨2787089009991174508593397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3716118679988232678124529 2787089009991174508593397)
                ·
                  refine ⟨261289594686672610180631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2787089009991174508593397 261289594686672610180631)
                  ·
                    rfl

theorem cell23_4579737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 5].length) (baseStart_4579737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579737 prefixEnd_4579737 := by exact prefixLift 4579737
  have htrace : WordTrace (prefixWord ++ tailWord_4579737) baseStart_4579737 baseEnd_4579737 := by
    simpa [prefixWord, tailWord_4579737, baseEnd_4579737] using wordTrace_append hprefix tailTrace_4579737
  have hstable : (prefixWord ++ tailWord_4579737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579737).length < 2 ^ (prefixWord ++ tailWord_4579737).sum := by decide
  have hdescent : baseEnd_4579737 < baseStart_4579737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579753 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_4579753 : Nat := 118140960795 + 4579753 * 2 ^ 59
def prefixEnd_4579753 : Nat := 4983230072969 + 3 ^ 40 * 4579753 * 2
def baseEnd_4579753 : Nat := 2351614567870525429025605

theorem tailTrace_4579753 : CollatzResearch.WordTrace tailWord_4579753 prefixEnd_4579753 2351614567870525429025605 := by
  unfold tailWord_4579753
  simp only [CollatzResearch.WordTrace]
  refine ⟨167037314577344515386607913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111358209718229676924405275 167037314577344515386607913)
  ·
    refine ⟨125277985933008386539955935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167037314577344515386607913 125277985933008386539955935)
    ·
      refine ⟨187916978899512579809933903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125277985933008386539955935 187916978899512579809933903)
      ·
        refine ⟨281875468349268869714900855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187916978899512579809933903 281875468349268869714900855)
        ·
          refine ⟨422813202523903304572351283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281875468349268869714900855 422813202523903304572351283)
          ·
            refine ⟨634219803785854956858526925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422813202523903304572351283 634219803785854956858526925)
            ·
              refine ⟨237832426419695608821947597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 634219803785854956858526925 237832426419695608821947597)
              ·
                refine ⟨89187159907385853308230349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237832426419695608821947597 89187159907385853308230349)
                ·
                  refine ⟨33445184965269694990586381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89187159907385853308230349 33445184965269694990586381)
                  ·
                    refine ⟨12541944361976135621469893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33445184965269694990586381 12541944361976135621469893)
                    ·
                      refine ⟨2351614567870525429025605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12541944361976135621469893 2351614567870525429025605)
                      ·
                        rfl

theorem cell23_4579753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_4579753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579753 prefixEnd_4579753 := by exact prefixLift 4579753
  have htrace : WordTrace (prefixWord ++ tailWord_4579753) baseStart_4579753 baseEnd_4579753 := by
    simpa [prefixWord, tailWord_4579753, baseEnd_4579753] using wordTrace_append hprefix tailTrace_4579753
  have hstable : (prefixWord ++ tailWord_4579753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579753).length < 2 ^ (prefixWord ++ tailWord_4579753).sum := by decide
  have hdescent : baseEnd_4579753 < baseStart_4579753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579790 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_4579790 : Nat := 118140960795 + 4579790 * 2 ^ 59
def prefixEnd_4579790 : Nat := 4983230072969 + 3 ^ 40 * 4579790 * 2
def baseEnd_4579790 : Nat := 2351633566654741784262935

theorem tailTrace_4579790 : CollatzResearch.WordTrace tailWord_4579790 prefixEnd_4579790 2351633566654741784262935 := by
  unfold tailWord_4579790
  simp only [CollatzResearch.WordTrace]
  refine ⟨20879833009776308838213103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111359109385473647137136549 20879833009776308838213103)
  ·
    refine ⟨31319749514664463257319655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20879833009776308838213103 31319749514664463257319655)
    ·
      refine ⟨46979624271996694885979483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31319749514664463257319655 46979624271996694885979483)
      ·
        refine ⟨70469436407995042328969225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46979624271996694885979483 70469436407995042328969225)
        ·
          refine ⟨52852077305996281746726919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70469436407995042328969225 52852077305996281746726919)
          ·
            refine ⟨79278115958994422620090379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52852077305996281746726919 79278115958994422620090379)
            ·
              refine ⟨118917173938491633930135569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79278115958994422620090379 118917173938491633930135569)
              ·
                refine ⟨89187880453868725447601677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118917173938491633930135569 89187880453868725447601677)
                ·
                  refine ⟨33445455170200772042850629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89187880453868725447601677 33445455170200772042850629)
                  ·
                    refine ⟨6271022844412644758034493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33445455170200772042850629 6271022844412644758034493)
                    ·
                      refine ⟨2351633566654741784262935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6271022844412644758034493 2351633566654741784262935)
                      ·
                        rfl

theorem cell23_4579790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_4579790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579790 prefixEnd_4579790 := by exact prefixLift 4579790
  have htrace : WordTrace (prefixWord ++ tailWord_4579790) baseStart_4579790 baseEnd_4579790 := by
    simpa [prefixWord, tailWord_4579790, baseEnd_4579790] using wordTrace_append hprefix tailTrace_4579790
  have hstable : (prefixWord ++ tailWord_4579790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579790).length < 2 ^ (prefixWord ++ tailWord_4579790).sum := by decide
  have hdescent : baseEnd_4579790 < baseStart_4579790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579793 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 8]
def baseStart_4579793 : Nat := 118140960795 + 4579793 * 2 ^ 59
def prefixEnd_4579793 : Nat := 4983230072969 + 3 ^ 40 * 4579793 * 2
def baseEnd_4579793 : Nat := 261292789677411696947269

theorem tailTrace_4579793 : CollatzResearch.WordTrace tailWord_4579793 prefixEnd_4579793 261292789677411696947269 := by
  unfold tailWord_4579793
  simp only [CollatzResearch.WordTrace]
  refine ⟨167038773497199602218064033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111359182331466401478709355 167038773497199602218064033)
  ·
    refine ⟨125279080122899701663548025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167038773497199602218064033 125279080122899701663548025)
    ·
      refine ⟨93959310092174776247661019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125279080122899701663548025 93959310092174776247661019)
      ·
        refine ⟨140938965138262164371491529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93959310092174776247661019 140938965138262164371491529)
        ·
          refine ⟨105704223853696623278618647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140938965138262164371491529 105704223853696623278618647)
          ·
            refine ⟨158556335780544934917927971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105704223853696623278618647 158556335780544934917927971)
            ·
              refine ⟨237834503670817402376891957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158556335780544934917927971 237834503670817402376891957)
              ·
                refine ⟨22296984719139131472833621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 237834503670817402376891957 22296984719139131472833621)
                ·
                  refine ⟨261292789677411696947269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22296984719139131472833621 261292789677411696947269)
                  ·
                    rfl

theorem cell23_4579793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 8].length) (baseStart_4579793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579793 prefixEnd_4579793 := by exact prefixLift 4579793
  have htrace : WordTrace (prefixWord ++ tailWord_4579793) baseStart_4579793 baseEnd_4579793 := by
    simpa [prefixWord, tailWord_4579793, baseEnd_4579793] using wordTrace_append hprefix tailTrace_4579793
  have hstable : (prefixWord ++ tailWord_4579793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579793).length < 2 ^ (prefixWord ++ tailWord_4579793).sum := by decide
  have hdescent : baseEnd_4579793 < baseStart_4579793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579837 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_4579837 : Nat := 118140960795 + 4579837 * 2 ^ 59
def prefixEnd_4579837 : Nat := 4983230072969 + 3 ^ 40 * 4579837 * 2
def baseEnd_4579837 : Nat := 2351657700245503100375219

theorem tailTrace_4579837 : CollatzResearch.WordTrace tailWord_4579837 prefixEnd_4579837 2351657700245503100375219 := by
  unfold tailWord_4579837
  simp only [CollatzResearch.WordTrace]
  refine ⟨167040378309040197732665765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111360252206026798488443843 167040378309040197732665765)
  ·
    refine ⟨31320070932945037074874831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167040378309040197732665765 31320070932945037074874831)
    ·
      refine ⟨46980106399417555612312247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31320070932945037074874831 46980106399417555612312247)
      ·
        refine ⟨70470159599126333418468371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46980106399417555612312247 70470159599126333418468371)
        ·
          refine ⟨105705239398689500127702557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70470159599126333418468371 105705239398689500127702557)
          ·
            refine ⟨39639464774508562547888459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105705239398689500127702557 39639464774508562547888459)
            ·
              refine ⟨59459197161762843821832689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39639464774508562547888459 59459197161762843821832689)
              ·
                refine ⟨44594397871322132866374517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59459197161762843821832689 44594397871322132866374517)
                ·
                  refine ⟨4180724800436449956222611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44594397871322132866374517 4180724800436449956222611)
                  ·
                    refine ⟨6271087200654674934333917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4180724800436449956222611 6271087200654674934333917)
                    ·
                      refine ⟨2351657700245503100375219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6271087200654674934333917 2351657700245503100375219)
                      ·
                        rfl

theorem cell23_4579837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_4579837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579837 prefixEnd_4579837 := by exact prefixLift 4579837
  have htrace : WordTrace (prefixWord ++ tailWord_4579837) baseStart_4579837 baseEnd_4579837 := by
    simpa [prefixWord, tailWord_4579837, baseEnd_4579837] using wordTrace_append hprefix tailTrace_4579837
  have hstable : (prefixWord ++ tailWord_4579837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579837).length < 2 ^ (prefixWord ++ tailWord_4579837).sum := by decide
  have hdescent : baseEnd_4579837 < baseStart_4579837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579844 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 6]
def baseStart_4579844 : Nat := 118140960795 + 4579844 * 2 ^ 59
def prefixEnd_4579844 : Nat := 4983230072969 + 3 ^ 40 * 4579844 * 2
def baseEnd_4579844 : Nat := 261295699401120508109743

theorem tailTrace_4579844 : CollatzResearch.WordTrace tailWord_4579844 prefixEnd_4579844 261295699401120508109743 := by
  unfold tailWord_4579844
  simp only [CollatzResearch.WordTrace]
  refine ⟨83520316810007418964085293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111360422413343225285447057 83520316810007418964085293)
  ·
    refine ⟨31320118803752782111531985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83520316810007418964085293 31320118803752782111531985)
    ·
      refine ⟨23490089102814586583648989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31320118803752782111531985 23490089102814586583648989)
      ·
        refine ⟨8808783413555469968868371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23490089102814586583648989 8808783413555469968868371)
        ·
          refine ⟨13213175120333204953302557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8808783413555469968868371 13213175120333204953302557)
          ·
            refine ⟨4954940670124951857488459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13213175120333204953302557 4954940670124951857488459)
            ·
              refine ⟨7432411005187427786232689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4954940670124951857488459 7432411005187427786232689)
              ·
                refine ⟨5574308253890570839674517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7432411005187427786232689 5574308253890570839674517)
                ·
                  refine ⟨261295699401120508109743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5574308253890570839674517 261295699401120508109743)
                  ·
                    rfl

theorem cell23_4579844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_4579844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579844 prefixEnd_4579844 := by exact prefixLift 4579844
  have htrace : WordTrace (prefixWord ++ tailWord_4579844) baseStart_4579844 baseEnd_4579844 := by
    simpa [prefixWord, tailWord_4579844, baseEnd_4579844] using wordTrace_append hprefix tailTrace_4579844
  have hstable : (prefixWord ++ tailWord_4579844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579844).length < 2 ^ (prefixWord ++ tailWord_4579844).sum := by decide
  have hdescent : baseEnd_4579844 < baseStart_4579844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579854 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_4579854 : Nat := 118140960795 + 4579854 * 2 ^ 59
def prefixEnd_4579854 : Nat := 4983230072969 + 3 ^ 40 * 4579854 * 2
def baseEnd_4579854 : Nat := 2351666429416629533862641

theorem tailTrace_4579854 : CollatzResearch.WordTrace tailWord_4579854 prefixEnd_4579854 2351666429416629533862641 := by
  unfold tailWord_4579854
  simp only [CollatzResearch.WordTrace]
  refine ⟨20880124793747326204504327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111360665566652406424023077 20880124793747326204504327)
  ·
    refine ⟨31320187190620989306756491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20880124793747326204504327 31320187190620989306756491)
    ·
      refine ⟨46980280785931483960134737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31320187190620989306756491 46980280785931483960134737)
      ·
        refine ⟨35235210589448612970101053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46980280785931483960134737 35235210589448612970101053)
        ·
          refine ⟨13213203971043229863787895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35235210589448612970101053 13213203971043229863787895)
          ·
            refine ⟨19819805956564844795681843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13213203971043229863787895 19819805956564844795681843)
            ·
              refine ⟨29729708934847267193522765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19819805956564844795681843 29729708934847267193522765)
              ·
                refine ⟨11148640850567725197571037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29729708934847267193522765 11148640850567725197571037)
                ·
                  refine ⟨4180740318962896949089139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11148640850567725197571037 4180740318962896949089139)
                  ·
                    refine ⟨6271110478444345423633709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4180740318962896949089139 6271110478444345423633709)
                    ·
                      refine ⟨2351666429416629533862641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6271110478444345423633709 2351666429416629533862641)
                      ·
                        rfl

theorem cell23_4579854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_4579854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579854 prefixEnd_4579854 := by exact prefixLift 4579854
  have htrace : WordTrace (prefixWord ++ tailWord_4579854) baseStart_4579854 baseEnd_4579854 := by
    simpa [prefixWord, tailWord_4579854, baseEnd_4579854] using wordTrace_append hprefix tailTrace_4579854
  have hstable : (prefixWord ++ tailWord_4579854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579854).length < 2 ^ (prefixWord ++ tailWord_4579854).sum := by decide
  have hdescent : baseEnd_4579854 < baseStart_4579854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579877 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 4]
def baseStart_4579877 : Nat := 118140960795 + 4579877 * 2 ^ 59
def prefixEnd_4579877 : Nat := 4983230072969 + 3 ^ 40 * 4579877 * 2
def baseEnd_4579877 : Nat := 2351678239471682943875035

theorem tailTrace_4579877 : CollatzResearch.WordTrace tailWord_4579877 prefixEnd_4579877 2351678239471682943875035 := by
  unfold tailWord_4579877
  simp only [CollatzResearch.WordTrace]
  refine ⟨167041837228895284564121885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111361224819263523042747923 167041837228895284564121885)
  ·
    refine ⟨62640688960835731711545707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167041837228895284564121885 62640688960835731711545707)
    ·
      refine ⟨93961033441253597567318561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62640688960835731711545707 93961033441253597567318561)
      ·
        refine ⟨70470775080940198175488921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93961033441253597567318561 70470775080940198175488921)
        ·
          refine ⟨52853081310705148631616691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70470775080940198175488921 52853081310705148631616691)
          ·
            refine ⟨79279621966057722947425037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52853081310705148631616691 79279621966057722947425037)
            ·
              refine ⟨29729858237271646105284389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79279621966057722947425037 29729858237271646105284389)
              ·
                refine ⟨5574348419488433644740823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29729858237271646105284389 5574348419488433644740823)
                ·
                  refine ⟨8361522629232650467111235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5574348419488433644740823 8361522629232650467111235)
                  ·
                    refine ⟨12542283943848975700666853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8361522629232650467111235 12542283943848975700666853)
                    ·
                      refine ⟨2351678239471682943875035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12542283943848975700666853 2351678239471682943875035)
                      ·
                        rfl

theorem cell23_4579877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_4579877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579877 prefixEnd_4579877 := by exact prefixLift 4579877
  have htrace : WordTrace (prefixWord ++ tailWord_4579877) baseStart_4579877 baseEnd_4579877 := by
    simpa [prefixWord, tailWord_4579877, baseEnd_4579877] using wordTrace_append hprefix tailTrace_4579877
  have hstable : (prefixWord ++ tailWord_4579877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579877).length < 2 ^ (prefixWord ++ tailWord_4579877).sum := by decide
  have hdescent : baseEnd_4579877 < baseStart_4579877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579897 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 5]
def baseStart_4579897 : Nat := 118140960795 + 4579897 * 2 ^ 59
def prefixEnd_4579897 : Nat := 4983230072969 + 3 ^ 40 * 4579897 * 2
def baseEnd_4579897 : Nat := 2351688509084772865624943

theorem tailTrace_4579897 : CollatzResearch.WordTrace tailWord_4579897 prefixEnd_4579897 2351688509084772865624943 := by
  unfold tailWord_4579897
  simp only [CollatzResearch.WordTrace]
  refine ⟨167042566688822827979849945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111361711125881885319899963 167042566688822827979849945)
  ·
    refine ⟨125281925016617120984887459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167042566688822827979849945 125281925016617120984887459)
    ·
      refine ⟨187922887524925681477331189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125281925016617120984887459 187922887524925681477331189)
      ·
        refine ⟨17617770705461782638499799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187922887524925681477331189 17617770705461782638499799)
        ·
          refine ⟨26426656058192673957749699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17617770705461782638499799 26426656058192673957749699)
          ·
            refine ⟨39639984087289010936624549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26426656058192673957749699 39639984087289010936624549)
            ·
              refine ⟨7432497016366689550617103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39639984087289010936624549 7432497016366689550617103)
              ·
                refine ⟨11148745524550034325925655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7432497016366689550617103 11148745524550034325925655)
                ·
                  refine ⟨16723118286825051488888483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11148745524550034325925655 16723118286825051488888483)
                  ·
                    refine ⟨25084677430237577233332725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16723118286825051488888483 25084677430237577233332725)
                    ·
                      refine ⟨2351688509084772865624943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25084677430237577233332725 2351688509084772865624943)
                      ·
                        rfl

theorem cell23_4579897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_4579897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579897 prefixEnd_4579897 := by exact prefixLift 4579897
  have htrace : WordTrace (prefixWord ++ tailWord_4579897) baseStart_4579897 baseEnd_4579897 := by
    simpa [prefixWord, tailWord_4579897, baseEnd_4579897] using wordTrace_append hprefix tailTrace_4579897
  have hstable : (prefixWord ++ tailWord_4579897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579897).length < 2 ^ (prefixWord ++ tailWord_4579897).sum := by decide
  have hdescent : baseEnd_4579897 < baseStart_4579897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579900 : List Nat := [2, 2, 2, 2, 3, 1, 11]
def baseStart_4579900 : Nat := 118140960795 + 4579900 * 2 ^ 59
def prefixEnd_4579900 : Nat := 4983230072969 + 3 ^ 40 * 4579900 * 2
def baseEnd_4579900 : Nat := 29033210487984399430709

theorem tailTrace_4579900 : CollatzResearch.WordTrace tailWord_4579900 prefixEnd_4579900 29033210487984399430709 := by
  unfold tailWord_4579900
  simp only [CollatzResearch.WordTrace]
  refine ⟨83521338053905979746104577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111361784071874639661472769 83521338053905979746104577)
  ·
    refine ⟨62641003540429484809578433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83521338053905979746104577 62641003540429484809578433)
    ·
      refine ⟨46980752655322113607183825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62641003540429484809578433 46980752655322113607183825)
      ·
        refine ⟨35235564491491585205387869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46980752655322113607183825 35235564491491585205387869)
        ·
          refine ⟨13213336684309344452020451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35235564491491585205387869 13213336684309344452020451)
          ·
            refine ⟨19820005026464016678030677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13213336684309344452020451 19820005026464016678030677)
            ·
              refine ⟨29033210487984399430709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19820005026464016678030677 29033210487984399430709)
              ·
                rfl

theorem cell23_4579900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 11].length) (baseStart_4579900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579900 prefixEnd_4579900 := by exact prefixLift 4579900
  have htrace : WordTrace (prefixWord ++ tailWord_4579900) baseStart_4579900 baseEnd_4579900 := by
    simpa [prefixWord, tailWord_4579900, baseEnd_4579900] using wordTrace_append hprefix tailTrace_4579900
  have hstable : (prefixWord ++ tailWord_4579900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579900).length < 2 ^ (prefixWord ++ tailWord_4579900).sum := by decide
  have hdescent : baseEnd_4579900 < baseStart_4579900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579911 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 3, 2, 2]
def baseStart_4579911 : Nat := 118140960795 + 4579911 * 2 ^ 59
def prefixEnd_4579911 : Nat := 4983230072969 + 3 ^ 40 * 4579911 * 2
def baseEnd_4579911 : Nat := 2351695697813935810849879

theorem tailTrace_4579911 : CollatzResearch.WordTrace tailWord_4579911 prefixEnd_4579911 2351695697813935810849879 := by
  unfold tailWord_4579911
  simp only [CollatzResearch.WordTrace]
  refine ⟨167043077310772108370859587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111362051540514738913906391 167043077310772108370859587)
  ·
    refine ⟨250564615966158162556289381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167043077310772108370859587 250564615966158162556289381)
    ·
      refine ⟨46980865493654655479304259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250564615966158162556289381 46980865493654655479304259)
      ·
        refine ⟨70471298240481983218956389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46980865493654655479304259 70471298240481983218956389)
        ·
          refine ⟨13213368420090371853554323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70471298240481983218956389 13213368420090371853554323)
          ·
            refine ⟨19820052630135557780331485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13213368420090371853554323 19820052630135557780331485)
            ·
              refine ⟨7432519736300834167624307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19820052630135557780331485 7432519736300834167624307)
              ·
                refine ⟨11148779604451251251436461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7432519736300834167624307 11148779604451251251436461)
                ·
                  refine ⟨4180792351669219219288673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11148779604451251251436461 4180792351669219219288673)
                  ·
                    refine ⟨3135594263751914414466505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4180792351669219219288673 3135594263751914414466505)
                    ·
                      refine ⟨2351695697813935810849879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135594263751914414466505 2351695697813935810849879)
                      ·
                        rfl

theorem cell23_4579911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_4579911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579911 prefixEnd_4579911 := by exact prefixLift 4579911
  have htrace : WordTrace (prefixWord ++ tailWord_4579911) baseStart_4579911 baseEnd_4579911 := by
    simpa [prefixWord, tailWord_4579911, baseEnd_4579911] using wordTrace_append hprefix tailTrace_4579911
  have hstable : (prefixWord ++ tailWord_4579911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579911).length < 2 ^ (prefixWord ++ tailWord_4579911).sum := by decide
  have hdescent : baseEnd_4579911 < baseStart_4579911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579917 : List Nat := [1, 6, 1, 1, 2, 1, 1, 10]
def baseStart_4579917 : Nat := 118140960795 + 4579917 * 2 ^ 59
def prefixEnd_4579917 : Nat := 4983230072969 + 3 ^ 40 * 4579917 * 2
def baseEnd_4579917 : Nat := 87099954766587510643513

theorem tailTrace_4579917 : CollatzResearch.WordTrace tailWord_4579917 prefixEnd_4579917 87099954766587510643513 := by
  unfold tailWord_4579917
  simp only [CollatzResearch.WordTrace]
  refine ⟨167043296148750371395578005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111362197432500247597052003 167043296148750371395578005)
  ·
    refine ⟨7830154506972673659167719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 167043296148750371395578005 7830154506972673659167719)
    ·
      refine ⟨11745231760459010488751579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7830154506972673659167719 11745231760459010488751579)
      ·
        refine ⟨17617847640688515733127369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11745231760459010488751579 17617847640688515733127369)
        ·
          refine ⟨13213385730516386799845527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17617847640688515733127369 13213385730516386799845527)
          ·
            refine ⟨19820078595774580199768291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13213385730516386799845527 19820078595774580199768291)
            ·
              refine ⟨29730117893661870299652437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19820078595774580199768291 29730117893661870299652437)
              ·
                refine ⟨87099954766587510643513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29730117893661870299652437 87099954766587510643513)
                ·
                  rfl

theorem cell23_4579917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 10].length) (baseStart_4579917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579917 prefixEnd_4579917 := by exact prefixLift 4579917
  have htrace : WordTrace (prefixWord ++ tailWord_4579917) baseStart_4579917 baseEnd_4579917 := by
    simpa [prefixWord, tailWord_4579917, baseEnd_4579917] using wordTrace_append hprefix tailTrace_4579917
  have hstable : (prefixWord ++ tailWord_4579917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579917).length < 2 ^ (prefixWord ++ tailWord_4579917).sum := by decide
  have hdescent : baseEnd_4579917 < baseStart_4579917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579921 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 2, 4]
def baseStart_4579921 : Nat := 118140960795 + 4579921 * 2 ^ 59
def prefixEnd_4579921 : Nat := 4983230072969 + 3 ^ 40 * 4579921 * 2
def baseEnd_4579921 : Nat := 783900277540160257241611

theorem tailTrace_4579921 : CollatzResearch.WordTrace tailWord_4579921 prefixEnd_4579921 783900277540160257241611 := by
  unfold tailWord_4579921
  simp only [CollatzResearch.WordTrace]
  refine ⟨167043442040735880078723617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111362294693823920052482411 167043442040735880078723617)
  ·
    refine ⟨125282581530551910059042713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167043442040735880078723617 125282581530551910059042713)
    ·
      refine ⟨93961936147913932544282035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125282581530551910059042713 93961936147913932544282035)
      ·
        refine ⟨140942904221870898816423053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93961936147913932544282035 140942904221870898816423053)
        ·
          refine ⟨52853589083201587056158645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140942904221870898816423053 52853589083201587056158645)
          ·
            refine ⟨4955023976550148786514873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52853589083201587056158645 4955023976550148786514873)
            ·
              refine ⟨3716267982412611589886155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4955023976550148786514873 3716267982412611589886155)
              ·
                refine ⟨5574401973618917384829233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3716267982412611589886155 5574401973618917384829233)
                ·
                  refine ⟨4180801480214188038621925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5574401973618917384829233 4180801480214188038621925)
                  ·
                    refine ⟨783900277540160257241611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4180801480214188038621925 783900277540160257241611)
                    ·
                      rfl

theorem cell23_4579921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_4579921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579921 prefixEnd_4579921 := by exact prefixLift 4579921
  have htrace : WordTrace (prefixWord ++ tailWord_4579921) baseStart_4579921 baseEnd_4579921 := by
    simpa [prefixWord, tailWord_4579921, baseEnd_4579921] using wordTrace_append hprefix tailTrace_4579921
  have hstable : (prefixWord ++ tailWord_4579921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579921).length < 2 ^ (prefixWord ++ tailWord_4579921).sum := by decide
  have hdescent : baseEnd_4579921 < baseStart_4579921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579927 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 3]
def baseStart_4579927 : Nat := 118140960795 + 4579927 * 2 ^ 59
def prefixEnd_4579927 : Nat := 4983230072969 + 3 ^ 40 * 4579927 * 2
def baseEnd_4579927 : Nat := 2351703913504407748249805

theorem tailTrace_4579927 : CollatzResearch.WordTrace tailWord_4579927 prefixEnd_4579927 2351703913504407748249805 := by
  unfold tailWord_4579927
  simp only [CollatzResearch.WordTrace]
  refine ⟨167043660878714143103442035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111362440585809428735628023 167043660878714143103442035)
  ·
    refine ⟨250565491318071214655163053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167043660878714143103442035 250565491318071214655163053)
    ·
      refine ⟨93962059244276705495686145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250565491318071214655163053 93962059244276705495686145)
      ·
        refine ⟨70471544433207529121764609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93962059244276705495686145 70471544433207529121764609)
        ·
          refine ⟨52853658324905646841323457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70471544433207529121764609 52853658324905646841323457)
          ·
            refine ⟨39640243743679235130992593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52853658324905646841323457 39640243743679235130992593)
            ·
              refine ⟨29730182807759426348244445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39640243743679235130992593 29730182807759426348244445)
              ·
                refine ⟨11148818552909784880591667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29730182807759426348244445 11148818552909784880591667)
                ·
                  refine ⟨16723227829364677320887501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11148818552909784880591667 16723227829364677320887501)
                  ·
                    refine ⟨6271210436011753995332813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16723227829364677320887501 6271210436011753995332813)
                    ·
                      refine ⟨2351703913504407748249805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6271210436011753995332813 2351703913504407748249805)
                      ·
                        rfl

theorem cell23_4579927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_4579927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579927 prefixEnd_4579927 := by exact prefixLift 4579927
  have htrace : WordTrace (prefixWord ++ tailWord_4579927) baseStart_4579927 baseEnd_4579927 := by
    simpa [prefixWord, tailWord_4579927, baseEnd_4579927] using wordTrace_append hprefix tailTrace_4579927
  have hstable : (prefixWord ++ tailWord_4579927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579927).length < 2 ^ (prefixWord ++ tailWord_4579927).sum := by decide
  have hdescent : baseEnd_4579927 < baseStart_4579927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579960 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 4, 6]
def baseStart_4579960 : Nat := 118140960795 + 4579960 * 2 ^ 59
def prefixEnd_4579960 : Nat := 4983230072969 + 3 ^ 40 * 4579960 * 2
def baseEnd_4579960 : Nat := 783906952788668706379051

theorem tailTrace_4579960 : CollatzResearch.WordTrace tailWord_4579960 prefixEnd_4579960 783906952788668706379051 := by
  unfold tailWord_4579960
  simp only [CollatzResearch.WordTrace]
  refine ⟨83522432243797294869696667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111363242991729726492928889 83522432243797294869696667)
  ·
    refine ⟨125283648365695942304545001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83522432243797294869696667 125283648365695942304545001)
    ·
      refine ⟨93962736274271956728408751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125283648365695942304545001 93962736274271956728408751)
      ·
        refine ⟨140944104411407935092613127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93962736274271956728408751 140944104411407935092613127)
        ·
          refine ⟨211416156617111902638919691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140944104411407935092613127 211416156617111902638919691)
          ·
            refine ⟨317124234925667853958379537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211416156617111902638919691 317124234925667853958379537)
            ·
              refine ⟨237843176194250890468784653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317124234925667853958379537 237843176194250890468784653)
              ·
                refine ⟨89191191072844083925794245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237843176194250890468784653 89191191072844083925794245)
                ·
                  refine ⟨16723348326158265736086421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89191191072844083925794245 16723348326158265736086421)
                  ·
                    refine ⟨783906952788668706379051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16723348326158265736086421 783906952788668706379051)
                    ·
                      rfl

theorem cell23_4579960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_4579960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579960 prefixEnd_4579960 := by exact prefixLift 4579960
  have htrace : WordTrace (prefixWord ++ tailWord_4579960) baseStart_4579960 baseEnd_4579960 := by
    simpa [prefixWord, tailWord_4579960, baseEnd_4579960] using wordTrace_append hprefix tailTrace_4579960
  have hstable : (prefixWord ++ tailWord_4579960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579960).length < 2 ^ (prefixWord ++ tailWord_4579960).sum := by decide
  have hdescent : baseEnd_4579960 < baseStart_4579960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579961 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 3]
def baseStart_4579961 : Nat := 118140960795 + 4579961 * 2 ^ 59
def prefixEnd_4579961 : Nat := 4983230072969 + 3 ^ 40 * 4579961 * 2
def baseEnd_4579961 : Nat := 2351721371846660615224649

theorem tailTrace_4579961 : CollatzResearch.WordTrace tailWord_4579961 prefixEnd_4579961 2351721371846660615224649 := by
  unfold tailWord_4579961
  simp only [CollatzResearch.WordTrace]
  refine ⟨167044900960590966910179737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111363267307060644606786491 167044900960590966910179737)
  ·
    refine ⟨125283675720443225182634803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167044900960590966910179737 125283675720443225182634803)
    ·
      refine ⟨187925513580664837773952205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125283675720443225182634803 187925513580664837773952205)
      ·
        refine ⟨70472067592749314165232077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187925513580664837773952205 70472067592749314165232077)
        ·
          refine ⟨26427025347280992811962029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70472067592749314165232077 26427025347280992811962029)
          ·
            refine ⟨9910134505230372304485761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26427025347280992811962029 9910134505230372304485761)
            ·
              refine ⟨7432600878922779228364321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9910134505230372304485761 7432600878922779228364321)
              ·
                refine ⟨5574450659192084421273241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7432600878922779228364321 5574450659192084421273241)
                ·
                  refine ⟨4180837994394063315954931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5574450659192084421273241 4180837994394063315954931)
                  ·
                    refine ⟨6271256991591094973932397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4180837994394063315954931 6271256991591094973932397)
                    ·
                      refine ⟨2351721371846660615224649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6271256991591094973932397 2351721371846660615224649)
                      ·
                        rfl

theorem cell23_4579961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_4579961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579961 prefixEnd_4579961 := by exact prefixLift 4579961
  have htrace : WordTrace (prefixWord ++ tailWord_4579961) baseStart_4579961 baseEnd_4579961 := by
    simpa [prefixWord, tailWord_4579961, baseEnd_4579961] using wordTrace_append hprefix tailTrace_4579961
  have hstable : (prefixWord ++ tailWord_4579961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579961).length < 2 ^ (prefixWord ++ tailWord_4579961).sum := by decide
  have hdescent : baseEnd_4579961 < baseStart_4579961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4579984 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 8, 2, 2]
def baseStart_4579984 : Nat := 118140960795 + 4579984 * 2 ^ 59
def prefixEnd_4579984 : Nat := 4983230072969 + 3 ^ 40 * 4579984 * 2
def baseEnd_4579984 : Nat := 2351733181901714025237043

theorem tailTrace_4579984 : CollatzResearch.WordTrace tailWord_4579984 prefixEnd_4579984 2351733181901714025237043 := by
  unfold tailWord_4579984
  simp only [CollatzResearch.WordTrace]
  refine ⟨83522869919753820919133503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111363826559671761225511337 83522869919753820919133503)
  ·
    refine ⟨125284304879630731378700255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83522869919753820919133503 125284304879630731378700255)
    ·
      refine ⟨187926457319446097068050383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125284304879630731378700255 187926457319446097068050383)
      ·
        refine ⟨281889685979169145602075575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187926457319446097068050383 281889685979169145602075575)
        ·
          refine ⟨422834528968753718403113363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281889685979169145602075575 422834528968753718403113363)
          ·
            refine ⟨634251793453130577604670045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422834528968753718403113363 634251793453130577604670045)
            ·
              refine ⟨237844422544923966601751267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 634251793453130577604670045 237844422544923966601751267)
              ·
                refine ⟨356766633817385949902626901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237844422544923966601751267 356766633817385949902626901)
                ·
                  refine ⟨4180858990047491600421409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 356766633817385949902626901 4180858990047491600421409)
                  ·
                    refine ⟨3135644242535618700316057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4180858990047491600421409 3135644242535618700316057)
                    ·
                      refine ⟨2351733181901714025237043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135644242535618700316057 2351733181901714025237043)
                      ·
                        rfl

theorem cell23_4579984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8, 2, 2].length) (baseStart_4579984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4579984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4579984 prefixEnd_4579984 := by exact prefixLift 4579984
  have htrace : WordTrace (prefixWord ++ tailWord_4579984) baseStart_4579984 baseEnd_4579984 := by
    simpa [prefixWord, tailWord_4579984, baseEnd_4579984] using wordTrace_append hprefix tailTrace_4579984
  have hstable : (prefixWord ++ tailWord_4579984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4579984).length < 2 ^ (prefixWord ++ tailWord_4579984).sum := by decide
  have hdescent : baseEnd_4579984 < baseStart_4579984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4579984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580057 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_4580057 : Nat := 118140960795 + 4580057 * 2 ^ 59
def prefixEnd_4580057 : Nat := 4983230072969 + 3 ^ 40 * 4580057 * 2
def baseEnd_4580057 : Nat := 2351770665989492239624207

theorem tailTrace_4580057 : CollatzResearch.WordTrace tailWord_4580057 prefixEnd_4580057 2351770665989492239624207 := by
  unfold tailWord_4580057
  simp only [CollatzResearch.WordTrace]
  refine ⟨167048402368243175305674425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111365601578828783537116283 167048402368243175305674425)
  ·
    refine ⟨125286301776182381479255819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167048402368243175305674425 125286301776182381479255819)
    ·
      refine ⟨187929452664273572218883729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125286301776182381479255819 187929452664273572218883729)
      ·
        refine ⟨140947089498205179164162797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187929452664273572218883729 140947089498205179164162797)
        ·
          refine ⟨52855158561826942186561049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140947089498205179164162797 52855158561826942186561049)
          ·
            refine ⟨39641368921370206639920787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52855158561826942186561049 39641368921370206639920787)
            ·
              refine ⟨59462053382055309959881181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39641368921370206639920787 59462053382055309959881181)
              ·
                refine ⟨22298270018270741234955443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59462053382055309959881181 22298270018270741234955443)
                ·
                  refine ⟨33447405027406111852433165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22298270018270741234955443 33447405027406111852433165)
                  ·
                    refine ⟨12542776885277291944662437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33447405027406111852433165 12542776885277291944662437)
                    ·
                      refine ⟨2351770665989492239624207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12542776885277291944662437 2351770665989492239624207)
                      ·
                        rfl

theorem cell23_4580057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_4580057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580057 prefixEnd_4580057 := by exact prefixLift 4580057
  have htrace : WordTrace (prefixWord ++ tailWord_4580057) baseStart_4580057 baseEnd_4580057 := by
    simpa [prefixWord, tailWord_4580057, baseEnd_4580057] using wordTrace_append hprefix tailTrace_4580057
  have hstable : (prefixWord ++ tailWord_4580057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580057).length < 2 ^ (prefixWord ++ tailWord_4580057).sum := by decide
  have hdescent : baseEnd_4580057 < baseStart_4580057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580181 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_4580181 : Nat := 118140960795 + 4580181 * 2 ^ 59
def prefixEnd_4580181 : Nat := 4983230072969 + 3 ^ 40 * 4580181 * 2
def baseEnd_4580181 : Nat := 2351834337590649754473637

theorem tailTrace_4580181 : CollatzResearch.WordTrace tailWord_4580181 prefixEnd_4580181 2351834337590649754473637 := by
  unfold tailWord_4580181
  simp only [CollatzResearch.WordTrace]
  refine ⟨167052925019793944483188397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111368616679862629655458931 167052925019793944483188397)
  ·
    refine ⟨62644846882422729181195649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167052925019793944483188397 62644846882422729181195649)
    ·
      refine ⟨46983635161817046885896737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62644846882422729181195649 46983635161817046885896737)
      ·
        refine ⟨35237726371362785164422553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46983635161817046885896737 35237726371362785164422553)
        ·
          refine ⟨26428294778522088873316915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35237726371362785164422553 26428294778522088873316915)
          ·
            refine ⟨39642442167783133309975373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26428294778522088873316915 39642442167783133309975373)
            ·
              refine ⟨14865915812918674991240765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39642442167783133309975373 14865915812918674991240765)
              ·
                refine ⟨5574718429844503121715287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14865915812918674991240765 5574718429844503121715287)
                ·
                  refine ⟨8362077644766754682572931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5574718429844503121715287 8362077644766754682572931)
                  ·
                    refine ⟨12543116467150132023859397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8362077644766754682572931 12543116467150132023859397)
                    ·
                      refine ⟨2351834337590649754473637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12543116467150132023859397 2351834337590649754473637)
                      ·
                        rfl

theorem cell23_4580181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_4580181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580181 prefixEnd_4580181 := by exact prefixLift 4580181
  have htrace : WordTrace (prefixWord ++ tailWord_4580181) baseStart_4580181 baseEnd_4580181 := by
    simpa [prefixWord, tailWord_4580181, baseEnd_4580181] using wordTrace_append hprefix tailTrace_4580181
  have hstable : (prefixWord ++ tailWord_4580181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580181).length < 2 ^ (prefixWord ++ tailWord_4580181).sum := by decide
  have hdescent : baseEnd_4580181 < baseStart_4580181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580226 : List Nat := [3, 4, 2, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4580226 : Nat := 118140960795 + 4580226 * 2 ^ 59
def prefixEnd_4580226 : Nat := 4983230072969 + 3 ^ 40 * 4580226 * 2
def baseEnd_4580226 : Nat := 2351857444220102078410931

theorem tailTrace_4580226 : CollatzResearch.WordTrace tailWord_4580226 prefixEnd_4580226 2351857444220102078410931 := by
  unfold tailWord_4580226
  simp only [CollatzResearch.WordTrace]
  refine ⟨41763641576157729292144133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111369710869753944779051021 41763641576157729292144133)
  ·
    refine ⟨7830682795529574242277025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41763641576157729292144133 7830682795529574242277025)
    ·
      refine ⟨5873012096647180681707769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7830682795529574242277025 5873012096647180681707769)
      ·
        refine ⟨4404759072485385511280827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5873012096647180681707769 4404759072485385511280827)
        ·
          refine ⟨6607138608728078266921241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4404759072485385511280827 6607138608728078266921241)
          ·
            refine ⟨4955353956546058700190931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6607138608728078266921241 4955353956546058700190931)
            ·
              refine ⟨7433030934819088050286397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4955353956546058700190931 7433030934819088050286397)
              ·
                refine ⟨2787386600557158018857399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7433030934819088050286397 2787386600557158018857399)
                ·
                  refine ⟨4181079900835737028286099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2787386600557158018857399 4181079900835737028286099)
                  ·
                    refine ⟨6271619851253605542429149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4181079900835737028286099 6271619851253605542429149)
                    ·
                      refine ⟨2351857444220102078410931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6271619851253605542429149 2351857444220102078410931)
                      ·
                        rfl

theorem cell23_4580226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4580226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580226 prefixEnd_4580226 := by exact prefixLift 4580226
  have htrace : WordTrace (prefixWord ++ tailWord_4580226) baseStart_4580226 baseEnd_4580226 := by
    simpa [prefixWord, tailWord_4580226, baseEnd_4580226] using wordTrace_append hprefix tailTrace_4580226
  have hstable : (prefixWord ++ tailWord_4580226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580226).length < 2 ^ (prefixWord ++ tailWord_4580226).sum := by decide
  have hdescent : baseEnd_4580226 < baseStart_4580226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580232 : List Nat := [2, 1, 3, 3, 2, 1, 3, 3, 1, 2, 2]
def baseStart_4580232 : Nat := 118140960795 + 4580232 * 2 ^ 59
def prefixEnd_4580232 : Nat := 4983230072969 + 3 ^ 40 * 4580232 * 2
def baseEnd_4580232 : Nat := 2351860525104029054935903

theorem tailTrace_4580232 : CollatzResearch.WordTrace tailWord_4580232 prefixEnd_4580232 2351860525104029054935903 := by
  unfold tailWord_4580232
  simp only [CollatzResearch.WordTrace]
  refine ⟨83527392571304590096647475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111369856761739453462196633 83527392571304590096647475)
  ·
    refine ⟨125291088856956885144971213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83527392571304590096647475 125291088856956885144971213)
    ·
      refine ⟨46984158321358831929364205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125291088856956885144971213 46984158321358831929364205)
      ·
        refine ⟨17619059370509561973511577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46984158321358831929364205 17619059370509561973511577)
        ·
          refine ⟨13214294527882171480133683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17619059370509561973511577 13214294527882171480133683)
          ·
            refine ⟨19821441791823257220200525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13214294527882171480133683 19821441791823257220200525)
            ·
              refine ⟨7433040671933721457575197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19821441791823257220200525 7433040671933721457575197)
              ·
                refine ⟨2787390251975145546590699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7433040671933721457575197 2787390251975145546590699)
                ·
                  refine ⟨4181085377962718319886049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2787390251975145546590699 4181085377962718319886049)
                  ·
                    refine ⟨3135814033472038739914537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4181085377962718319886049 3135814033472038739914537)
                    ·
                      refine ⟨2351860525104029054935903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135814033472038739914537 2351860525104029054935903)
                      ·
                        rfl

theorem cell23_4580232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_4580232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580232 prefixEnd_4580232 := by exact prefixLift 4580232
  have htrace : WordTrace (prefixWord ++ tailWord_4580232) baseStart_4580232 baseEnd_4580232 := by
    simpa [prefixWord, tailWord_4580232, baseEnd_4580232] using wordTrace_append hprefix tailTrace_4580232
  have hstable : (prefixWord ++ tailWord_4580232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580232).length < 2 ^ (prefixWord ++ tailWord_4580232).sum := by decide
  have hdescent : baseEnd_4580232 < baseStart_4580232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580241 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 5, 3, 2]
def baseStart_4580241 : Nat := 118140960795 + 4580241 * 2 ^ 59
def prefixEnd_4580241 : Nat := 4983230072969 + 3 ^ 40 * 4580241 * 2
def baseEnd_4580241 : Nat := 2351865146429919519723361

theorem tailTrace_4580241 : CollatzResearch.WordTrace tailWord_4580241 prefixEnd_4580241 2351865146429919519723361 := by
  unfold tailWord_4580241
  simp only [CollatzResearch.WordTrace]
  refine ⟨167055113399576574730372577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111370075599717716486915051 167055113399576574730372577)
  ·
    refine ⟨125291335049682431047779433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167055113399576574730372577 125291335049682431047779433)
    ·
      refine ⟨93968501287261823285834575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125291335049682431047779433 93968501287261823285834575)
      ·
        refine ⟨140952751930892734928751863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93968501287261823285834575 140952751930892734928751863)
        ·
          refine ⟨211429127896339102393127795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140952751930892734928751863 211429127896339102393127795)
          ·
            refine ⟨317143691844508653589691693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211429127896339102393127795 317143691844508653589691693)
            ·
              refine ⟨118928884441690745096134385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317143691844508653589691693 118928884441690745096134385)
              ·
                refine ⟨89196663331268058822100789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118928884441690745096134385 89196663331268058822100789)
                ·
                  refine ⟨8362187187306380514571949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89196663331268058822100789 8362187187306380514571949)
                  ·
                    refine ⟨3135820195239892692964481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8362187187306380514571949 3135820195239892692964481)
                    ·
                      refine ⟨2351865146429919519723361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135820195239892692964481 2351865146429919519723361)
                      ·
                        rfl

theorem cell23_4580241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_4580241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580241 prefixEnd_4580241 := by exact prefixLift 4580241
  have htrace : WordTrace (prefixWord ++ tailWord_4580241) baseStart_4580241 baseEnd_4580241 := by
    simpa [prefixWord, tailWord_4580241, baseEnd_4580241] using wordTrace_append hprefix tailTrace_4580241
  have hstable : (prefixWord ++ tailWord_4580241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580241).length < 2 ^ (prefixWord ++ tailWord_4580241).sum := by decide
  have hdescent : baseEnd_4580241 < baseStart_4580241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580269 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4580269 : Nat := 118140960795 + 4580269 * 2 ^ 59
def prefixEnd_4580269 : Nat := 4983230072969 + 3 ^ 40 * 4580269 * 2
def baseEnd_4580269 : Nat := 2351879523888245410173233

theorem tailTrace_4580269 : CollatzResearch.WordTrace tailWord_4580269 prefixEnd_4580269 2351879523888245410173233 := by
  unfold tailWord_4580269
  simp only [CollatzResearch.WordTrace]
  refine ⟨167056134643475135512391861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111370756428983423674927907 167056134643475135512391861)
  ·
    refine ⟨15661512622825793954286737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167056134643475135512391861 15661512622825793954286737)
    ·
      refine ⟨11746134467119345465715053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15661512622825793954286737 11746134467119345465715053)
      ·
        refine ⟨4404800425169754549643145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11746134467119345465715053 4404800425169754549643145)
        ·
          refine ⟨3303600318877315912232359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4404800425169754549643145 3303600318877315912232359)
          ·
            refine ⟨4955400478315973868348539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3303600318877315912232359 4955400478315973868348539)
            ·
              refine ⟨7433100717473960802522809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4955400478315973868348539 7433100717473960802522809)
              ·
                refine ⟨5574825538105470601892107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7433100717473960802522809 5574825538105470601892107)
                ·
                  refine ⟨8362238307158205902838161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5574825538105470601892107 8362238307158205902838161)
                  ·
                    refine ⟨6271678730368654427128621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8362238307158205902838161 6271678730368654427128621)
                    ·
                      refine ⟨2351879523888245410173233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6271678730368654427128621 2351879523888245410173233)
                      ·
                        rfl

theorem cell23_4580269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4580269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580269 prefixEnd_4580269 := by exact prefixLift 4580269
  have htrace : WordTrace (prefixWord ++ tailWord_4580269) baseStart_4580269 baseEnd_4580269 := by
    simpa [prefixWord, tailWord_4580269, baseEnd_4580269] using wordTrace_append hprefix tailTrace_4580269
  have hstable : (prefixWord ++ tailWord_4580269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580269).length < 2 ^ (prefixWord ++ tailWord_4580269).sum := by decide
  have hdescent : baseEnd_4580269 < baseStart_4580269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580288 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 1, 4, 2]
def baseStart_4580288 : Nat := 118140960795 + 4580288 * 2 ^ 59
def prefixEnd_4580288 : Nat := 4983230072969 + 3 ^ 40 * 4580288 * 2
def baseEnd_4580288 : Nat := 2351889280020680835835645

theorem tailTrace_4580288 : CollatzResearch.WordTrace tailWord_4580288 prefixEnd_4580288 2351889280020680835835645 := by
  unfold tailWord_4580288
  simp only [CollatzResearch.WordTrace]
  refine ⟨83528413815203150878666759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111371218420270867838222345 83528413815203150878666759)
  ·
    refine ⟨125292620722804726318000139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83528413815203150878666759 125292620722804726318000139)
    ·
      refine ⟨187938931084207089477000209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125292620722804726318000139 187938931084207089477000209)
      ·
        refine ⟨140954198313155317107750157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187938931084207089477000209 140954198313155317107750157)
        ·
          refine ⟨52857824367433243915406309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140954198313155317107750157 52857824367433243915406309)
          ·
            refine ⟨9910842068893733234138683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52857824367433243915406309 9910842068893733234138683)
            ·
              refine ⟨14866263103340599851208025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9910842068893733234138683 14866263103340599851208025)
              ·
                refine ⟨11149697327505449888406019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14866263103340599851208025 11149697327505449888406019)
                ·
                  refine ⟨16724545991258174832609029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11149697327505449888406019 16724545991258174832609029)
                  ·
                    refine ⟨3135852373360907781114193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16724545991258174832609029 3135852373360907781114193)
                    ·
                      refine ⟨2351889280020680835835645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135852373360907781114193 2351889280020680835835645)
                      ·
                        rfl

theorem cell23_4580288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_4580288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580288 prefixEnd_4580288 := by exact prefixLift 4580288
  have htrace : WordTrace (prefixWord ++ tailWord_4580288) baseStart_4580288 baseEnd_4580288 := by
    simpa [prefixWord, tailWord_4580288, baseEnd_4580288] using wordTrace_append hprefix tailTrace_4580288
  have hstable : (prefixWord ++ tailWord_4580288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580288).length < 2 ^ (prefixWord ++ tailWord_4580288).sum := by decide
  have hdescent : baseEnd_4580288 < baseStart_4580288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580305 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 2, 2, 2]
def baseStart_4580305 : Nat := 118140960795 + 4580305 * 2 ^ 59
def prefixEnd_4580305 : Nat := 4983230072969 + 3 ^ 40 * 4580305 * 2
def baseEnd_4580305 : Nat := 2351898009191807269323067

theorem tailTrace_4580305 : CollatzResearch.WordTrace tailWord_4580305 prefixEnd_4580305 2351898009191807269323067 := by
  unfold tailWord_4580305
  simp only [CollatzResearch.WordTrace]
  refine ⟨167057447671344713660702369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111371631780896475773801579 167057447671344713660702369)
  ·
    refine ⟨125293085753508535245526777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167057447671344713660702369 125293085753508535245526777)
    ·
      refine ⟨93969814315131401434145083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125293085753508535245526777 93969814315131401434145083)
      ·
        refine ⟨140954721472697102151217625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93969814315131401434145083 140954721472697102151217625)
        ·
          refine ⟨105716041104522826613413219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140954721472697102151217625 105716041104522826613413219)
          ·
            refine ⟨158574061656784239920119829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105716041104522826613413219 158574061656784239920119829)
            ·
              refine ⟨7433159140161761246255617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158574061656784239920119829 7433159140161761246255617)
              ·
                refine ⟨5574869355121320934691713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7433159140161761246255617 5574869355121320934691713)
                ·
                  refine ⟨4181152016340990701018785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5574869355121320934691713 4181152016340990701018785)
                  ·
                    refine ⟨3135864012255743025764089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4181152016340990701018785 3135864012255743025764089)
                    ·
                      refine ⟨2351898009191807269323067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135864012255743025764089 2351898009191807269323067)
                      ·
                        rfl

theorem cell23_4580305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_4580305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580305 prefixEnd_4580305 := by exact prefixLift 4580305
  have htrace : WordTrace (prefixWord ++ tailWord_4580305) baseStart_4580305 baseEnd_4580305 := by
    simpa [prefixWord, tailWord_4580305, baseEnd_4580305] using wordTrace_append hprefix tailTrace_4580305
  have hstable : (prefixWord ++ tailWord_4580305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580305).length < 2 ^ (prefixWord ++ tailWord_4580305).sum := by decide
  have hdescent : baseEnd_4580305 < baseStart_4580305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580322 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_4580322 : Nat := 118140960795 + 4580322 * 2 ^ 59
def prefixEnd_4580322 : Nat := 4983230072969 + 3 ^ 40 * 4580322 * 2
def baseEnd_4580322 : Nat := 2351906738362933702810489

theorem tailTrace_4580322 : CollatzResearch.WordTrace tailWord_4580322 prefixEnd_4580322 2351906738362933702810489 := by
  unfold tailWord_4580322
  simp only [CollatzResearch.WordTrace]
  refine ⟨41764516928070781391017805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111372045141522083709380813 41764516928070781391017805)
  ·
    refine ⟨15661693848026543021631677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41764516928070781391017805 15661693848026543021631677)
    ·
      refine ⟨5873135193009953633111879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15661693848026543021631677 5873135193009953633111879)
      ·
        refine ⟨8809702789514930449667819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5873135193009953633111879 8809702789514930449667819)
        ·
          refine ⟨13214554184272395674501729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8809702789514930449667819 13214554184272395674501729)
          ·
            refine ⟨9910915638204296755876297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13214554184272395674501729 9910915638204296755876297)
            ·
              refine ⟨7433186728653222566907223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9910915638204296755876297 7433186728653222566907223)
              ·
                refine ⟨11149780092979833850360835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7433186728653222566907223 11149780092979833850360835)
                ·
                  refine ⟨16724670139469750775541253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11149780092979833850360835 16724670139469750775541253)
                  ·
                    refine ⟨3135875651150578270413985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16724670139469750775541253 3135875651150578270413985)
                    ·
                      refine ⟨2351906738362933702810489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135875651150578270413985 2351906738362933702810489)
                      ·
                        rfl

theorem cell23_4580322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_4580322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580322 prefixEnd_4580322 := by exact prefixLift 4580322
  have htrace : WordTrace (prefixWord ++ tailWord_4580322) baseStart_4580322 baseEnd_4580322 := by
    simpa [prefixWord, tailWord_4580322, baseEnd_4580322] using wordTrace_append hprefix tailTrace_4580322
  have hstable : (prefixWord ++ tailWord_4580322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580322).length < 2 ^ (prefixWord ++ tailWord_4580322).sum := by decide
  have hdescent : baseEnd_4580322 < baseStart_4580322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580361 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 4]
def baseStart_4580361 : Nat := 118140960795 + 4580361 * 2 ^ 59
def prefixEnd_4580361 : Nat := 4983230072969 + 3 ^ 40 * 4580361 * 2
def baseEnd_4580361 : Nat := 2351926764108459050222809

theorem tailTrace_4580361 : CollatzResearch.WordTrace tailWord_4580361 prefixEnd_4580361 2351926764108459050222809 := by
  unfold tailWord_4580361
  simp only [CollatzResearch.WordTrace]
  refine ⟨167059490159141835224740937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111372993439427890149827291 167059490159141835224740937)
  ·
    refine ⟨125294617619356376418555703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167059490159141835224740937 125294617619356376418555703)
    ·
      refine ⟨187941926429034564627833555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125294617619356376418555703 187941926429034564627833555)
      ·
        refine ⟨281912889643551846941750333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187941926429034564627833555 281912889643551846941750333)
        ·
          refine ⟨105717333616331942603156375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281912889643551846941750333 105717333616331942603156375)
          ·
            refine ⟨158576000424497913904734563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105717333616331942603156375 158576000424497913904734563)
            ·
              refine ⟨237864000636746870857101845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158576000424497913904734563 237864000636746870857101845)
              ·
                refine ⟨11149875029847509571426649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 237864000636746870857101845 11149875029847509571426649)
                ·
                  refine ⟨8362406272385632178569987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11149875029847509571426649 8362406272385632178569987)
                  ·
                    refine ⟨12543609408578448267854981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8362406272385632178569987 12543609408578448267854981)
                    ·
                      refine ⟨2351926764108459050222809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12543609408578448267854981 2351926764108459050222809)
                      ·
                        rfl

theorem cell23_4580361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_4580361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580361 prefixEnd_4580361 := by exact prefixLift 4580361
  have htrace : WordTrace (prefixWord ++ tailWord_4580361) baseStart_4580361 baseEnd_4580361 := by
    simpa [prefixWord, tailWord_4580361, baseEnd_4580361] using wordTrace_append hprefix tailTrace_4580361
  have hstable : (prefixWord ++ tailWord_4580361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580361).length < 2 ^ (prefixWord ++ tailWord_4580361).sum := by decide
  have hdescent : baseEnd_4580361 < baseStart_4580361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580378 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2]
def baseStart_4580378 : Nat := 118140960795 + 4580378 * 2 ^ 59
def prefixEnd_4580378 : Nat := 4983230072969 + 3 ^ 40 * 4580378 * 2
def baseEnd_4580378 : Nat := 2351935493279585483710231

theorem tailTrace_4580378 : CollatzResearch.WordTrace tailWord_4580378 prefixEnd_4580378 2351935493279585483710231 := by
  unfold tailWord_4580378
  simp only [CollatzResearch.WordTrace]
  refine ⟨41765027550020061782027447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111373406800053498085406525 41765027550020061782027447)
  ·
    refine ⟨62647541325030092673041171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41765027550020061782027447 62647541325030092673041171)
    ·
      refine ⟨93971311987545139009561757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62647541325030092673041171 93971311987545139009561757)
      ·
        refine ⟨35239241995329427128585659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93971311987545139009561757 35239241995329427128585659)
        ·
          refine ⟨52858862992994140692878489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35239241995329427128585659 52858862992994140692878489)
          ·
            refine ⟨39644147244745605519658867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52858862992994140692878489 39644147244745605519658867)
            ·
              refine ⟨59466220867118408279488301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39644147244745605519658867 59466220867118408279488301)
              ·
                refine ⟨22299832825169403104808113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59466220867118408279488301 22299832825169403104808113)
                ·
                  refine ⟨16724874618877052328606085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22299832825169403104808113 16724874618877052328606085)
                  ·
                    refine ⟨3135913991039447311613641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16724874618877052328606085 3135913991039447311613641)
                    ·
                      refine ⟨2351935493279585483710231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135913991039447311613641 2351935493279585483710231)
                      ·
                        rfl

theorem cell23_4580378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_4580378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580378 prefixEnd_4580378 := by exact prefixLift 4580378
  have htrace : WordTrace (prefixWord ++ tailWord_4580378) baseStart_4580378 baseEnd_4580378 := by
    simpa [prefixWord, tailWord_4580378, baseEnd_4580378] using wordTrace_append hprefix tailTrace_4580378
  have hstable : (prefixWord ++ tailWord_4580378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580378).length < 2 ^ (prefixWord ++ tailWord_4580378).sum := by decide
  have hdescent : baseEnd_4580378 < baseStart_4580378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580398 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_4580398 : Nat := 118140960795 + 4580398 * 2 ^ 59
def prefixEnd_4580398 : Nat := 4983230072969 + 3 ^ 40 * 4580398 * 2
def baseEnd_4580398 : Nat := 2351945762892675405460139

theorem tailTrace_4580398 : CollatzResearch.WordTrace tailWord_4580398 prefixEnd_4580398 2351945762892675405460139 := by
  unfold tailWord_4580398
  simp only [CollatzResearch.WordTrace]
  refine ⟨20882604957500973817979731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111373893106671860362558565 20882604957500973817979731)
  ·
    refine ⟨31323907436251460726969597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20882604957500973817979731 31323907436251460726969597)
    ·
      refine ⟨11746465288594297772613599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31323907436251460726969597 11746465288594297772613599)
      ·
        refine ⟨17619697932891446658920399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11746465288594297772613599 17619697932891446658920399)
        ·
          refine ⟨26429546899337169988380599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17619697932891446658920399 26429546899337169988380599)
          ·
            refine ⟨39644320349005754982570899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26429546899337169988380599 39644320349005754982570899)
            ·
              refine ⟨59466480523508632473856349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39644320349005754982570899 59466480523508632473856349)
              ·
                refine ⟨22299930196315737177696131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59466480523508632473856349 22299930196315737177696131)
                ·
                  refine ⟨33449895294473605766544197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22299930196315737177696131 33449895294473605766544197)
                  ·
                    refine ⟨6271855367713801081227037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33449895294473605766544197 6271855367713801081227037)
                    ·
                      refine ⟨2351945762892675405460139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6271855367713801081227037 2351945762892675405460139)
                      ·
                        rfl

theorem cell23_4580398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_4580398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580398 prefixEnd_4580398 := by exact prefixLift 4580398
  have htrace : WordTrace (prefixWord ++ tailWord_4580398) baseStart_4580398 baseEnd_4580398 := by
    simpa [prefixWord, tailWord_4580398, baseEnd_4580398] using wordTrace_append hprefix tailTrace_4580398
  have hstable : (prefixWord ++ tailWord_4580398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580398).length < 2 ^ (prefixWord ++ tailWord_4580398).sum := by decide
  have hdescent : baseEnd_4580398 < baseStart_4580398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580422 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_4580422 : Nat := 118140960795 + 4580422 * 2 ^ 59
def prefixEnd_4580422 : Nat := 4983230072969 + 3 ^ 40 * 4580422 * 2
def baseEnd_4580422 : Nat := 783986028809461103853343

theorem tailTrace_4580422 : CollatzResearch.WordTrace tailWord_4580422 prefixEnd_4580422 783986028809461103853343 := by
  unfold tailWord_4580422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5220678594122526332584735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111374476674613895095141013 5220678594122526332584735)
  ·
    refine ⟨7831017891183789498877103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5220678594122526332584735 7831017891183789498877103)
    ·
      refine ⟨11746526836775684248315655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7831017891183789498877103 11746526836775684248315655)
      ·
        refine ⟨17619790255163526372473483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11746526836775684248315655 17619790255163526372473483)
        ·
          refine ⟨26429685382745289558710225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17619790255163526372473483 26429685382745289558710225)
          ·
            refine ⟨19822264037058967169032669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26429685382745289558710225 19822264037058967169032669)
            ·
              refine ⟨7433349013897112688387251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19822264037058967169032669 7433349013897112688387251)
              ·
                refine ⟨11150023520845669032580877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7433349013897112688387251 11150023520845669032580877)
                ·
                  refine ⟨4181258820317125887217829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11150023520845669032580877 4181258820317125887217829)
                  ·
                    refine ⟨783986028809461103853343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4181258820317125887217829 783986028809461103853343)
                    ·
                      rfl

theorem cell23_4580422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_4580422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580422 prefixEnd_4580422 := by exact prefixLift 4580422
  have htrace : WordTrace (prefixWord ++ tailWord_4580422) baseStart_4580422 baseEnd_4580422 := by
    simpa [prefixWord, tailWord_4580422, baseEnd_4580422] using wordTrace_append hprefix tailTrace_4580422
  have hstable : (prefixWord ++ tailWord_4580422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580422).length < 2 ^ (prefixWord ++ tailWord_4580422).sum := by decide
  have hdescent : baseEnd_4580422 < baseStart_4580422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580455 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_4580455 : Nat := 118140960795 + 4580455 * 2 ^ 59
def prefixEnd_4580455 : Nat := 4983230072969 + 3 ^ 40 * 4580455 * 2
def baseEnd_4580455 : Nat := 2351975031289981682447377

theorem tailTrace_4580455 : CollatzResearch.WordTrace tailWord_4580455 prefixEnd_4580455 2351975031289981682447377 := by
  unfold tailWord_4580455
  simp only [CollatzResearch.WordTrace]
  refine ⟨167062918620801289278662819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111375279080534192852441879 167062918620801289278662819)
  ·
    refine ⟨250594377931201933917994229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167062918620801289278662819 250594377931201933917994229)
    ·
      refine ⟨23493222931050181304811959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 250594377931201933917994229 23493222931050181304811959)
      ·
        refine ⟨35239834396575271957217939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23493222931050181304811959 35239834396575271957217939)
        ·
          refine ⟨52859751594862907935826909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35239834396575271957217939 52859751594862907935826909)
          ·
            refine ⟨19822406848073590475935091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52859751594862907935826909 19822406848073590475935091)
            ·
              refine ⟨29733610272110385713902637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19822406848073590475935091 29733610272110385713902637)
              ·
                refine ⟨11150103852041394642713489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29733610272110385713902637 11150103852041394642713489)
                ·
                  refine ⟨8362577889031045982035117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11150103852041394642713489 8362577889031045982035117)
                  ·
                    refine ⟨3135966708386642243263169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8362577889031045982035117 3135966708386642243263169)
                    ·
                      refine ⟨2351975031289981682447377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3135966708386642243263169 2351975031289981682447377)
                      ·
                        rfl

theorem cell23_4580455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_4580455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580455 prefixEnd_4580455 := by exact prefixLift 4580455
  have htrace : WordTrace (prefixWord ++ tailWord_4580455) baseStart_4580455 baseEnd_4580455 := by
    simpa [prefixWord, tailWord_4580455, baseEnd_4580455] using wordTrace_append hprefix tailTrace_4580455
  have hstable : (prefixWord ++ tailWord_4580455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580455).length < 2 ^ (prefixWord ++ tailWord_4580455).sum := by decide
  have hdescent : baseEnd_4580455 < baseStart_4580455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580519 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_4580519 : Nat := 118140960795 + 4580519 * 2 ^ 59
def prefixEnd_4580519 : Nat := 4983230072969 + 3 ^ 40 * 4580519 * 2
def baseEnd_4580519 : Nat := 2352007894051869432047083

theorem tailTrace_4580519 : CollatzResearch.WordTrace tailWord_4580519 prefixEnd_4580519 2352007894051869432047083 := by
  unfold tailWord_4580519
  simp only [CollatzResearch.WordTrace]
  refine ⟨167065252892569428208992611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111376835261712952139328407 167065252892569428208992611)
  ·
    refine ⟨250597879338854142313488917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167065252892569428208992611 250597879338854142313488917)
    ·
      refine ⟨11746775594008787920944793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 250597879338854142313488917 11746775594008787920944793)
      ·
        refine ⟨8810081695506590940708595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11746775594008787920944793 8810081695506590940708595)
        ·
          refine ⟨13215122543259886411062893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8810081695506590940708595 13215122543259886411062893)
          ·
            refine ⟨4955670953722457404148585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13215122543259886411062893 4955670953722457404148585)
            ·
              refine ⟨3716753215291843053111439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4955670953722457404148585 3716753215291843053111439)
              ·
                refine ⟨5575129822937764579667159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3716753215291843053111439 5575129822937764579667159)
                ·
                  refine ⟨8362694734406646869500739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5575129822937764579667159 8362694734406646869500739)
                  ·
                    refine ⟨12544042101609970304251109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8362694734406646869500739 12544042101609970304251109)
                    ·
                      refine ⟨2352007894051869432047083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12544042101609970304251109 2352007894051869432047083)
                      ·
                        rfl

theorem cell23_4580519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_4580519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580519 prefixEnd_4580519 := by exact prefixLift 4580519
  have htrace : WordTrace (prefixWord ++ tailWord_4580519) baseStart_4580519 baseEnd_4580519 := by
    simpa [prefixWord, tailWord_4580519, baseEnd_4580519] using wordTrace_append hprefix tailTrace_4580519
  have hstable : (prefixWord ++ tailWord_4580519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580519).length < 2 ^ (prefixWord ++ tailWord_4580519).sum := by decide
  have hdescent : baseEnd_4580519 < baseStart_4580519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580535 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 4, 1, 3]
def baseStart_4580535 : Nat := 118140960795 + 4580535 * 2 ^ 59
def prefixEnd_4580535 : Nat := 4983230072969 + 3 ^ 40 * 4580535 * 2
def baseEnd_4580535 : Nat := 2352016109742341369447009

theorem tailTrace_4580535 : CollatzResearch.WordTrace tailWord_4580535 prefixEnd_4580535 2352016109742341369447009 := by
  unfold tailWord_4580535
  simp only [CollatzResearch.WordTrace]
  refine ⟨167065836460511462941575059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111377224307007641961050039 167065836460511462941575059)
  ·
    refine ⟨250598754690767194412362589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167065836460511462941575059 250598754690767194412362589)
    ·
      refine ⟨93974533009037697904635971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250598754690767194412362589 93974533009037697904635971)
      ·
        refine ⟨140961799513556546856953957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93974533009037697904635971 140961799513556546856953957)
        ·
          refine ⟨26430337408791852535678867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140961799513556546856953957 26430337408791852535678867)
          ·
            refine ⟨39645506113187778803518301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26430337408791852535678867 39645506113187778803518301)
            ·
              refine ⟨14867064792445417051319363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39645506113187778803518301 14867064792445417051319363)
              ·
                refine ⟨22300597188668125576979045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14867064792445417051319363 22300597188668125576979045)
                ·
                  refine ⟨4181361972875273545683571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22300597188668125576979045 4181361972875273545683571)
                  ·
                    refine ⟨6272042959312910318525357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4181361972875273545683571 6272042959312910318525357)
                    ·
                      refine ⟨2352016109742341369447009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6272042959312910318525357 2352016109742341369447009)
                      ·
                        rfl

theorem cell23_4580535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_4580535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580535 prefixEnd_4580535 := by exact prefixLift 4580535
  have htrace : WordTrace (prefixWord ++ tailWord_4580535) baseStart_4580535 baseEnd_4580535 := by
    simpa [prefixWord, tailWord_4580535, baseEnd_4580535] using wordTrace_append hprefix tailTrace_4580535
  have hstable : (prefixWord ++ tailWord_4580535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580535).length < 2 ^ (prefixWord ++ tailWord_4580535).sum := by decide
  have hdescent : baseEnd_4580535 < baseStart_4580535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580546 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_4580546 : Nat := 118140960795 + 4580546 * 2 ^ 59
def prefixEnd_4580546 : Nat := 4983230072969 + 3 ^ 40 * 4580546 * 2
def baseEnd_4580546 : Nat := 784007252676513608803153

theorem tailTrace_4580546 : CollatzResearch.WordTrace tailWord_4580546 prefixEnd_4580546 784007252676513608803153 := by
  unfold tailWord_4580546
  simp only [CollatzResearch.WordTrace]
  refine ⟨41766559415867902955056373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111377491775647741213483661 41766559415867902955056373)
  ·
    refine ⟨3915614945237615902036535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41766559415867902955056373 3915614945237615902036535)
    ·
      refine ⟨5873422417856423853054803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3915614945237615902036535 5873422417856423853054803)
      ·
        refine ⟨8810133626784635779582205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5873422417856423853054803 8810133626784635779582205)
        ·
          refine ⟨3303800110044238417343327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8810133626784635779582205 3303800110044238417343327)
          ·
            refine ⟨4955700165066357626014991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3303800110044238417343327 4955700165066357626014991)
            ·
              refine ⟨7433550247599536439022487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4955700165066357626014991 7433550247599536439022487)
              ·
                refine ⟨11150325371399304658533731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7433550247599536439022487 11150325371399304658533731)
                ·
                  refine ⟨16725488057098956987800597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11150325371399304658533731 16725488057098956987800597)
                  ·
                    refine ⟨784007252676513608803153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16725488057098956987800597 784007252676513608803153)
                    ·
                      rfl

theorem cell23_4580546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_4580546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580546 prefixEnd_4580546 := by exact prefixLift 4580546
  have htrace : WordTrace (prefixWord ++ tailWord_4580546) baseStart_4580546 baseEnd_4580546 := by
    simpa [prefixWord, tailWord_4580546, baseEnd_4580546] using wordTrace_append hprefix tailTrace_4580546
  have hstable : (prefixWord ++ tailWord_4580546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580546).length < 2 ^ (prefixWord ++ tailWord_4580546).sum := by decide
  have hdescent : baseEnd_4580546 < baseStart_4580546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580571 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 6]
def baseStart_4580571 : Nat := 118140960795 + 4580571 * 2 ^ 59
def prefixEnd_4580571 : Nat := 4983230072969 + 3 ^ 40 * 4580571 * 2
def baseEnd_4580571 : Nat := 2352034595045903228596843

theorem tailTrace_4580571 : CollatzResearch.WordTrace tailWord_4580571 prefixEnd_4580571 2352034595045903228596843 := by
  unfold tailWord_4580571
  simp only [CollatzResearch.WordTrace]
  refine ⟨167067149488381041089885567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111378099658920694059923711 167067149488381041089885567)
  ·
    refine ⟨250600724232571561634828351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167067149488381041089885567 250600724232571561634828351)
    ·
      refine ⟨375901086348857342452242527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250600724232571561634828351 375901086348857342452242527)
      ·
        refine ⟨563851629523286013678363791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375901086348857342452242527 563851629523286013678363791)
        ·
          refine ⟨845777444284929020517545687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563851629523286013678363791 845777444284929020517545687)
          ·
            refine ⟨1268666166427393530776318531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845777444284929020517545687 1268666166427393530776318531)
            ·
              refine ⟨1902999249641090296164477797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268666166427393530776318531 1902999249641090296164477797)
              ·
                refine ⟨356812359307704430530839587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1902999249641090296164477797 356812359307704430530839587)
                ·
                  refine ⟨535218538961556645796259381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356812359307704430530839587 535218538961556645796259381)
                  ·
                    refine ⟨50176738027645935543399317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 535218538961556645796259381 50176738027645935543399317)
                    ·
                      refine ⟨2352034595045903228596843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50176738027645935543399317 2352034595045903228596843)
                      ·
                        rfl

theorem cell23_4580571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_4580571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580571 prefixEnd_4580571 := by exact prefixLift 4580571
  have htrace : WordTrace (prefixWord ++ tailWord_4580571) baseStart_4580571 baseEnd_4580571 := by
    simpa [prefixWord, tailWord_4580571, baseEnd_4580571] using wordTrace_append hprefix tailTrace_4580571
  have hstable : (prefixWord ++ tailWord_4580571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580571).length < 2 ^ (prefixWord ++ tailWord_4580571).sum := by decide
  have hdescent : baseEnd_4580571 < baseStart_4580571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580575 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 1, 4, 2]
def baseStart_4580575 : Nat := 118140960795 + 4580575 * 2 ^ 59
def prefixEnd_4580575 : Nat := 4983230072969 + 3 ^ 40 * 4580575 * 2
def baseEnd_4580575 : Nat := 2352036648968521212946825

theorem tailTrace_4580575 : CollatzResearch.WordTrace tailWord_4580575 prefixEnd_4580575 2352036648968521212946825 := by
  unfold tailWord_4580575
  simp only [CollatzResearch.WordTrace]
  refine ⟨167067295380366549773031179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111378196920244366515354119 167067295380366549773031179)
  ·
    refine ⟨250600943070549824659546769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167067295380366549773031179 250600943070549824659546769)
    ·
      refine ⟨187950707302912368494660077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250600943070549824659546769 187950707302912368494660077)
      ·
        refine ⟨70481515238592138185497529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187950707302912368494660077 70481515238592138185497529)
        ·
          refine ⟨52861136428944103639123147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70481515238592138185497529 52861136428944103639123147)
          ·
            refine ⟨79291704643416155458684721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52861136428944103639123147 79291704643416155458684721)
            ·
              refine ⟨59468778482562116594013541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79291704643416155458684721 59468778482562116594013541)
              ·
                refine ⟨11150395965480396861377539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59468778482562116594013541 11150395965480396861377539)
                ·
                  refine ⟨16725593948220595292066309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11150395965480396861377539 16725593948220595292066309)
                  ·
                    refine ⟨3136048865291361617262433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16725593948220595292066309 3136048865291361617262433)
                    ·
                      refine ⟨2352036648968521212946825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136048865291361617262433 2352036648968521212946825)
                      ·
                        rfl

theorem cell23_4580575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_4580575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580575 prefixEnd_4580575 := by exact prefixLift 4580575
  have htrace : WordTrace (prefixWord ++ tailWord_4580575) baseStart_4580575 baseEnd_4580575 := by
    simpa [prefixWord, tailWord_4580575, baseEnd_4580575] using wordTrace_append hprefix tailTrace_4580575
  have hstable : (prefixWord ++ tailWord_4580575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580575).length < 2 ^ (prefixWord ++ tailWord_4580575).sum := by decide
  have hdescent : baseEnd_4580575 < baseStart_4580575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580608 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 3]
def baseStart_4580608 : Nat := 118140960795 + 4580608 * 2 ^ 59
def prefixEnd_4580608 : Nat := 4983230072969 + 3 ^ 40 * 4580608 * 2
def baseEnd_4580608 : Nat := 2352053593830119583834173

theorem tailTrace_4580608 : CollatzResearch.WordTrace tailWord_4580608 prefixEnd_4580608 2352053593830119583834173 := by
  unfold tailWord_4580608
  simp only [CollatzResearch.WordTrace]
  refine ⟨83534249494623498204491239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111378999326164664272654985 83534249494623498204491239)
  ·
    refine ⟨125301374241935247306736859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83534249494623498204491239 125301374241935247306736859)
    ·
      refine ⟨187952061362902870960105289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125301374241935247306736859 187952061362902870960105289)
      ·
        refine ⟨140964046022177153220078967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187952061362902870960105289 140964046022177153220078967)
        ·
          refine ⟨211446069033265729830118451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140964046022177153220078967 211446069033265729830118451)
          ·
            refine ⟨317169103549898594745177677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211446069033265729830118451 317169103549898594745177677)
            ·
              refine ⟨118938413831211973029441629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317169103549898594745177677 118938413831211973029441629)
              ·
                refine ⟨44601905186704489886040611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118938413831211973029441629 44601905186704489886040611)
                ·
                  refine ⟨66902857780056734829060917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44601905186704489886040611 66902857780056734829060917)
                  ·
                    refine ⟨6272142916880318890224461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66902857780056734829060917 6272142916880318890224461)
                    ·
                      refine ⟨2352053593830119583834173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6272142916880318890224461 2352053593830119583834173)
                      ·
                        rfl

theorem cell23_4580608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_4580608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580608 prefixEnd_4580608 := by exact prefixLift 4580608
  have htrace : WordTrace (prefixWord ++ tailWord_4580608) baseStart_4580608 baseEnd_4580608 := by
    simpa [prefixWord, tailWord_4580608, baseEnd_4580608] using wordTrace_append hprefix tailTrace_4580608
  have hstable : (prefixWord ++ tailWord_4580608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580608).length < 2 ^ (prefixWord ++ tailWord_4580608).sum := by decide
  have hdescent : baseEnd_4580608 < baseStart_4580608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580609 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_4580609 : Nat := 118140960795 + 4580609 * 2 ^ 59
def prefixEnd_4580609 : Nat := 4983230072969 + 3 ^ 40 * 4580609 * 2
def baseEnd_4580609 : Nat := 2352054107310774079921669

theorem tailTrace_4580609 : CollatzResearch.WordTrace tailWord_4580609 prefixEnd_4580609 2352054107310774079921669 := by
  unfold tailWord_4580609
  simp only [CollatzResearch.WordTrace]
  refine ⟨167068535462243373579768881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111379023641495582386512587 167068535462243373579768881)
  ·
    refine ⟨125301401596682530184826661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167068535462243373579768881 125301401596682530184826661)
    ·
      refine ⟨23494012799377974409654999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125301401596682530184826661 23494012799377974409654999)
      ·
        refine ⟨35241019199066961614482499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23494012799377974409654999 35241019199066961614482499)
        ·
          refine ⟨52861528798600442421723749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35241019199066961614482499 52861528798600442421723749)
          ·
            refine ⟨9911536649737582954073203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52861528798600442421723749 9911536649737582954073203)
            ·
              refine ⟨14867304974606374431109805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9911536649737582954073203 14867304974606374431109805)
              ·
                refine ⟨5575239365477390411666177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14867304974606374431109805 5575239365477390411666177)
                ·
                  refine ⟨4181429524108042808749633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5575239365477390411666177 4181429524108042808749633)
                  ·
                    refine ⟨3136072143081032106562225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4181429524108042808749633 3136072143081032106562225)
                    ·
                      refine ⟨2352054107310774079921669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136072143081032106562225 2352054107310774079921669)
                      ·
                        rfl

theorem cell23_4580609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_4580609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580609 prefixEnd_4580609 := by exact prefixLift 4580609
  have htrace : WordTrace (prefixWord ++ tailWord_4580609) baseStart_4580609 baseEnd_4580609 := by
    simpa [prefixWord, tailWord_4580609, baseEnd_4580609] using wordTrace_append hprefix tailTrace_4580609
  have hstable : (prefixWord ++ tailWord_4580609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580609).length < 2 ^ (prefixWord ++ tailWord_4580609).sum := by decide
  have hdescent : baseEnd_4580609 < baseStart_4580609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580626 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4580626 : Nat := 118140960795 + 4580626 * 2 ^ 59
def prefixEnd_4580626 : Nat := 4983230072969 + 3 ^ 40 * 4580626 * 2
def baseEnd_4580626 : Nat := 2352062836481900513409091

theorem tailTrace_4580626 : CollatzResearch.WordTrace tailWord_4580626 prefixEnd_4580626 2352062836481900513409091 := by
  unfold tailWord_4580626
  simp only [CollatzResearch.WordTrace]
  refine ⟨41767288875795446370784433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111379437002121190322091821 41767288875795446370784433)
  ·
    refine ⟨31325466656846584778088325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41767288875795446370784433 31325466656846584778088325)
    ·
      refine ⟨5873524998158734645891561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31325466656846584778088325 5873524998158734645891561)
      ·
        refine ⟨4405143748619050984418671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5873524998158734645891561 4405143748619050984418671)
        ·
          refine ⟨6607715622928576476628007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4405143748619050984418671 6607715622928576476628007)
          ·
            refine ⟨9911573434392864714942011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6607715622928576476628007 9911573434392864714942011)
            ·
              refine ⟨14867360151589297072413017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9911573434392864714942011 14867360151589297072413017)
              ·
                refine ⟨11150520113691972804309763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14867360151589297072413017 11150520113691972804309763)
                ·
                  refine ⟨16725780170537959206464645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11150520113691972804309763 16725780170537959206464645)
                  ·
                    refine ⟨3136083781975867351212121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16725780170537959206464645 3136083781975867351212121)
                    ·
                      refine ⟨2352062836481900513409091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136083781975867351212121 2352062836481900513409091)
                      ·
                        rfl

theorem cell23_4580626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4580626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580626 prefixEnd_4580626 := by exact prefixLift 4580626
  have htrace : WordTrace (prefixWord ++ tailWord_4580626) baseStart_4580626 baseEnd_4580626 := by
    simpa [prefixWord, tailWord_4580626, baseEnd_4580626] using wordTrace_append hprefix tailTrace_4580626
  have hstable : (prefixWord ++ tailWord_4580626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580626).length < 2 ^ (prefixWord ++ tailWord_4580626).sum := by decide
  have hdescent : baseEnd_4580626 < baseStart_4580626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580645 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_4580645 : Nat := 118140960795 + 4580645 * 2 ^ 59
def prefixEnd_4580645 : Nat := 4983230072969 + 3 ^ 40 * 4580645 * 2
def baseEnd_4580645 : Nat := 784024197538111979690501

theorem tailTrace_4580645 : CollatzResearch.WordTrace tailWord_4580645 prefixEnd_4580645 784024197538111979690501 := by
  unfold tailWord_4580645
  simp only [CollatzResearch.WordTrace]
  refine ⟨167069848490112951728079389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111379898993408634485386259 167069848490112951728079389)
  ·
    refine ⟨62651193183792356898029771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167069848490112951728079389 62651193183792356898029771)
    ·
      refine ⟨93976789775688535347044657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62651193183792356898029771 93976789775688535347044657)
      ·
        refine ⟨70482592331766401510283493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93976789775688535347044657 70482592331766401510283493)
        ·
          refine ⟨13215486062206200283178155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70482592331766401510283493 13215486062206200283178155)
          ·
            refine ⟨19823229093309300424767233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13215486062206200283178155 19823229093309300424767233)
            ·
              refine ⟨14867421819981975318575425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19823229093309300424767233 14867421819981975318575425)
              ·
                refine ⟨11150566364986481488931569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14867421819981975318575425 11150566364986481488931569)
                ·
                  refine ⟨8362924773739861116698677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11150566364986481488931569 8362924773739861116698677)
                  ·
                    refine ⟨784024197538111979690501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8362924773739861116698677 784024197538111979690501)
                    ·
                      rfl

theorem cell23_4580645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_4580645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580645 prefixEnd_4580645 := by exact prefixLift 4580645
  have htrace : WordTrace (prefixWord ++ tailWord_4580645) baseStart_4580645 baseEnd_4580645 := by
    simpa [prefixWord, tailWord_4580645, baseEnd_4580645] using wordTrace_append hprefix tailTrace_4580645
  have hstable : (prefixWord ++ tailWord_4580645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580645).length < 2 ^ (prefixWord ++ tailWord_4580645).sum := by decide
  have hdescent : baseEnd_4580645 < baseStart_4580645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580688 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 8]
def baseStart_4580688 : Nat := 118140960795 + 4580688 * 2 ^ 59
def prefixEnd_4580688 : Nat := 4983230072969 + 3 ^ 40 * 4580688 * 2
def baseEnd_4580688 : Nat := 261343852475831030092645

theorem tailTrace_4580688 : CollatzResearch.WordTrace tailWord_4580688 prefixEnd_4580688 261343852475831030092645 := by
  unfold tailWord_4580688
  simp only [CollatzResearch.WordTrace]
  refine ⟨83535708414478585035947359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111380944552638113381263145 83535708414478585035947359)
  ·
    refine ⟨125303562621717877553921039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83535708414478585035947359 125303562621717877553921039)
    ·
      refine ⟨187955343932576816330881559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125303562621717877553921039 187955343932576816330881559)
      ·
        refine ⟨281933015898865224496322339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187955343932576816330881559 281933015898865224496322339)
        ·
          refine ⟨422899523848297836744483509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281933015898865224496322339 422899523848297836744483509)
          ·
            refine ⟨39646830360777922194795329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 422899523848297836744483509 39646830360777922194795329)
            ·
              refine ⟨29735122770583441646096497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39646830360777922194795329 29735122770583441646096497)
              ·
                refine ⟨22301342077937581234572373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29735122770583441646096497 22301342077937581234572373)
                ·
                  refine ⟨261343852475831030092645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22301342077937581234572373 261343852475831030092645)
                  ·
                    rfl

theorem cell23_4580688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 8].length) (baseStart_4580688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580688 prefixEnd_4580688 := by exact prefixLift 4580688
  have htrace : WordTrace (prefixWord ++ tailWord_4580688) baseStart_4580688 baseEnd_4580688 := by
    simpa [prefixWord, tailWord_4580688, baseEnd_4580688] using wordTrace_append hprefix tailTrace_4580688
  have hstable : (prefixWord ++ tailWord_4580688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580688).length < 2 ^ (prefixWord ++ tailWord_4580688).sum := by decide
  have hdescent : baseEnd_4580688 < baseStart_4580688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580694 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4580694 : Nat := 118140960795 + 4580694 * 2 ^ 59
def prefixEnd_4580694 : Nat := 4983230072969 + 3 ^ 40 * 4580694 * 2
def baseEnd_4580694 : Nat := 2352097753166406247358779

theorem tailTrace_4580694 : CollatzResearch.WordTrace tailWord_4580694 prefixEnd_4580694 2352097753166406247358779 := by
  unfold tailWord_4580694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10441977229183464568538321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111381090444623622064408757 10441977229183464568538321)
  ·
    refine ⟨7831482921887598426403741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10441977229183464568538321 7831482921887598426403741)
    ·
      refine ⟨2936806095707849409901403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7831482921887598426403741 2936806095707849409901403)
      ·
        refine ⟨4405209143561774114852105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2936806095707849409901403 4405209143561774114852105)
        ·
          refine ⟨3303906857671330586139079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4405209143561774114852105 3303906857671330586139079)
          ·
            refine ⟨4955860286506995879208619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3303906857671330586139079 4955860286506995879208619)
            ·
              refine ⟨7433790429760493818812929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4955860286506995879208619 7433790429760493818812929)
              ·
                refine ⟨5575342822320370364109697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7433790429760493818812929 5575342822320370364109697)
                ·
                  refine ⟨4181507116740277773082273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5575342822320370364109697 4181507116740277773082273)
                  ·
                    refine ⟨3136130337555208329811705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4181507116740277773082273 3136130337555208329811705)
                    ·
                      refine ⟨2352097753166406247358779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136130337555208329811705 2352097753166406247358779)
                      ·
                        rfl

theorem cell23_4580694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4580694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580694 prefixEnd_4580694 := by exact prefixLift 4580694
  have htrace : WordTrace (prefixWord ++ tailWord_4580694) baseStart_4580694 baseEnd_4580694 := by
    simpa [prefixWord, tailWord_4580694, baseEnd_4580694] using wordTrace_append hprefix tailTrace_4580694
  have hstable : (prefixWord ++ tailWord_4580694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580694).length < 2 ^ (prefixWord ++ tailWord_4580694).sum := by decide
  have hdescent : baseEnd_4580694 < baseStart_4580694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580722 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 6]
def baseStart_4580722 : Nat := 118140960795 + 4580722 * 2 ^ 59
def prefixEnd_4580722 : Nat := 4983230072969 + 3 ^ 40 * 4580722 * 2
def baseEnd_4580722 : Nat := 261345792291636904200961

theorem tailTrace_4580722 : CollatzResearch.WordTrace tailWord_4580722 prefixEnd_4580722 261345792291636904200961 := by
  unfold tailWord_4580722
  simp only [CollatzResearch.WordTrace]
  refine ⟨41768164227708498469658105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111381771273889329252421613 41768164227708498469658105)
  ·
    refine ⟨31326123170781373852243579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41768164227708498469658105 31326123170781373852243579)
    ·
      refine ⟨46989184756172060778365369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31326123170781373852243579 46989184756172060778365369)
      ·
        refine ⟨35241888567129045583774027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46989184756172060778365369 35241888567129045583774027)
        ·
          refine ⟨52862832850693568375661041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35241888567129045583774027 52862832850693568375661041)
          ·
            refine ⟨39647124638020176281745781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52862832850693568375661041 39647124638020176281745781)
            ·
              refine ⟨3716917934814391526413667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39647124638020176281745781 3716917934814391526413667)
              ·
                refine ⟨5575376902221587289620501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3716917934814391526413667 5575376902221587289620501)
                ·
                  refine ⟨261345792291636904200961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5575376902221587289620501 261345792291636904200961)
                  ·
                    rfl

theorem cell23_4580722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_4580722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580722 prefixEnd_4580722 := by exact prefixLift 4580722
  have htrace : WordTrace (prefixWord ++ tailWord_4580722) baseStart_4580722 baseEnd_4580722 := by
    simpa [prefixWord, tailWord_4580722, baseEnd_4580722] using wordTrace_append hprefix tailTrace_4580722
  have hstable : (prefixWord ++ tailWord_4580722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580722).length < 2 ^ (prefixWord ++ tailWord_4580722).sum := by decide
  have hdescent : baseEnd_4580722 < baseStart_4580722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580732 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_4580732 : Nat := 118140960795 + 4580732 * 2 ^ 59
def prefixEnd_4580732 : Nat := 4983230072969 + 3 ^ 40 * 4580732 * 2
def baseEnd_4580732 : Nat := 2352117265431277098683603

theorem tailTrace_4580732 : CollatzResearch.WordTrace tailWord_4580732 prefixEnd_4580732 2352117265431277098683603 := by
  unfold tailWord_4580732
  simp only [CollatzResearch.WordTrace]
  refine ⟨83536510820398882793248225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111382014427198510390997633 83536510820398882793248225)
  ·
    refine ⟨62652383115299162094936169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83536510820398882793248225 62652383115299162094936169)
    ·
      refine ⟨46989287336474371571202127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62652383115299162094936169 46989287336474371571202127)
      ·
        refine ⟨70483931004711557356803191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46989287336474371571202127 70483931004711557356803191)
        ·
          refine ⟨105725896507067336035204787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70483931004711557356803191 105725896507067336035204787)
          ·
            refine ⟨158588844760601004052807181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105725896507067336035204787 158588844760601004052807181)
            ·
              refine ⟨59470816785225376519802693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158588844760601004052807181 59470816785225376519802693)
              ·
                refine ⟨11150778147229758097463005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59470816785225376519802693 11150778147229758097463005)
                ·
                  refine ⟨4181541805211159286548627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11150778147229758097463005 4181541805211159286548627)
                  ·
                    refine ⟨6272312707816738929822941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4181541805211159286548627 6272312707816738929822941)
                    ·
                      refine ⟨2352117265431277098683603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6272312707816738929822941 2352117265431277098683603)
                      ·
                        rfl

theorem cell23_4580732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_4580732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580732 prefixEnd_4580732 := by exact prefixLift 4580732
  have htrace : WordTrace (prefixWord ++ tailWord_4580732) baseStart_4580732 baseEnd_4580732 := by
    simpa [prefixWord, tailWord_4580732, baseEnd_4580732] using wordTrace_append hprefix tailTrace_4580732
  have hstable : (prefixWord ++ tailWord_4580732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580732).length < 2 ^ (prefixWord ++ tailWord_4580732).sum := by decide
  have hdescent : baseEnd_4580732 < baseStart_4580732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580785 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4580785 : Nat := 118140960795 + 4580785 * 2 ^ 59
def prefixEnd_4580785 : Nat := 4983230072969 + 3 ^ 40 * 4580785 * 2
def baseEnd_4580785 : Nat := 2352144479905965391320859

theorem tailTrace_4580785 : CollatzResearch.WordTrace tailWord_4580785 prefixEnd_4580785 2352144479905965391320859 := by
  unfold tailWord_4580785
  simp only [CollatzResearch.WordTrace]
  refine ⟨167074954709605755638175809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111383303139737170425450539 167074954709605755638175809)
  ·
    refine ⟨125306216032204316728631857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167074954709605755638175809 125306216032204316728631857)
    ·
      refine ⟨93979662024153237546473893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125306216032204316728631857 93979662024153237546473893)
      ·
        refine ⟨17621186629528732039963855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93979662024153237546473893 17621186629528732039963855)
        ·
          refine ⟨26431779944293098059945783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17621186629528732039963855 26431779944293098059945783)
          ·
            refine ⟨39647669916439647089918675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26431779944293098059945783 39647669916439647089918675)
            ·
              refine ⟨59471504874659470634878013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39647669916439647089918675 59471504874659470634878013)
              ·
                refine ⟨22301814327997301488079255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59471504874659470634878013 22301814327997301488079255)
                ·
                  refine ⟨33452721491995952232118883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22301814327997301488079255 33452721491995952232118883)
                  ·
                    refine ⟨50179082237993928348178325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33452721491995952232118883 50179082237993928348178325)
                    ·
                      refine ⟨2352144479905965391320859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50179082237993928348178325 2352144479905965391320859)
                      ·
                        rfl

theorem cell23_4580785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4580785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580785 prefixEnd_4580785 := by exact prefixLift 4580785
  have htrace : WordTrace (prefixWord ++ tailWord_4580785) baseStart_4580785 baseEnd_4580785 := by
    simpa [prefixWord, tailWord_4580785, baseEnd_4580785] using wordTrace_append hprefix tailTrace_4580785
  have hstable : (prefixWord ++ tailWord_4580785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580785).length < 2 ^ (prefixWord ++ tailWord_4580785).sum := by decide
  have hdescent : baseEnd_4580785 < baseStart_4580785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580789 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_4580789 : Nat := 118140960795 + 4580789 * 2 ^ 59
def prefixEnd_4580789 : Nat := 4983230072969 + 3 ^ 40 * 4580789 * 2
def baseEnd_4580789 : Nat := 2352146533828583375670841

theorem tailTrace_4580789 : CollatzResearch.WordTrace tailWord_4580789 prefixEnd_4580789 2352146533828583375670841 := by
  unfold tailWord_4580789
  simp only [CollatzResearch.WordTrace]
  refine ⟨167075100601591264321321421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111383400401060842880880947 167075100601591264321321421)
  ·
    refine ⟨62653162725596724120495533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167075100601591264321321421 62653162725596724120495533)
    ·
      refine ⟨23494936022098771545185825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62653162725596724120495533 23494936022098771545185825)
      ·
        refine ⟨17621202016574078658889369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23494936022098771545185825 17621202016574078658889369)
        ·
          refine ⟨13215901512430558994167027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17621202016574078658889369 13215901512430558994167027)
          ·
            refine ⟨19823852268645838491250541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13215901512430558994167027 19823852268645838491250541)
            ·
              refine ⟨7433944600742189434218953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19823852268645838491250541 7433944600742189434218953)
              ·
                refine ⟨5575458450556642075664215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7433944600742189434218953 5575458450556642075664215)
                ·
                  refine ⟨8363187675834963113496323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5575458450556642075664215 8363187675834963113496323)
                  ·
                    refine ⟨12544781513752444670244485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8363187675834963113496323 12544781513752444670244485)
                    ·
                      refine ⟨2352146533828583375670841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12544781513752444670244485 2352146533828583375670841)
                      ·
                        rfl

theorem cell23_4580789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_4580789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580789 prefixEnd_4580789 := by exact prefixLift 4580789
  have htrace : WordTrace (prefixWord ++ tailWord_4580789) baseStart_4580789 baseEnd_4580789 := by
    simpa [prefixWord, tailWord_4580789, baseEnd_4580789] using wordTrace_append hprefix tailTrace_4580789
  have hstable : (prefixWord ++ tailWord_4580789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580789).length < 2 ^ (prefixWord ++ tailWord_4580789).sum := by decide
  have hdescent : baseEnd_4580789 < baseStart_4580789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580825 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 2, 7]
def baseStart_4580825 : Nat := 118140960795 + 4580825 * 2 ^ 59
def prefixEnd_4580825 : Nat := 4983230072969 + 3 ^ 40 * 4580825 * 2
def baseEnd_4580825 : Nat := 784055006377381744940225

theorem tailTrace_4580825 : CollatzResearch.WordTrace tailWord_4580825 prefixEnd_4580825 784055006377381744940225 := by
  unfold tailWord_4580825
  simp only [CollatzResearch.WordTrace]
  refine ⟨167076413629460842469631929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111384275752973894979754619 167076413629460842469631929)
  ·
    refine ⟨125307310222095631852223947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167076413629460842469631929 125307310222095631852223947)
    ·
      refine ⟨187960965333143447778335921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125307310222095631852223947 187960965333143447778335921)
      ·
        refine ⟨140970723999857585833751941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187960965333143447778335921 140970723999857585833751941)
        ·
          refine ⟨26432010749973297343828489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140970723999857585833751941 26432010749973297343828489)
          ·
            refine ⟨19824008062479973007871367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26432010749973297343828489 19824008062479973007871367)
            ·
              refine ⟨29736012093719959511807051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19824008062479973007871367 29736012093719959511807051)
              ·
                refine ⟨44604018140579939267710577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29736012093719959511807051 44604018140579939267710577)
                ·
                  refine ⟨33453013605434954450782933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44604018140579939267710577 33453013605434954450782933)
                  ·
                    refine ⟨784055006377381744940225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33453013605434954450782933 784055006377381744940225)
                    ·
                      rfl

theorem cell23_4580825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_4580825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580825 prefixEnd_4580825 := by exact prefixLift 4580825
  have htrace : WordTrace (prefixWord ++ tailWord_4580825) baseStart_4580825 baseEnd_4580825 := by
    simpa [prefixWord, tailWord_4580825, baseEnd_4580825] using wordTrace_append hprefix tailTrace_4580825
  have hstable : (prefixWord ++ tailWord_4580825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580825).length < 2 ^ (prefixWord ++ tailWord_4580825).sum := by decide
  have hdescent : baseEnd_4580825 < baseStart_4580825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580839 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_4580839 : Nat := 118140960795 + 4580839 * 2 ^ 59
def prefixEnd_4580839 : Nat := 4983230072969 + 3 ^ 40 * 4580839 * 2
def baseEnd_4580839 : Nat := 2352172207861308180045611

theorem tailTrace_4580839 : CollatzResearch.WordTrace tailWord_4580839 prefixEnd_4580839 2352172207861308180045611 := by
  unfold tailWord_4580839
  simp only [CollatzResearch.WordTrace]
  refine ⟨167076924251410122860641571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111384616167606748573761047 167076924251410122860641571)
  ·
    refine ⟨250615386377115184290962357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167076924251410122860641571 250615386377115184290962357)
    ·
      refine ⟨23495192472854548527277721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 250615386377115184290962357 23495192472854548527277721)
      ·
        refine ⟨17621394354640911395458291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23495192472854548527277721 17621394354640911395458291)
        ·
          refine ⟨26432091531961367093187437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17621394354640911395458291 26432091531961367093187437)
          ·
            refine ⟨9912034324485512659945289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26432091531961367093187437 9912034324485512659945289)
            ·
              refine ⟨7434025743364134494958967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9912034324485512659945289 7434025743364134494958967)
              ·
                refine ⟨11151038615046201742438451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7434025743364134494958967 11151038615046201742438451)
                ·
                  refine ⟨16726557922569302613657677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11151038615046201742438451 16726557922569302613657677)
                  ·
                    refine ⟨6272459220963488480121629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16726557922569302613657677 6272459220963488480121629)
                    ·
                      refine ⟨2352172207861308180045611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6272459220963488480121629 2352172207861308180045611)
                      ·
                        rfl

theorem cell23_4580839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_4580839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580839 prefixEnd_4580839 := by exact prefixLift 4580839
  have htrace : WordTrace (prefixWord ++ tailWord_4580839) baseStart_4580839 baseEnd_4580839 := by
    simpa [prefixWord, tailWord_4580839, baseEnd_4580839] using wordTrace_append hprefix tailTrace_4580839
  have hstable : (prefixWord ++ tailWord_4580839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580839).length < 2 ^ (prefixWord ++ tailWord_4580839).sum := by decide
  have hdescent : baseEnd_4580839 < baseStart_4580839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580849 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 3, 3, 2]
def baseStart_4580849 : Nat := 118140960795 + 4580849 * 2 ^ 59
def prefixEnd_4580849 : Nat := 4983230072969 + 3 ^ 40 * 4580849 * 2
def baseEnd_4580849 : Nat := 2352177342667853140920565

theorem tailTrace_4580849 : CollatzResearch.WordTrace tailWord_4580849 prefixEnd_4580849 2352177342667853140920565 := by
  unfold tailWord_4580849
  simp only [CollatzResearch.WordTrace]
  refine ⟨167077288981373894568505601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111384859320915929712337067 167077288981373894568505601)
  ·
    refine ⟨125307966736030420926379201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167077288981373894568505601 125307966736030420926379201)
    ·
      refine ⟨93980975052022815694784401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125307966736030420926379201 93980975052022815694784401)
      ·
        refine ⟨70485731289017111771088301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93980975052022815694784401 70485731289017111771088301)
        ·
          refine ⟨26432149233381416914158113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70485731289017111771088301 26432149233381416914158113)
          ·
            refine ⟨19824111925036062685618585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26432149233381416914158113 19824111925036062685618585)
            ·
              refine ⟨14868083943777047014213939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19824111925036062685618585 14868083943777047014213939)
              ·
                refine ⟨22302125915665570521320909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14868083943777047014213939 22302125915665570521320909)
                ·
                  refine ⟨8363297218374588945495341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22302125915665570521320909 8363297218374588945495341)
                  ·
                    refine ⟨3136236456890470854560753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8363297218374588945495341 3136236456890470854560753)
                    ·
                      refine ⟨2352177342667853140920565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136236456890470854560753 2352177342667853140920565)
                      ·
                        rfl

theorem cell23_4580849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_4580849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580849 prefixEnd_4580849 := by exact prefixLift 4580849
  have htrace : WordTrace (prefixWord ++ tailWord_4580849) baseStart_4580849 baseEnd_4580849 := by
    simpa [prefixWord, tailWord_4580849, baseEnd_4580849] using wordTrace_append hprefix tailTrace_4580849
  have hstable : (prefixWord ++ tailWord_4580849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580849).length < 2 ^ (prefixWord ++ tailWord_4580849).sum := by decide
  have hdescent : baseEnd_4580849 < baseStart_4580849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580892 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_4580892 : Nat := 118140960795 + 4580892 * 2 ^ 59
def prefixEnd_4580892 : Nat := 4983230072969 + 3 ^ 40 * 4580892 * 2
def baseEnd_4580892 : Nat := 2352199422335996472682867

theorem tailTrace_4580892 : CollatzResearch.WordTrace tailWord_4580892 prefixEnd_4580892 2352199422335996472682867 := by
  unfold tailWord_4580892
  simp only [CollatzResearch.WordTrace]
  refine ⟨83539428660109056456160465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111385904880145408608213953 83539428660109056456160465)
  ·
    refine ⟨62654571495081792342120349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83539428660109056456160465 62654571495081792342120349)
    ·
      refine ⟨23495464310655672128295131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62654571495081792342120349 23495464310655672128295131)
      ·
        refine ⟨35243196465983508192442697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23495464310655672128295131 35243196465983508192442697)
        ·
          refine ⟨26432397349487631144332023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35243196465983508192442697 26432397349487631144332023)
          ·
            refine ⟨39648596024231446716498035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26432397349487631144332023 39648596024231446716498035)
            ·
              refine ⟨59472894036347170074747053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39648596024231446716498035 59472894036347170074747053)
              ·
                refine ⟨22302335263630188778030145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59472894036347170074747053 22302335263630188778030145)
                ·
                  refine ⟨16726751447722641583522609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22302335263630188778030145 16726751447722641583522609)
                  ·
                    refine ⟨12545063585791981187641957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16726751447722641583522609 12545063585791981187641957)
                    ·
                      refine ⟨2352199422335996472682867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12545063585791981187641957 2352199422335996472682867)
                      ·
                        rfl

theorem cell23_4580892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_4580892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580892 prefixEnd_4580892 := by exact prefixLift 4580892
  have htrace : WordTrace (prefixWord ++ tailWord_4580892) baseStart_4580892 baseEnd_4580892 := by
    simpa [prefixWord, tailWord_4580892, baseEnd_4580892] using wordTrace_append hprefix tailTrace_4580892
  have hstable : (prefixWord ++ tailWord_4580892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580892).length < 2 ^ (prefixWord ++ tailWord_4580892).sum := by decide
  have hdescent : baseEnd_4580892 < baseStart_4580892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580896 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4580896 : Nat := 118140960795 + 4580896 * 2 ^ 59
def prefixEnd_4580896 : Nat := 4983230072969 + 3 ^ 40 * 4580896 * 2
def baseEnd_4580896 : Nat := 2352201476258614457032849

theorem tailTrace_4580896 : CollatzResearch.WordTrace tailWord_4580896 prefixEnd_4580896 2352201476258614457032849 := by
  unfold tailWord_4580896
  simp only [CollatzResearch.WordTrace]
  refine ⟨83539501606101810797733271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111386002141469081063644361 83539501606101810797733271)
  ·
    refine ⟨125309252409152716196599907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83539501606101810797733271 125309252409152716196599907)
    ·
      refine ⟨187963878613729074294899861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125309252409152716196599907 187963878613729074294899861)
      ·
        refine ⟨8810806810018550357573431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 187963878613729074294899861 8810806810018550357573431)
        ·
          refine ⟨13216210215027825536360147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8810806810018550357573431 13216210215027825536360147)
          ·
            refine ⟨19824315322541738304540221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13216210215027825536360147 19824315322541738304540221)
            ·
              refine ⟨7434118245953151864202583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19824315322541738304540221 7434118245953151864202583)
              ·
                refine ⟨11151177368929727796303875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7434118245953151864202583 11151177368929727796303875)
                ·
                  refine ⟨16726766053394591694455813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11151177368929727796303875 16726766053394591694455813)
                  ·
                    refine ⟨3136268635011485942710465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16726766053394591694455813 3136268635011485942710465)
                    ·
                      refine ⟨2352201476258614457032849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136268635011485942710465 2352201476258614457032849)
                      ·
                        rfl

theorem cell23_4580896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4580896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580896 prefixEnd_4580896 := by exact prefixLift 4580896
  have htrace : WordTrace (prefixWord ++ tailWord_4580896) baseStart_4580896 baseEnd_4580896 := by
    simpa [prefixWord, tailWord_4580896, baseEnd_4580896] using wordTrace_append hprefix tailTrace_4580896
  have hstable : (prefixWord ++ tailWord_4580896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580896).length < 2 ^ (prefixWord ++ tailWord_4580896).sum := by decide
  have hdescent : baseEnd_4580896 < baseStart_4580896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580919 : List Nat := [1, 1, 3, 1, 2, 4, 3, 3, 5]
def baseStart_4580919 : Nat := 118140960795 + 4580919 * 2 ^ 59
def prefixEnd_4580919 : Nat := 4983230072969 + 3 ^ 40 * 4580919 * 2
def baseEnd_4580919 : Nat := 261357031812629763005027

theorem tailTrace_4580919 : CollatzResearch.WordTrace tailWord_4580919 prefixEnd_4580919 261357031812629763005027 := by
  unfold tailWord_4580919
  simp only [CollatzResearch.WordTrace]
  refine ⟨167079842091120296523553811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111386561394080197682369207 167079842091120296523553811)
  ·
    refine ⟨250619763136680444785330717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167079842091120296523553811 250619763136680444785330717)
    ·
      refine ⟨93982411176255166794499019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250619763136680444785330717 93982411176255166794499019)
      ·
        refine ⟨140973616764382750191748529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93982411176255166794499019 140973616764382750191748529)
        ·
          refine ⟨105730212573287062643811397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140973616764382750191748529 105730212573287062643811397)
          ·
            refine ⟨19824414857491324245714637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105730212573287062643811397 19824414857491324245714637)
            ·
              refine ⟨7434155571559246592142989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19824414857491324245714637 7434155571559246592142989)
              ·
                refine ⟨2787808339334717472053621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7434155571559246592142989 2787808339334717472053621)
                ·
                  refine ⟨261357031812629763005027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2787808339334717472053621 261357031812629763005027)
                  ·
                    rfl

theorem cell23_4580919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 5].length) (baseStart_4580919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580919 prefixEnd_4580919 := by exact prefixLift 4580919
  have htrace : WordTrace (prefixWord ++ tailWord_4580919) baseStart_4580919 baseEnd_4580919 := by
    simpa [prefixWord, tailWord_4580919, baseEnd_4580919] using wordTrace_append hprefix tailTrace_4580919
  have hstable : (prefixWord ++ tailWord_4580919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580919).length < 2 ^ (prefixWord ++ tailWord_4580919).sum := by decide
  have hdescent : baseEnd_4580919 < baseStart_4580919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4580952 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_4580952 : Nat := 118140960795 + 4580952 * 2 ^ 59
def prefixEnd_4580952 : Nat := 4983230072969 + 3 ^ 40 * 4580952 * 2
def baseEnd_4580952 : Nat := 2352230231175266237932591

theorem tailTrace_4580952 : CollatzResearch.WordTrace tailWord_4580952 prefixEnd_4580952 2352230231175266237932591 := by
  unfold tailWord_4580952
  simp only [CollatzResearch.WordTrace]
  refine ⟨83540522850000371579752555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111387363800000495439670073 83540522850000371579752555)
  ·
    refine ⟨125310784275000557369628833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83540522850000371579752555 125310784275000557369628833)
    ·
      refine ⟨93983088206250418027221625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125310784275000557369628833 93983088206250418027221625)
      ·
        refine ⟨70487316154687813520416219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93983088206250418027221625 70487316154687813520416219)
        ·
          refine ⟨105730974232031720280624329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70487316154687813520416219 105730974232031720280624329)
          ·
            refine ⟨79298230674023790210468247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105730974232031720280624329 79298230674023790210468247)
            ·
              refine ⟨118947346011035685315702371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79298230674023790210468247 118947346011035685315702371)
              ·
                refine ⟨178421019016553527973553557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118947346011035685315702371 178421019016553527973553557)
                ·
                  refine ⟨8363485266400946623760323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 178421019016553527973553557 8363485266400946623760323)
                  ·
                    refine ⟨12545227899601419935640485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8363485266400946623760323 12545227899601419935640485)
                    ·
                      refine ⟨2352230231175266237932591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12545227899601419935640485 2352230231175266237932591)
                      ·
                        rfl

theorem cell23_4580952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_4580952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4580952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4580952 prefixEnd_4580952 := by exact prefixLift 4580952
  have htrace : WordTrace (prefixWord ++ tailWord_4580952) baseStart_4580952 baseEnd_4580952 := by
    simpa [prefixWord, tailWord_4580952, baseEnd_4580952] using wordTrace_append hprefix tailTrace_4580952
  have hstable : (prefixWord ++ tailWord_4580952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4580952).length < 2 ^ (prefixWord ++ tailWord_4580952).sum := by decide
  have hdescent : baseEnd_4580952 < baseStart_4580952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4580952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581039 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 1, 5]
def baseStart_4581039 : Nat := 118140960795 + 4581039 * 2 ^ 59
def prefixEnd_4581039 : Nat := 4983230072969 + 3 ^ 40 * 4581039 * 2
def baseEnd_4581039 : Nat := 784091634664069132514897

theorem tailTrace_4581039 : CollatzResearch.WordTrace tailWord_4581039 prefixEnd_4581039 784091634664069132514897 := by
  unfold tailWord_4581039
  simp only [CollatzResearch.WordTrace]
  refine ⟨167084218850685557017922171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111389479233790371345281447 167084218850685557017922171)
  ·
    refine ⟨250626328276028335526883257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167084218850685557017922171 250626328276028335526883257)
    ·
      refine ⟨187969746207021251645162443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250626328276028335526883257 187969746207021251645162443)
      ·
        refine ⟨281954619310531877467743665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187969746207021251645162443 281954619310531877467743665)
        ·
          refine ⟨211465964482898908100807749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281954619310531877467743665 211465964482898908100807749)
          ·
            refine ⟨39649868340543545268901453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211465964482898908100807749 39649868340543545268901453)
            ·
              refine ⟨14868700627703829475838045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39649868340543545268901453 14868700627703829475838045)
              ·
                refine ⟨5575762735388936053439267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14868700627703829475838045 5575762735388936053439267)
                ·
                  refine ⟨8363644103083404080158901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5575762735388936053439267 8363644103083404080158901)
                  ·
                    refine ⟨784091634664069132514897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8363644103083404080158901 784091634664069132514897)
                    ·
                      rfl

theorem cell23_4581039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 5].length) (baseStart_4581039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581039 prefixEnd_4581039 := by exact prefixLift 4581039
  have htrace : WordTrace (prefixWord ++ tailWord_4581039) baseStart_4581039 baseEnd_4581039 := by
    simpa [prefixWord, tailWord_4581039, baseEnd_4581039] using wordTrace_append hprefix tailTrace_4581039
  have hstable : (prefixWord ++ tailWord_4581039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581039).length < 2 ^ (prefixWord ++ tailWord_4581039).sum := by decide
  have hdescent : baseEnd_4581039 < baseStart_4581039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581046 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_4581046 : Nat := 118140960795 + 4581046 * 2 ^ 59
def prefixEnd_4581046 : Nat := 4983230072969 + 3 ^ 40 * 4581046 * 2
def baseEnd_4581046 : Nat := 2352278498356788870157159

theorem tailTrace_4581046 : CollatzResearch.WordTrace tailWord_4581046 prefixEnd_4581046 2352278498356788870157159 := by
  unfold tailWord_4581046
  simp only [CollatzResearch.WordTrace]
  refine ⟨10442779635103762325839187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111389649441106798142284661 10442779635103762325839187)
  ·
    refine ⟨15664169452655643488758781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10442779635103762325839187 15664169452655643488758781)
    ·
      refine ⟨5874063544745866308284543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15664169452655643488758781 5874063544745866308284543)
      ·
        refine ⟨8811095317118799462426815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5874063544745866308284543 8811095317118799462426815)
        ·
          refine ⟨13216642975678199193640223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8811095317118799462426815 13216642975678199193640223)
          ·
            refine ⟨19824964463517298790460335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13216642975678199193640223 19824964463517298790460335)
            ·
              refine ⟨29737446695275948185690503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19824964463517298790460335 29737446695275948185690503)
              ·
                refine ⟨44606170042913922278535755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29737446695275948185690503 44606170042913922278535755)
                ·
                  refine ⟨66909255064370883417803633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44606170042913922278535755 66909255064370883417803633)
                  ·
                    refine ⟨50181941298278162563352725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66909255064370883417803633 50181941298278162563352725)
                    ·
                      refine ⟨2352278498356788870157159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50181941298278162563352725 2352278498356788870157159)
                      ·
                        rfl

theorem cell23_4581046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_4581046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581046 prefixEnd_4581046 := by exact prefixLift 4581046
  have htrace : WordTrace (prefixWord ++ tailWord_4581046) baseStart_4581046 baseEnd_4581046 := by
    simpa [prefixWord, tailWord_4581046, baseEnd_4581046] using wordTrace_append hprefix tailTrace_4581046
  have hstable : (prefixWord ++ tailWord_4581046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581046).length < 2 ^ (prefixWord ++ tailWord_4581046).sum := by decide
  have hdescent : baseEnd_4581046 < baseStart_4581046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581053 : List Nat := [1, 4, 1, 2, 1, 2, 1, 6, 1, 1, 3]
def baseStart_4581053 : Nat := 118140960795 + 4581053 * 2 ^ 59
def prefixEnd_4581053 : Nat := 4983230072969 + 3 ^ 40 * 4581053 * 2
def baseEnd_4581053 : Nat := 2352282092721370342769627

theorem tailTrace_4581053 : CollatzResearch.WordTrace tailWord_4581053 prefixEnd_4581053 2352282092721370342769627 := by
  unfold tailWord_4581053
  simp only [CollatzResearch.WordTrace]
  refine ⟨167084729472634837408931813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111389819648423224939287875 167084729472634837408931813)
  ·
    refine ⟨31328386776119032014174715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167084729472634837408931813 31328386776119032014174715)
    ·
      refine ⟨46992580164178548021262073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31328386776119032014174715 46992580164178548021262073)
      ·
        refine ⟨35244435123133911015946555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46992580164178548021262073 35244435123133911015946555)
        ·
          refine ⟨52866652684700866523919833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35244435123133911015946555 52866652684700866523919833)
          ·
            refine ⟨39649989513525649892939875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52866652684700866523919833 39649989513525649892939875)
            ·
              refine ⟨59474984270288474839409813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39649989513525649892939875 59474984270288474839409813)
              ·
                refine ⟨2787889887669772258097335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59474984270288474839409813 2787889887669772258097335)
                ·
                  refine ⟨4181834831504658387146003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2787889887669772258097335 4181834831504658387146003)
                  ·
                    refine ⟨6272752247256987580719005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4181834831504658387146003 6272752247256987580719005)
                    ·
                      refine ⟨2352282092721370342769627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6272752247256987580719005 2352282092721370342769627)
                      ·
                        rfl

theorem cell23_4581053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_4581053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581053 prefixEnd_4581053 := by exact prefixLift 4581053
  have htrace : WordTrace (prefixWord ++ tailWord_4581053) baseStart_4581053 baseEnd_4581053 := by
    simpa [prefixWord, tailWord_4581053, baseEnd_4581053] using wordTrace_append hprefix tailTrace_4581053
  have hstable : (prefixWord ++ tailWord_4581053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581053).length < 2 ^ (prefixWord ++ tailWord_4581053).sum := by decide
  have hdescent : baseEnd_4581053 < baseStart_4581053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581096 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_4581096 : Nat := 118140960795 + 4581096 * 2 ^ 59
def prefixEnd_4581096 : Nat := 4983230072969 + 3 ^ 40 * 4581096 * 2
def baseEnd_4581096 : Nat := 2352304172389513674531929

theorem tailTrace_4581096 : CollatzResearch.WordTrace tailWord_4581096 prefixEnd_4581096 2352304172389513674531929 := by
  unfold tailWord_4581096
  simp only [CollatzResearch.WordTrace]
  refine ⟨83543148905739527876373571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111390865207652703835164761 83543148905739527876373571)
  ·
    refine ⟨125314723358609291814560357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83543148905739527876373571 125314723358609291814560357)
    ·
      refine ⟨23496510629739242215230067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125314723358609291814560357 23496510629739242215230067)
      ·
        refine ⟨35244765944608863322845101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23496510629739242215230067 35244765944608863322845101)
        ·
          refine ⟨13216787229228323746066913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35244765944608863322845101 13216787229228323746066913)
          ·
            refine ⟨9912590421921242809550185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13216787229228323746066913 9912590421921242809550185)
            ·
              refine ⟨7434442816440932107162639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9912590421921242809550185 7434442816440932107162639)
              ·
                refine ⟨11151664224661398160743959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7434442816440932107162639 11151664224661398160743959)
                ·
                  refine ⟨16727496336992097241115939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11151664224661398160743959 16727496336992097241115939)
                  ·
                    refine ⟨25091244505488145861673909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16727496336992097241115939 25091244505488145861673909)
                    ·
                      refine ⟨2352304172389513674531929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25091244505488145861673909 2352304172389513674531929)
                      ·
                        rfl

theorem cell23_4581096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_4581096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581096 prefixEnd_4581096 := by exact prefixLift 4581096
  have htrace : WordTrace (prefixWord ++ tailWord_4581096) baseStart_4581096 baseEnd_4581096 := by
    simpa [prefixWord, tailWord_4581096, baseEnd_4581096] using wordTrace_append hprefix tailTrace_4581096
  have hstable : (prefixWord ++ tailWord_4581096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581096).length < 2 ^ (prefixWord ++ tailWord_4581096).sum := by decide
  have hdescent : baseEnd_4581096 < baseStart_4581096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581110 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_4581110 : Nat := 118140960795 + 4581110 * 2 ^ 59
def prefixEnd_4581110 : Nat := 4983230072969 + 3 ^ 40 * 4581110 * 2
def baseEnd_4581110 : Nat := 2352311361118676619756865

theorem tailTrace_4581110 : CollatzResearch.WordTrace tailWord_4581110 prefixEnd_4581110 2352311361118676619756865 := by
  unfold tailWord_4581110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10442925527089271008984799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111391205622285557429171189 10442925527089271008984799)
  ·
    refine ⟨15664388290633906513477199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10442925527089271008984799 15664388290633906513477199)
    ·
      refine ⟨23496582435950859770215799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15664388290633906513477199 23496582435950859770215799)
      ·
        refine ⟨35244873653926289655323699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23496582435950859770215799 35244873653926289655323699)
        ·
          refine ⟨52867310480889434482985549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35244873653926289655323699 52867310480889434482985549)
          ·
            refine ⟨19825241430333537931119581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52867310480889434482985549 19825241430333537931119581)
            ·
              refine ⟨7434465536375076724169843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19825241430333537931119581 7434465536375076724169843)
              ·
                refine ⟨11151698304562615086254765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7434465536375076724169843 11151698304562615086254765)
                ·
                  refine ⟨4181886864210980657345537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11151698304562615086254765 4181886864210980657345537)
                  ·
                    refine ⟨3136415148158235493009153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4181886864210980657345537 3136415148158235493009153)
                    ·
                      refine ⟨2352311361118676619756865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136415148158235493009153 2352311361118676619756865)
                      ·
                        rfl

theorem cell23_4581110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_4581110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581110 prefixEnd_4581110 := by exact prefixLift 4581110
  have htrace : WordTrace (prefixWord ++ tailWord_4581110) baseStart_4581110 baseEnd_4581110 := by
    simpa [prefixWord, tailWord_4581110, baseEnd_4581110] using wordTrace_append hprefix tailTrace_4581110
  have hstable : (prefixWord ++ tailWord_4581110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581110).length < 2 ^ (prefixWord ++ tailWord_4581110).sum := by decide
  have hdescent : baseEnd_4581110 < baseStart_4581110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581160 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_4581160 : Nat := 118140960795 + 4581160 * 2 ^ 59
def prefixEnd_4581160 : Nat := 4983230072969 + 3 ^ 40 * 4581160 * 2
def baseEnd_4581160 : Nat := 2352337035151401424131635

theorem tailTrace_4581160 : CollatzResearch.WordTrace tailWord_4581160 prefixEnd_4581160 2352337035151401424131635 := by
  unfold tailWord_4581160
  simp only [CollatzResearch.WordTrace]
  refine ⟨83544316041623597341538467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111392421388831463122051289 83544316041623597341538467)
  ·
    refine ⟨125316474062435396012307701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83544316041623597341538467 125316474062435396012307701)
    ·
      refine ⟨11748419443353318376153847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125316474062435396012307701 11748419443353318376153847)
      ·
        refine ⟨17622629165029977564230771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11748419443353318376153847 17622629165029977564230771)
        ·
          refine ⟨26433943747544966346346157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17622629165029977564230771 26433943747544966346346157)
          ·
            refine ⟨9912728905329362379879809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26433943747544966346346157 9912728905329362379879809)
            ·
              refine ⟨7434546678997021784909857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9912728905329362379879809 7434546678997021784909857)
              ·
                refine ⟨5575910009247766338682393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7434546678997021784909857 5575910009247766338682393)
                ·
                  refine ⟨4181932506935824754011795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5575910009247766338682393 4181932506935824754011795)
                  ·
                    refine ⟨6272898760403737131017693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4181932506935824754011795 6272898760403737131017693)
                    ·
                      refine ⟨2352337035151401424131635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6272898760403737131017693 2352337035151401424131635)
                      ·
                        rfl

theorem cell23_4581160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_4581160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581160 prefixEnd_4581160 := by exact prefixLift 4581160
  have htrace : WordTrace (prefixWord ++ tailWord_4581160) baseStart_4581160 baseEnd_4581160 := by
    simpa [prefixWord, tailWord_4581160, baseEnd_4581160] using wordTrace_append hprefix tailTrace_4581160
  have hstable : (prefixWord ++ tailWord_4581160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581160).length < 2 ^ (prefixWord ++ tailWord_4581160).sum := by decide
  have hdescent : baseEnd_4581160 < baseStart_4581160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581189 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 7]
def baseStart_4581189 : Nat := 118140960795 + 4581189 * 2 ^ 59
def prefixEnd_4581189 : Nat := 4983230072969 + 3 ^ 40 * 4581189 * 2
def baseEnd_4581189 : Nat := 261372436232264645629889

theorem tailTrace_4581189 : CollatzResearch.WordTrace tailWord_4581189 prefixEnd_4581189 261372436232264645629889 := by
  unfold tailWord_4581189
  simp only [CollatzResearch.WordTrace]
  refine ⟨167089689800142132635882621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111393126533428088423921747 167089689800142132635882621)
  ·
    refine ⟨62658633675053299738455983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167089689800142132635882621 62658633675053299738455983)
    ·
      refine ⟨93987950512579949607683975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62658633675053299738455983 93987950512579949607683975)
      ·
        refine ⟨140981925768869924411525963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93987950512579949607683975 140981925768869924411525963)
        ·
          refine ⟨211472888653304886617288945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140981925768869924411525963 211472888653304886617288945)
          ·
            refine ⟨158604666489978664962966709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211472888653304886617288945 158604666489978664962966709)
            ·
              refine ⟨14869187483435499840278129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158604666489978664962966709 14869187483435499840278129)
              ·
                refine ⟨11151890612576624880208597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14869187483435499840278129 11151890612576624880208597)
                ·
                  refine ⟨261372436232264645629889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11151890612576624880208597 261372436232264645629889)
                  ·
                    rfl

theorem cell23_4581189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_4581189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581189 prefixEnd_4581189 := by exact prefixLift 4581189
  have htrace : WordTrace (prefixWord ++ tailWord_4581189) baseStart_4581189 baseEnd_4581189 := by
    simpa [prefixWord, tailWord_4581189, baseEnd_4581189] using wordTrace_append hprefix tailTrace_4581189
  have hstable : (prefixWord ++ tailWord_4581189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581189).length < 2 ^ (prefixWord ++ tailWord_4581189).sum := by decide
  have hdescent : baseEnd_4581189 < baseStart_4581189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581216 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 3]
def baseStart_4581216 : Nat := 118140960795 + 4581216 * 2 ^ 59
def prefixEnd_4581216 : Nat := 4983230072969 + 3 ^ 40 * 4581216 * 2
def baseEnd_4581216 : Nat := 2352365790068053205031377

theorem tailTrace_4581216 : CollatzResearch.WordTrace tailWord_4581216 prefixEnd_4581216 2352365790068053205031377 := by
  unfold tailWord_4581216
  simp only [CollatzResearch.WordTrace]
  refine ⟨83545337285522158123557751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111393783047362877498077001 83545337285522158123557751)
  ·
    refine ⟨125318005928283237185336627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83545337285522158123557751 125318005928283237185336627)
    ·
      refine ⟨187977008892424855778004941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125318005928283237185336627 187977008892424855778004941)
      ·
        refine ⟨70491378334659320916751853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187977008892424855778004941 70491378334659320916751853)
        ·
          refine ⟨26434266875497245343781945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70491378334659320916751853 26434266875497245343781945)
          ·
            refine ⟨19825700156622934007836459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26434266875497245343781945 19825700156622934007836459)
            ·
              refine ⟨29738550234934401011754689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19825700156622934007836459 29738550234934401011754689)
              ·
                refine ⟨22303912676200800758816017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29738550234934401011754689 22303912676200800758816017)
                ·
                  refine ⟨16727934507150600569112013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22303912676200800758816017 16727934507150600569112013)
                  ·
                    refine ⟨6272975440181475213417005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16727934507150600569112013 6272975440181475213417005)
                    ·
                      refine ⟨2352365790068053205031377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6272975440181475213417005 2352365790068053205031377)
                      ·
                        rfl

theorem cell23_4581216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_4581216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581216 prefixEnd_4581216 := by exact prefixLift 4581216
  have htrace : WordTrace (prefixWord ++ tailWord_4581216) baseStart_4581216 baseEnd_4581216 := by
    simpa [prefixWord, tailWord_4581216, baseEnd_4581216] using wordTrace_append hprefix tailTrace_4581216
  have hstable : (prefixWord ++ tailWord_4581216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581216).length < 2 ^ (prefixWord ++ tailWord_4581216).sum := by decide
  have hdescent : baseEnd_4581216 < baseStart_4581216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581259 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 5]
def baseStart_4581259 : Nat := 118140960795 + 4581259 * 2 ^ 59
def prefixEnd_4581259 : Nat := 4983230072969 + 3 ^ 40 * 4581259 * 2
def baseEnd_4581259 : Nat := 2352387869736196536793679

theorem tailTrace_4581259 : CollatzResearch.WordTrace tailWord_4581259 prefixEnd_4581259 2352387869736196536793679 := by
  unfold tailWord_4581259
  simp only [CollatzResearch.WordTrace]
  refine ⟨167092242909888534590930831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111394828606592356393953887 167092242909888534590930831)
  ·
    refine ⟨250638364364832801886396247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167092242909888534590930831 250638364364832801886396247)
    ·
      refine ⟨375957546547249202829594371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250638364364832801886396247 375957546547249202829594371)
      ·
        refine ⟨563936319820873804244391557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375957546547249202829594371 563936319820873804244391557)
        ·
          refine ⟨105738059966413838295823417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 563936319820873804244391557 105738059966413838295823417)
          ·
            refine ⟨79303544974810378721867563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105738059966413838295823417 79303544974810378721867563)
            ·
              refine ⟨118955317462215568082801345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79303544974810378721867563 118955317462215568082801345)
              ·
                refine ⟨89216488096661676062101009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118955317462215568082801345 89216488096661676062101009)
                ·
                  refine ⟨66912366072496257046575757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89216488096661676062101009 66912366072496257046575757)
                  ·
                    refine ⟨25092137277186096392465909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66912366072496257046575757 25092137277186096392465909)
                    ·
                      refine ⟨2352387869736196536793679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25092137277186096392465909 2352387869736196536793679)
                      ·
                        rfl

theorem cell23_4581259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_4581259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581259 prefixEnd_4581259 := by exact prefixLift 4581259
  have htrace : WordTrace (prefixWord ++ tailWord_4581259) baseStart_4581259 baseEnd_4581259 := by
    simpa [prefixWord, tailWord_4581259, baseEnd_4581259] using wordTrace_append hprefix tailTrace_4581259
  have hstable : (prefixWord ++ tailWord_4581259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581259).length < 2 ^ (prefixWord ++ tailWord_4581259).sum := by decide
  have hdescent : baseEnd_4581259 < baseStart_4581259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581310 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_4581310 : Nat := 118140960795 + 4581310 * 2 ^ 59
def prefixEnd_4581310 : Nat := 4983230072969 + 3 ^ 40 * 4581310 * 2
def baseEnd_4581310 : Nat := 2352414057249575837255945

theorem tailTrace_4581310 : CollatzResearch.WordTrace tailWord_4581310 prefixEnd_4581310 2352414057249575837255945 := by
  unfold tailWord_4581310
  simp only [CollatzResearch.WordTrace]
  refine ⟨20886762879087971287629673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111396068688469180200691589 20886762879087971287629673)
  ·
    refine ⟨15665072159315978465722255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20886762879087971287629673 15665072159315978465722255)
    ·
      refine ⟨23497608238973967698583383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15665072159315978465722255 23497608238973967698583383)
      ·
        refine ⟨35246412358460951547875075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23497608238973967698583383 35246412358460951547875075)
        ·
          refine ⟨52869618537691427321812613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35246412358460951547875075 52869618537691427321812613)
          ·
            refine ⟨9913053475817142622839865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52869618537691427321812613 9913053475817142622839865)
            ·
              refine ⟨7434790106862856967129899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9913053475817142622839865 7434790106862856967129899)
              ·
                refine ⟨11152185160294285450694849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7434790106862856967129899 11152185160294285450694849)
                ·
                  refine ⟨8364138870220714088021137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11152185160294285450694849 8364138870220714088021137)
                  ·
                    refine ⟨6273104152665535566015853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8364138870220714088021137 6273104152665535566015853)
                    ·
                      refine ⟨2352414057249575837255945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6273104152665535566015853 2352414057249575837255945)
                      ·
                        rfl

theorem cell23_4581310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_4581310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581310 prefixEnd_4581310 := by exact prefixLift 4581310
  have htrace : WordTrace (prefixWord ++ tailWord_4581310) baseStart_4581310 baseEnd_4581310 := by
    simpa [prefixWord, tailWord_4581310, baseEnd_4581310] using wordTrace_append hprefix tailTrace_4581310
  have hstable : (prefixWord ++ tailWord_4581310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581310).length < 2 ^ (prefixWord ++ tailWord_4581310).sum := by decide
  have hdescent : baseEnd_4581310 < baseStart_4581310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581330 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 6]
def baseStart_4581330 : Nat := 118140960795 + 4581330 * 2 ^ 59
def prefixEnd_4581330 : Nat := 4983230072969 + 3 ^ 40 * 4581330 * 2
def baseEnd_4581330 : Nat := 261380480762518417667317

theorem tailTrace_4581330 : CollatzResearch.WordTrace tailWord_4581330 prefixEnd_4581330 261380480762518417667317 := by
  unfold tailWord_4581330
  simp only [CollatzResearch.WordTrace]
  refine ⟨41773708123157828429191361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111396554995087542477843629 41773708123157828429191361)
  ·
    refine ⟨31330281092368371321893521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41773708123157828429191361 31330281092368371321893521)
    ·
      refine ⟨23497710819276278491420141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31330281092368371321893521 23497710819276278491420141)
      ·
        refine ⟨8811641557228604434282553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23497710819276278491420141 8811641557228604434282553)
        ·
          refine ⟨6608731167921453325711915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8811641557228604434282553 6608731167921453325711915)
          ·
            refine ⟨9913096751882179988567873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6608731167921453325711915 9913096751882179988567873)
            ·
              refine ⟨7434822563911634991425905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9913096751882179988567873 7434822563911634991425905)
              ·
                refine ⟨5576116922933726243569429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7434822563911634991425905 5576116922933726243569429)
                ·
                  refine ⟨261380480762518417667317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5576116922933726243569429 261380480762518417667317)
                  ·
                    rfl

theorem cell23_4581330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_4581330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581330 prefixEnd_4581330 := by exact prefixLift 4581330
  have htrace : WordTrace (prefixWord ++ tailWord_4581330) baseStart_4581330 baseEnd_4581330 := by
    simpa [prefixWord, tailWord_4581330, baseEnd_4581330] using wordTrace_append hprefix tailTrace_4581330
  have hstable : (prefixWord ++ tailWord_4581330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581330).length < 2 ^ (prefixWord ++ tailWord_4581330).sum := by decide
  have hdescent : baseEnd_4581330 < baseStart_4581330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581334 : List Nat := [5, 2, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_4581334 : Nat := 118140960795 + 4581334 * 2 ^ 59
def prefixEnd_4581334 : Nat := 4983230072969 + 3 ^ 40 * 4581334 * 2
def baseEnd_4581334 : Nat := 784142126928427914451945

theorem tailTrace_4581334 : CollatzResearch.WordTrace tailWord_4581334 prefixEnd_4581334 784142126928427914451945 := by
  unfold tailWord_4581334
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443436149038551399994441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111396652256411214933274037 10443436149038551399994441)
  ·
    refine ⟨7832577111778913549995831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10443436149038551399994441 7832577111778913549995831)
    ·
      refine ⟨11748865667668370324993747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7832577111778913549995831 11748865667668370324993747)
      ·
        refine ⟨17623298501502555487490621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11748865667668370324993747 17623298501502555487490621)
        ·
          refine ⟨6608736938063458307808983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17623298501502555487490621 6608736938063458307808983)
          ·
            refine ⟨9913105407095187461713475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6608736938063458307808983 9913105407095187461713475)
            ·
              refine ⟨14869658110642781192570213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9913105407095187461713475 14869658110642781192570213)
              ·
                refine ⟨2788060895745521473606915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14869658110642781192570213 2788060895745521473606915)
                ·
                  refine ⟨4182091343618282210410373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788060895745521473606915 4182091343618282210410373)
                  ·
                    refine ⟨784142126928427914451945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182091343618282210410373 784142126928427914451945)
                    ·
                      rfl

theorem cell23_4581334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_4581334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581334 prefixEnd_4581334 := by exact prefixLift 4581334
  have htrace : WordTrace (prefixWord ++ tailWord_4581334) baseStart_4581334 baseEnd_4581334 := by
    simpa [prefixWord, tailWord_4581334, baseEnd_4581334] using wordTrace_append hprefix tailTrace_4581334
  have hstable : (prefixWord ++ tailWord_4581334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581334).length < 2 ^ (prefixWord ++ tailWord_4581334).sum := by decide
  have hdescent : baseEnd_4581334 < baseStart_4581334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581374 : List Nat := [4, 2, 2, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4581374 : Nat := 118140960795 + 4581374 * 2 ^ 59
def prefixEnd_4581374 : Nat := 4983230072969 + 3 ^ 40 * 4581374 * 2
def baseEnd_4581374 : Nat := 2352446920011463586855651

theorem tailTrace_4581374 : CollatzResearch.WordTrace tailWord_4581374 prefixEnd_4581374 2352446920011463586855651 := by
  unfold tailWord_4581374
  simp only [CollatzResearch.WordTrace]
  refine ⟨20887054663058988653920897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111397624869647939487578117 20887054663058988653920897)
  ·
    refine ⟨15665290997294241490440673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20887054663058988653920897 15665290997294241490440673)
    ·
      refine ⟨11748968247970681117830505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15665290997294241490440673 11748968247970681117830505)
      ·
        refine ⟨8811726185978010838372879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11748968247970681117830505 8811726185978010838372879)
        ·
          refine ⟨13217589278967016257559319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8811726185978010838372879 13217589278967016257559319)
          ·
            refine ⟨19826383918450524386338979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13217589278967016257559319 19826383918450524386338979)
            ·
              refine ⟨29739575877675786579508469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19826383918450524386338979 29739575877675786579508469)
              ·
                refine ⟨2788085238532104991828919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29739575877675786579508469 2788085238532104991828919)
                ·
                  refine ⟨4182127857798157487743379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788085238532104991828919 4182127857798157487743379)
                  ·
                    refine ⟨6273191786697236231615069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4182127857798157487743379 6273191786697236231615069)
                    ·
                      refine ⟨2352446920011463586855651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6273191786697236231615069 2352446920011463586855651)
                      ·
                        rfl

theorem cell23_4581374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4581374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581374 prefixEnd_4581374 := by exact prefixLift 4581374
  have htrace : WordTrace (prefixWord ++ tailWord_4581374) baseStart_4581374 baseEnd_4581374 := by
    simpa [prefixWord, tailWord_4581374, baseEnd_4581374] using wordTrace_append hprefix tailTrace_4581374
  have hstable : (prefixWord ++ tailWord_4581374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581374).length < 2 ^ (prefixWord ++ tailWord_4581374).sum := by decide
  have hdescent : baseEnd_4581374 < baseStart_4581374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581376 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_4581376 : Nat := 118140960795 + 4581376 * 2 ^ 59
def prefixEnd_4581376 : Nat := 4983230072969 + 3 ^ 40 * 4581376 * 2
def baseEnd_4581376 : Nat := 2352447946972772579030641

theorem tailTrace_4581376 : CollatzResearch.WordTrace tailWord_4581376 prefixEnd_4581376 2352447946972772579030641 := by
  unfold tailWord_4581376
  simp only [CollatzResearch.WordTrace]
  refine ⟨83548255125232331786469991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111397673500309775715293321 83548255125232331786469991)
  ·
    refine ⟨125322382687848497679704987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83548255125232331786469991 125322382687848497679704987)
    ·
      refine ⟨187983574031772746519557481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125322382687848497679704987 187983574031772746519557481)
      ·
        refine ⟨140987680523829559889668111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187983574031772746519557481 140987680523829559889668111)
        ·
          refine ⟨211481520785744339834502167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140987680523829559889668111 211481520785744339834502167)
          ·
            refine ⟨317222281178616509751753251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211481520785744339834502167 317222281178616509751753251)
            ·
              refine ⟨475833421767924764627629877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317222281178616509751753251 475833421767924764627629877)
              ·
                refine ⟨44609383290742946683840301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 475833421767924764627629877 44609383290742946683840301)
                ·
                  refine ⟨16728518734028605006440113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44609383290742946683840301 16728518734028605006440113)
                  ·
                    refine ⟨12546389050521453754830085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16728518734028605006440113 12546389050521453754830085)
                    ·
                      refine ⟨2352447946972772579030641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12546389050521453754830085 2352447946972772579030641)
                      ·
                        rfl

theorem cell23_4581376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_4581376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581376 prefixEnd_4581376 := by exact prefixLift 4581376
  have htrace : WordTrace (prefixWord ++ tailWord_4581376) baseStart_4581376 baseEnd_4581376 := by
    simpa [prefixWord, tailWord_4581376, baseEnd_4581376] using wordTrace_append hprefix tailTrace_4581376
  have hstable : (prefixWord ++ tailWord_4581376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581376).length < 2 ^ (prefixWord ++ tailWord_4581376).sum := by decide
  have hdescent : baseEnd_4581376 < baseStart_4581376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581430 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_4581430 : Nat := 118140960795 + 4581430 * 2 ^ 59
def prefixEnd_4581430 : Nat := 4983230072969 + 3 ^ 40 * 4581430 * 2
def baseEnd_4581430 : Nat := 2352475674928115367755393

theorem tailTrace_4581430 : CollatzResearch.WordTrace tailWord_4581430 prefixEnd_4581430 2352475674928115367755393 := by
  unfold tailWord_4581430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443654987016814424712859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111398986528179353863603829 10443654987016814424712859)
  ·
    refine ⟨15665482480525221637069289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10443654987016814424712859 15665482480525221637069289)
    ·
      refine ⟨11749111860393916227801967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15665482480525221637069289 11749111860393916227801967)
      ·
        refine ⟨17623667790590874341702951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11749111860393916227801967 17623667790590874341702951)
        ·
          refine ⟨26435501685886311512554427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17623667790590874341702951 26435501685886311512554427)
          ·
            refine ⟨39653252528829467268831641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26435501685886311512554427 39653252528829467268831641)
            ·
              refine ⟨29739939396622100451623731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39653252528829467268831641 29739939396622100451623731)
              ·
                refine ⟨44609909094933150677435597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29739939396622100451623731 44609909094933150677435597)
                ·
                  refine ⟨16728715910599931504038349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44609909094933150677435597 16728715910599931504038349)
                  ·
                    refine ⟨6273268466474974314014381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16728715910599931504038349 6273268466474974314014381)
                    ·
                      refine ⟨2352475674928115367755393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6273268466474974314014381 2352475674928115367755393)
                      ·
                        rfl

theorem cell23_4581430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_4581430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581430 prefixEnd_4581430 := by exact prefixLift 4581430
  have htrace : WordTrace (prefixWord ++ tailWord_4581430) baseStart_4581430 baseEnd_4581430 := by
    simpa [prefixWord, tailWord_4581430, baseEnd_4581430] using wordTrace_append hprefix tailTrace_4581430
  have hstable : (prefixWord ++ tailWord_4581430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581430).length < 2 ^ (prefixWord ++ tailWord_4581430).sum := by decide
  have hdescent : baseEnd_4581430 < baseStart_4581430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581464 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 2, 1, 3]
def baseStart_4581464 : Nat := 118140960795 + 4581464 * 2 ^ 59
def prefixEnd_4581464 : Nat := 4983230072969 + 3 ^ 40 * 4581464 * 2
def baseEnd_4581464 : Nat := 2352493133270368234730237

theorem tailTrace_4581464 : CollatzResearch.WordTrace tailWord_4581464 prefixEnd_4581464 2352493133270368234730237 := by
  unfold tailWord_4581464
  simp only [CollatzResearch.WordTrace]
  refine ⟨83549859937072927301071723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111399813249430569734762297 83549859937072927301071723)
  ·
    refine ⟨125324789905609390951607585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83549859937072927301071723 125324789905609390951607585)
    ·
      refine ⟨93993592429207043213705689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125324789905609390951607585 93993592429207043213705689)
      ·
        refine ⟨70495194321905282410279267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93993592429207043213705689 70495194321905282410279267)
        ·
          refine ⟨105742791482857923615418901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70495194321905282410279267 105742791482857923615418901)
          ·
            refine ⟨4956693350758965169472761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105742791482857923615418901 4956693350758965169472761)
            ·
              refine ⟨3717520013069223877104571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4956693350758965169472761 3717520013069223877104571)
              ·
                refine ⟨5576280019603835815656857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717520013069223877104571 5576280019603835815656857)
                ·
                  refine ⟨4182210014702876861742643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5576280019603835815656857 4182210014702876861742643)
                  ·
                    refine ⟨6273315022054315292613965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4182210014702876861742643 6273315022054315292613965)
                    ·
                      refine ⟨2352493133270368234730237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6273315022054315292613965 2352493133270368234730237)
                      ·
                        rfl

theorem cell23_4581464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_4581464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581464 prefixEnd_4581464 := by exact prefixLift 4581464
  have htrace : WordTrace (prefixWord ++ tailWord_4581464) baseStart_4581464 baseEnd_4581464 := by
    simpa [prefixWord, tailWord_4581464, baseEnd_4581464] using wordTrace_append hprefix tailTrace_4581464
  have hstable : (prefixWord ++ tailWord_4581464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581464).length < 2 ^ (prefixWord ++ tailWord_4581464).sum := by decide
  have hdescent : baseEnd_4581464 < baseStart_4581464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581474 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4581474 : Nat := 118140960795 + 4581474 * 2 ^ 59
def prefixEnd_4581474 : Nat := 4983230072969 + 3 ^ 40 * 4581474 * 2
def baseEnd_4581474 : Nat := 2352498268076913195605191

theorem tailTrace_4581474 : CollatzResearch.WordTrace tailWord_4581474 prefixEnd_4581474 2352498268076913195605191 := by
  unfold tailWord_4581474
  simp only [CollatzResearch.WordTrace]
  refine ⟨41775021151027406577501869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111400056402739750873338317 41775021151027406577501869)
  ·
    refine ⟨15665632931635277466563201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41775021151027406577501869 15665632931635277466563201)
    ·
      refine ⟨11749224698726458099922401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15665632931635277466563201 11749224698726458099922401)
      ·
        refine ⟨8811918524044843574941801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11749224698726458099922401 8811918524044843574941801)
        ·
          refine ⟨6608938893033632681206351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8811918524044843574941801 6608938893033632681206351)
          ·
            refine ⟨9913408339550449021809527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6608938893033632681206351 9913408339550449021809527)
            ·
              refine ⟨14870112509325673532714291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9913408339550449021809527 14870112509325673532714291)
              ·
                refine ⟨22305168763988510299071437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14870112509325673532714291 22305168763988510299071437)
                ·
                  refine ⟨8364438286495691362151789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22305168763988510299071437 8364438286495691362151789)
                  ·
                    refine ⟨3136664357435884260806921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8364438286495691362151789 3136664357435884260806921)
                    ·
                      refine ⟨2352498268076913195605191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136664357435884260806921 2352498268076913195605191)
                      ·
                        rfl

theorem cell23_4581474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4581474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581474 prefixEnd_4581474 := by exact prefixLift 4581474
  have htrace : WordTrace (prefixWord ++ tailWord_4581474) baseStart_4581474 baseEnd_4581474 := by
    simpa [prefixWord, tailWord_4581474, baseEnd_4581474] using wordTrace_append hprefix tailTrace_4581474
  have hstable : (prefixWord ++ tailWord_4581474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581474).length < 2 ^ (prefixWord ++ tailWord_4581474).sum := by decide
  have hdescent : baseEnd_4581474 < baseStart_4581474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581540 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_4581540 : Nat := 118140960795 + 4581540 * 2 ^ 59
def prefixEnd_4581540 : Nat := 4983230072969 + 3 ^ 40 * 4581540 * 2
def baseEnd_4581540 : Nat := 784177385933369979126629

theorem tailTrace_4581540 : CollatzResearch.WordTrace tailWord_4581540 prefixEnd_4581540 784177385933369979126629 := by
  unfold tailWord_4581540
  simp only [CollatzResearch.WordTrace]
  refine ⟨83551245910935259790955037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111401661214580346387940049 83551245910935259790955037)
  ·
    refine ⟨31331717216600722421608139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83551245910935259790955037 31331717216600722421608139)
    ·
      refine ⟨46997575824901083632412209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31331717216600722421608139 46997575824901083632412209)
      ·
        refine ⟨35248181868675812724309157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46997575824901083632412209 35248181868675812724309157)
        ·
          refine ⟨6609034100376714885807967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35248181868675812724309157 6609034100376714885807967)
          ·
            refine ⟨9913551150565072328711951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6609034100376714885807967 9913551150565072328711951)
            ·
              refine ⟨14870326725847608493067927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9913551150565072328711951 14870326725847608493067927)
              ·
                refine ⟨22305490088771412739601891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14870326725847608493067927 22305490088771412739601891)
                ·
                  refine ⟨33458235133157119109402837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22305490088771412739601891 33458235133157119109402837)
                  ·
                    refine ⟨784177385933369979126629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33458235133157119109402837 784177385933369979126629)
                    ·
                      rfl

theorem cell23_4581540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_4581540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581540 prefixEnd_4581540 := by exact prefixLift 4581540
  have htrace : WordTrace (prefixWord ++ tailWord_4581540) baseStart_4581540 baseEnd_4581540 := by
    simpa [prefixWord, tailWord_4581540, baseEnd_4581540] using wordTrace_append hprefix tailTrace_4581540
  have hstable : (prefixWord ++ tailWord_4581540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581540).length < 2 ^ (prefixWord ++ tailWord_4581540).sum := by decide
  have hdescent : baseEnd_4581540 < baseStart_4581540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581560 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 4, 4, 2]
def baseStart_4581560 : Nat := 118140960795 + 4581560 * 2 ^ 59
def prefixEnd_4581560 : Nat := 4983230072969 + 3 ^ 40 * 4581560 * 2
def baseEnd_4581560 : Nat := 2352542427413199859129795

theorem tailTrace_4581560 : CollatzResearch.WordTrace tailWord_4581560 prefixEnd_4581560 2352542427413199859129795 := by
  unfold tailWord_4581560
  simp only [CollatzResearch.WordTrace]
  refine ⟨83551610640899031498819067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111402147521198708665092089 83551610640899031498819067)
  ·
    refine ⟨125327415961348547248228601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83551610640899031498819067 125327415961348547248228601)
    ·
      refine ⟨93995561971011410436171451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125327415961348547248228601 93995561971011410436171451)
      ·
        refine ⟨140993342956517115654257177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93995561971011410436171451 140993342956517115654257177)
        ·
          refine ⟨105745007217387836740692883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140993342956517115654257177 105745007217387836740692883)
          ·
            refine ⟨158617510826081755111039325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105745007217387836740692883 158617510826081755111039325)
            ·
              refine ⟨59481566559780658166639747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158617510826081755111039325 59481566559780658166639747)
              ·
                refine ⟨89222349839670987249959621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59481566559780658166639747 89222349839670987249959621)
                ·
                  refine ⟨16729190594938310109367429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89222349839670987249959621 16729190594938310109367429)
                  ·
                    refine ⟨3136723236550933145506393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16729190594938310109367429 3136723236550933145506393)
                    ·
                      refine ⟨2352542427413199859129795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136723236550933145506393 2352542427413199859129795)
                      ·
                        rfl

theorem cell23_4581560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_4581560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581560 prefixEnd_4581560 := by exact prefixLift 4581560
  have htrace : WordTrace (prefixWord ++ tailWord_4581560) baseStart_4581560 baseEnd_4581560 := by
    simpa [prefixWord, tailWord_4581560, baseEnd_4581560] using wordTrace_append hprefix tailTrace_4581560
  have hstable : (prefixWord ++ tailWord_4581560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581560).length < 2 ^ (prefixWord ++ tailWord_4581560).sum := by decide
  have hdescent : baseEnd_4581560 < baseStart_4581560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581597 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4581597 : Nat := 118140960795 + 4581597 * 2 ^ 59
def prefixEnd_4581597 : Nat := 4983230072969 + 3 ^ 40 * 4581597 * 2
def baseEnd_4581597 : Nat := 2352561426197416214367125

theorem tailTrace_4581597 : CollatzResearch.WordTrace tailWord_4581597 prefixEnd_4581597 2352561426197416214367125 := by
  unfold tailWord_4581597
  simp only [CollatzResearch.WordTrace]
  refine ⟨167104570782664018316735045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111403047188442678877823363 167104570782664018316735045)
  ·
    refine ⟨31332107021749503434387821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167104570782664018316735045 31332107021749503434387821)
    ·
      refine ⟨11749540133156063787895433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31332107021749503434387821 11749540133156063787895433)
      ·
        refine ⟨8812155099867047840921575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11749540133156063787895433 8812155099867047840921575)
        ·
          refine ⟨13218232649800571761382363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8812155099867047840921575 13218232649800571761382363)
          ·
            refine ⟨19827348974700857642073545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13218232649800571761382363 19827348974700857642073545)
            ·
              refine ⟨14870511731025643231555159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19827348974700857642073545 14870511731025643231555159)
              ·
                refine ⟨22305767596538464847332739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14870511731025643231555159 22305767596538464847332739)
                ·
                  refine ⟨33458651394807697270999109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22305767596538464847332739 33458651394807697270999109)
                  ·
                    refine ⟨6273497136526443238312333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33458651394807697270999109 6273497136526443238312333)
                    ·
                      refine ⟨2352561426197416214367125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6273497136526443238312333 2352561426197416214367125)
                      ·
                        rfl

theorem cell23_4581597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4581597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581597 prefixEnd_4581597 := by exact prefixLift 4581597
  have htrace : WordTrace (prefixWord ++ tailWord_4581597) baseStart_4581597 baseEnd_4581597 := by
    simpa [prefixWord, tailWord_4581597, baseEnd_4581597] using wordTrace_append hprefix tailTrace_4581597
  have hstable : (prefixWord ++ tailWord_4581597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581597).length < 2 ^ (prefixWord ++ tailWord_4581597).sum := by decide
  have hdescent : baseEnd_4581597 < baseStart_4581597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581634 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 6]
def baseStart_4581634 : Nat := 118140960795 + 4581634 * 2 ^ 59
def prefixEnd_4581634 : Nat := 4983230072969 + 3 ^ 40 * 4581634 * 2
def baseEnd_4581634 : Nat := 261397824997959174400495

theorem tailTrace_4581634 : CollatzResearch.WordTrace tailWord_4581634 prefixEnd_4581634 261397824997959174400495 := by
  unfold tailWord_4581634
  simp only [CollatzResearch.WordTrace]
  refine ⟨41776480070882493408957989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111403946855686649090554637 41776480070882493408957989)
  ·
    refine ⟨7833090013290467514179623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41776480070882493408957989 7833090013290467514179623)
    ·
      refine ⟨11749635019935701271269435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7833090013290467514179623 11749635019935701271269435)
      ·
        refine ⟨17624452529903551906904153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11749635019935701271269435 17624452529903551906904153)
        ·
          refine ⟨13218339397427663930178115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17624452529903551906904153 13218339397427663930178115)
          ·
            refine ⟨19827509096141495895267173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13218339397427663930178115 19827509096141495895267173)
            ·
              refine ⟨3717657955526530480362595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19827509096141495895267173 3717657955526530480362595)
              ·
                refine ⟨5576486933289795720543893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717657955526530480362595 5576486933289795720543893)
                ·
                  refine ⟨261397824997959174400495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5576486933289795720543893 261397824997959174400495)
                  ·
                    rfl

theorem cell23_4581634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_4581634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581634 prefixEnd_4581634 := by exact prefixLift 4581634
  have htrace : WordTrace (prefixWord ++ tailWord_4581634) baseStart_4581634 baseEnd_4581634 := by
    simpa [prefixWord, tailWord_4581634, baseEnd_4581634] using wordTrace_append hprefix tailTrace_4581634
  have hstable : (prefixWord ++ tailWord_4581634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581634).length < 2 ^ (prefixWord ++ tailWord_4581634).sum := by decide
  have hdescent : baseEnd_4581634 < baseStart_4581634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581664 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 1, 5]
def baseStart_4581664 : Nat := 118140960795 + 4581664 * 2 ^ 59
def prefixEnd_4581664 : Nat := 4983230072969 + 3 ^ 40 * 4581664 * 2
def baseEnd_4581664 : Nat := 784198609800422484076439

theorem tailTrace_4581664 : CollatzResearch.WordTrace tailWord_4581664 prefixEnd_4581664 784198609800422484076439 := by
  unfold tailWord_4581664
  simp only [CollatzResearch.WordTrace]
  refine ⟨83553507236710644379712023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111404676315614192506282697 83553507236710644379712023)
  ·
    refine ⟨125330260855065966569568035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83553507236710644379712023 125330260855065966569568035)
    ·
      refine ⟨187995391282598949854352053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125330260855065966569568035 187995391282598949854352053)
      ·
        refine ⟨17624567932743651548845505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187995391282598949854352053 17624567932743651548845505)
        ·
          refine ⟨13218425949557738661634129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17624567932743651548845505 13218425949557738661634129)
          ·
            refine ⟨9913819462168303996225597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13218425949557738661634129 9913819462168303996225597)
            ·
              refine ⟨3717682298313113998584599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9913819462168303996225597 3717682298313113998584599)
              ·
                refine ⟨5576523447469670997876899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717682298313113998584599 5576523447469670997876899)
                ·
                  refine ⟨8364785171204506496815349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5576523447469670997876899 8364785171204506496815349)
                  ·
                    refine ⟨784198609800422484076439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8364785171204506496815349 784198609800422484076439)
                    ·
                      rfl

theorem cell23_4581664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 5].length) (baseStart_4581664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581664 prefixEnd_4581664 := by exact prefixLift 4581664
  have htrace : WordTrace (prefixWord ++ tailWord_4581664) baseStart_4581664 baseEnd_4581664 := by
    simpa [prefixWord, tailWord_4581664, baseEnd_4581664] using wordTrace_append hprefix tailTrace_4581664
  have hstable : (prefixWord ++ tailWord_4581664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581664).length < 2 ^ (prefixWord ++ tailWord_4581664).sum := by decide
  have hdescent : baseEnd_4581664 < baseStart_4581664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581690 : List Nat := [3, 1, 1, 1, 4, 2, 3, 8]
def baseStart_4581690 : Nat := 118140960795 + 4581690 * 2 ^ 59
def prefixEnd_4581690 : Nat := 4983230072969 + 3 ^ 40 * 4581690 * 2
def baseEnd_4581690 : Nat := 87133673329566087055711

theorem tailTrace_4581690 : CollatzResearch.WordTrace tailWord_4581690 prefixEnd_4581690 87133673329566087055711 := by
  unfold tailWord_4581690
  simp only [CollatzResearch.WordTrace]
  refine ⟨41776990692831773799967631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111405308514218063466580349 41776990692831773799967631)
  ·
    refine ⟨62665486039247660699951447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41776990692831773799967631 62665486039247660699951447)
    ·
      refine ⟨93998229058871491049927171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62665486039247660699951447 93998229058871491049927171)
      ·
        refine ⟨140997343588307236574890757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93998229058871491049927171 140997343588307236574890757)
        ·
          refine ⟨26437001922807606857792017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140997343588307236574890757 26437001922807606857792017)
          ·
            refine ⟨19827751442105705143344013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26437001922807606857792017 19827751442105705143344013)
            ·
              refine ⟨7435406790789639428754005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19827751442105705143344013 7435406790789639428754005)
              ·
                refine ⟨87133673329566087055711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7435406790789639428754005 87133673329566087055711)
                ·
                  rfl

theorem cell23_4581690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 8].length) (baseStart_4581690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581690 prefixEnd_4581690 := by exact prefixLift 4581690
  have htrace : WordTrace (prefixWord ++ tailWord_4581690) baseStart_4581690 baseEnd_4581690 := by
    simpa [prefixWord, tailWord_4581690, baseEnd_4581690] using wordTrace_append hprefix tailTrace_4581690
  have hstable : (prefixWord ++ tailWord_4581690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581690).length < 2 ^ (prefixWord ++ tailWord_4581690).sum := by decide
  have hdescent : baseEnd_4581690 < baseStart_4581690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581694 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_4581694 : Nat := 118140960795 + 4581694 * 2 ^ 59
def prefixEnd_4581694 : Nat := 4983230072969 + 3 ^ 40 * 4581694 * 2
def baseEnd_4581694 : Nat := 784203744606967444951393

theorem tailTrace_4581694 : CollatzResearch.WordTrace tailWord_4581694 prefixEnd_4581694 784203744606967444951393 := by
  unfold tailWord_4581694
  simp only [CollatzResearch.WordTrace]
  refine ⟨20888513582914075485377017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111405405775541735922010757 20888513582914075485377017)
  ·
    refine ⟨15666385187185556614032763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20888513582914075485377017 15666385187185556614032763)
    ·
      refine ⟨23499577780778334921049145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15666385187185556614032763 23499577780778334921049145)
      ·
        refine ⟨17624683335583751190786859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23499577780778334921049145 17624683335583751190786859)
        ·
          refine ⟨26437025003375626786180289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17624683335583751190786859 26437025003375626786180289)
          ·
            refine ⟨19827768752531720089635217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26437025003375626786180289 19827768752531720089635217)
            ·
              refine ⟨14870826564398790067226413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19827768752531720089635217 14870826564398790067226413)
              ·
                refine ⟨5576559961649546275209905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14870826564398790067226413 5576559961649546275209905)
                ·
                  refine ⟨4182419971237159706407429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5576559961649546275209905 4182419971237159706407429)
                  ·
                    refine ⟨784203744606967444951393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182419971237159706407429 784203744606967444951393)
                    ·
                      rfl

theorem cell23_4581694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_4581694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581694 prefixEnd_4581694 := by exact prefixLift 4581694
  have htrace : WordTrace (prefixWord ++ tailWord_4581694) baseStart_4581694 baseEnd_4581694 := by
    simpa [prefixWord, tailWord_4581694, baseEnd_4581694] using wordTrace_append hprefix tailTrace_4581694
  have hstable : (prefixWord ++ tailWord_4581694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581694).length < 2 ^ (prefixWord ++ tailWord_4581694).sum := by decide
  have hdescent : baseEnd_4581694 < baseStart_4581694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581761 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_4581761 : Nat := 118140960795 + 4581761 * 2 ^ 59
def prefixEnd_4581761 : Nat := 4983230072969 + 3 ^ 40 * 4581761 * 2
def baseEnd_4581761 : Nat := 2352645637024753572716371

theorem tailTrace_4581761 : CollatzResearch.WordTrace tailWord_4581761 prefixEnd_4581761 2352645637024753572716371 := by
  unfold tailWord_4581761
  simp only [CollatzResearch.WordTrace]
  refine ⟨167110552354069874325705137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111407034902713249550470091 167110552354069874325705137)
  ·
    refine ⟨125332914265552405744278853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167110552354069874325705137 125332914265552405744278853)
    ·
      refine ⟨23499921424791076077052285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125332914265552405744278853 23499921424791076077052285)
      ·
        refine ⟨8812470534296653528894607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23499921424791076077052285 8812470534296653528894607)
        ·
          refine ⟨13218705801444980293341911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8812470534296653528894607 13218705801444980293341911)
          ·
            refine ⟨19828058702167470440012867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13218705801444980293341911 19828058702167470440012867)
            ·
              refine ⟨29742088053251205660019301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19828058702167470440012867 29742088053251205660019301)
              ·
                refine ⟨5576641509984601061253619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29742088053251205660019301 5576641509984601061253619)
                ·
                  refine ⟨8364962264976901591880429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5576641509984601061253619 8364962264976901591880429)
                  ·
                    refine ⟨3136860849366338096955161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8364962264976901591880429 3136860849366338096955161)
                    ·
                      refine ⟨2352645637024753572716371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136860849366338096955161 2352645637024753572716371)
                      ·
                        rfl

theorem cell23_4581761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_4581761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581761 prefixEnd_4581761 := by exact prefixLift 4581761
  have htrace : WordTrace (prefixWord ++ tailWord_4581761) baseStart_4581761 baseEnd_4581761 := by
    simpa [prefixWord, tailWord_4581761, baseEnd_4581761] using wordTrace_append hprefix tailTrace_4581761
  have hstable : (prefixWord ++ tailWord_4581761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581761).length < 2 ^ (prefixWord ++ tailWord_4581761).sum := by decide
  have hdescent : baseEnd_4581761 < baseStart_4581761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581791 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 2, 2, 2]
def baseStart_4581791 : Nat := 118140960795 + 4581791 * 2 ^ 59
def prefixEnd_4581791 : Nat := 4983230072969 + 3 ^ 40 * 4581791 * 2
def baseEnd_4581791 : Nat := 2352661041444388455341233

theorem tailTrace_4581791 : CollatzResearch.WordTrace tailWord_4581791 prefixEnd_4581791 2352661041444388455341233 := by
  unfold tailWord_4581791
  simp only [CollatzResearch.WordTrace]
  refine ⟨167111646543961189449297227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111407764362640792966198151 167111646543961189449297227)
  ·
    refine ⟨250667469815941784173945841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167111646543961189449297227 250667469815941784173945841)
    ·
      refine ⟨188000602361956338130459381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250667469815941784173945841 188000602361956338130459381)
      ·
        refine ⟨17625056471433406699730567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188000602361956338130459381 17625056471433406699730567)
        ·
          refine ⟨26437584707150110049595851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17625056471433406699730567 26437584707150110049595851)
          ·
            refine ⟨39656377060725165074393777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26437584707150110049595851 39656377060725165074393777)
            ·
              refine ⟨29742282795543873805795333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39656377060725165074393777 29742282795543873805795333)
              ·
                refine ⟨5576678024164476338586625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29742282795543873805795333 5576678024164476338586625)
                ·
                  refine ⟨4182508518123357253939969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5576678024164476338586625 4182508518123357253939969)
                  ·
                    refine ⟨3136881388592517940454977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4182508518123357253939969 3136881388592517940454977)
                    ·
                      refine ⟨2352661041444388455341233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136881388592517940454977 2352661041444388455341233)
                      ·
                        rfl

theorem cell23_4581791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_4581791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581791 prefixEnd_4581791 := by exact prefixLift 4581791
  have htrace : WordTrace (prefixWord ++ tailWord_4581791) baseStart_4581791 baseEnd_4581791 := by
    simpa [prefixWord, tailWord_4581791, baseEnd_4581791] using wordTrace_append hprefix tailTrace_4581791
  have hstable : (prefixWord ++ tailWord_4581791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581791).length < 2 ^ (prefixWord ++ tailWord_4581791).sum := by decide
  have hdescent : baseEnd_4581791 < baseStart_4581791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581812 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_4581812 : Nat := 118140960795 + 4581812 * 2 ^ 59
def prefixEnd_4581812 : Nat := 4983230072969 + 3 ^ 40 * 4581812 * 2
def baseEnd_4581812 : Nat := 2352671824538132873178637

theorem tailTrace_4581812 : CollatzResearch.WordTrace tailWord_4581812 prefixEnd_4581812 2352671824538132873178637 := by
  unfold tailWord_4581812
  simp only [CollatzResearch.WordTrace]
  refine ⟨83556206238442555017905845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111408274984590073357207793 83556206238442555017905845)
  ·
    refine ⟨7833394334853989532928673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83556206238442555017905845 7833394334853989532928673)
    ·
      refine ⟨5875045751140492149696505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7833394334853989532928673 5875045751140492149696505)
      ·
        refine ⟨4406284313355369112272379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5875045751140492149696505 4406284313355369112272379)
        ·
          refine ⟨6609426470033053668408569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406284313355369112272379 6609426470033053668408569)
          ·
            refine ⟨4957069852524790251306427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6609426470033053668408569 4957069852524790251306427)
            ·
              refine ⟨7435604778787185376959641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4957069852524790251306427 7435604778787185376959641)
              ·
                refine ⟨5576703584090389032719731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7435604778787185376959641 5576703584090389032719731)
                ·
                  refine ⟨8365055376135583549079597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5576703584090389032719731 8365055376135583549079597)
                  ·
                    refine ⟨3136895766050843830904849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8365055376135583549079597 3136895766050843830904849)
                    ·
                      refine ⟨2352671824538132873178637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136895766050843830904849 2352671824538132873178637)
                      ·
                        rfl

theorem cell23_4581812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_4581812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581812 prefixEnd_4581812 := by exact prefixLift 4581812
  have htrace : WordTrace (prefixWord ++ tailWord_4581812) baseStart_4581812 baseEnd_4581812 := by
    simpa [prefixWord, tailWord_4581812, baseEnd_4581812] using wordTrace_append hprefix tailTrace_4581812
  have hstable : (prefixWord ++ tailWord_4581812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581812).length < 2 ^ (prefixWord ++ tailWord_4581812).sum := by decide
  have hdescent : baseEnd_4581812 < baseStart_4581812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581825 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4581825 : Nat := 118140960795 + 4581825 * 2 ^ 59
def prefixEnd_4581825 : Nat := 4983230072969 + 3 ^ 40 * 4581825 * 2
def baseEnd_4581825 : Nat := 2352678499786641322316077

theorem tailTrace_4581825 : CollatzResearch.WordTrace tailWord_4581825 prefixEnd_4581825 2352678499786641322316077 := by
  unfold tailWord_4581825
  simp only [CollatzResearch.WordTrace]
  refine ⟨167112886625838013256034929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111408591083892008837356619 167112886625838013256034929)
  ·
    refine ⟨125334664969378509942026197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167112886625838013256034929 125334664969378509942026197)
    ·
      refine ⟨2937531210219808826766239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 125334664969378509942026197 2937531210219808826766239)
      ·
        refine ⟨4406296815329713240149359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937531210219808826766239 4406296815329713240149359)
        ·
          refine ⟨6609445222994569860224039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406296815329713240149359 6609445222994569860224039)
          ·
            refine ⟨9914167834491854790336059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6609445222994569860224039 9914167834491854790336059)
            ·
              refine ⟨14871251751737782185504089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9914167834491854790336059 14871251751737782185504089)
              ·
                refine ⟨11153438813803336639128067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14871251751737782185504089 11153438813803336639128067)
                ·
                  refine ⟨16730158220705004958692101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11153438813803336639128067 16730158220705004958692101)
                  ·
                    refine ⟨3136904666382188429754769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16730158220705004958692101 3136904666382188429754769)
                    ·
                      refine ⟨2352678499786641322316077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136904666382188429754769 2352678499786641322316077)
                      ·
                        rfl

theorem cell23_4581825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4581825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581825 prefixEnd_4581825 := by exact prefixLift 4581825
  have htrace : WordTrace (prefixWord ++ tailWord_4581825) baseStart_4581825 baseEnd_4581825 := by
    simpa [prefixWord, tailWord_4581825, baseEnd_4581825] using wordTrace_append hprefix tailTrace_4581825
  have hstable : (prefixWord ++ tailWord_4581825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581825).length < 2 ^ (prefixWord ++ tailWord_4581825).sum := by decide
  have hdescent : baseEnd_4581825 < baseStart_4581825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581844 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_4581844 : Nat := 118140960795 + 4581844 * 2 ^ 59
def prefixEnd_4581844 : Nat := 4983230072969 + 3 ^ 40 * 4581844 * 2
def baseEnd_4581844 : Nat := 784229418639692249326163

theorem tailTrace_4581844 : CollatzResearch.WordTrace tailWord_4581844 prefixEnd_4581844 784229418639692249326163 := by
  unfold tailWord_4581844
  simp only [CollatzResearch.WordTrace]
  refine ⟨83556789806384589750488293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111409053075179453000651057 83556789806384589750488293)
  ·
    refine ⟨15666898088697110578216555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83556789806384589750488293 15666898088697110578216555)
    ·
      refine ⟨23500347133045665867324833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15666898088697110578216555 23500347133045665867324833)
      ·
        refine ⟨17625260349784249400493625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23500347133045665867324833 17625260349784249400493625)
        ·
          refine ⟨13218945262338187050370219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17625260349784249400493625 13218945262338187050370219)
          ·
            refine ⟨19828417893507280575555329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13218945262338187050370219 19828417893507280575555329)
            ·
              refine ⟨14871313420130460431666497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19828417893507280575555329 14871313420130460431666497)
              ·
                refine ⟨11153485065097845323749873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14871313420130460431666497 11153485065097845323749873)
                ·
                  refine ⟨8365113798823383992812405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11153485065097845323749873 8365113798823383992812405)
                  ·
                    refine ⟨784229418639692249326163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8365113798823383992812405 784229418639692249326163)
                    ·
                      rfl

theorem cell23_4581844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_4581844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581844 prefixEnd_4581844 := by exact prefixLift 4581844
  have htrace : WordTrace (prefixWord ++ tailWord_4581844) baseStart_4581844 baseEnd_4581844 := by
    simpa [prefixWord, tailWord_4581844, baseEnd_4581844] using wordTrace_append hprefix tailTrace_4581844
  have hstable : (prefixWord ++ tailWord_4581844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581844).length < 2 ^ (prefixWord ++ tailWord_4581844).sum := by decide
  have hdescent : baseEnd_4581844 < baseStart_4581844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581858 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4581858 : Nat := 118140960795 + 4581858 * 2 ^ 59
def prefixEnd_4581858 : Nat := 4983230072969 + 3 ^ 40 * 4581858 * 2
def baseEnd_4581858 : Nat := 2352695444648239693203425

theorem tailTrace_4581858 : CollatzResearch.WordTrace tailWord_4581858 prefixEnd_4581858 2352695444648239693203425 := by
  unfold tailWord_4581858
  simp only [CollatzResearch.WordTrace]
  refine ⟨41778522558679614972996557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111409393489812306594657485 41778522558679614972996557)
  ·
    refine ⟨15666945959504855614873709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41778522558679614972996557 15666945959504855614873709)
    ·
      refine ⟨5875104734814320855577641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15666945959504855614873709 5875104734814320855577641)
      ·
        refine ⟨4406328551110740641683231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5875104734814320855577641 4406328551110740641683231)
        ·
          refine ⟨6609492826666110962524847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406328551110740641683231 6609492826666110962524847)
          ·
            refine ⟨9914239239999166443787271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6609492826666110962524847 9914239239999166443787271)
            ·
              refine ⟨14871358859998749665680907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9914239239999166443787271 14871358859998749665680907)
              ·
                refine ⟨22307038289998124498521361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14871358859998749665680907 22307038289998124498521361)
                ·
                  refine ⟨16730278717498593373891021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22307038289998124498521361 16730278717498593373891021)
                  ·
                    refine ⟨6273854519061972515209133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16730278717498593373891021 6273854519061972515209133)
                    ·
                      refine ⟨2352695444648239693203425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6273854519061972515209133 2352695444648239693203425)
                      ·
                        rfl

theorem cell23_4581858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4581858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581858 prefixEnd_4581858 := by exact prefixLift 4581858
  have htrace : WordTrace (prefixWord ++ tailWord_4581858) baseStart_4581858 baseEnd_4581858 := by
    simpa [prefixWord, tailWord_4581858, baseEnd_4581858] using wordTrace_append hprefix tailTrace_4581858
  have hstable : (prefixWord ++ tailWord_4581858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581858).length < 2 ^ (prefixWord ++ tailWord_4581858).sum := by decide
  have hdescent : baseEnd_4581858 < baseStart_4581858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581864 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_4581864 : Nat := 118140960795 + 4581864 * 2 ^ 59
def prefixEnd_4581864 : Nat := 4983230072969 + 3 ^ 40 * 4581864 * 2
def baseEnd_4581864 : Nat := 2352698525532166669728397

theorem tailTrace_4581864 : CollatzResearch.WordTrace tailWord_4581864 prefixEnd_4581864 2352698525532166669728397 := by
  unfold tailWord_4581864
  simp only [CollatzResearch.WordTrace]
  refine ⟨83557154536348361458352323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111409539381797815277803097 83557154536348361458352323)
  ·
    refine ⟨125335731804522542187528485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83557154536348361458352323 125335731804522542187528485)
    ·
      refine ⟨23500449713347976660161591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125335731804522542187528485 23500449713347976660161591)
      ·
        refine ⟨35250674570021964990242387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23500449713347976660161591 35250674570021964990242387)
        ·
          refine ⟨52876011855032947485363581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35250674570021964990242387 52876011855032947485363581)
          ·
            refine ⟨19828504445637355307011343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52876011855032947485363581 19828504445637355307011343)
            ·
              refine ⟨29742756668456032960517015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19828504445637355307011343 29742756668456032960517015)
              ·
                refine ⟨44614135002684049440775523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29742756668456032960517015 44614135002684049440775523)
                ·
                  refine ⟨66921202504026074161163285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44614135002684049440775523 66921202504026074161163285)
                  ·
                    refine ⟨3136931367376222226304529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66921202504026074161163285 3136931367376222226304529)
                    ·
                      refine ⟨2352698525532166669728397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136931367376222226304529 2352698525532166669728397)
                      ·
                        rfl

theorem cell23_4581864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_4581864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581864 prefixEnd_4581864 := by exact prefixLift 4581864
  have htrace : WordTrace (prefixWord ++ tailWord_4581864) baseStart_4581864 baseEnd_4581864 := by
    simpa [prefixWord, tailWord_4581864, baseEnd_4581864] using wordTrace_append hprefix tailTrace_4581864
  have hstable : (prefixWord ++ tailWord_4581864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581864).length < 2 ^ (prefixWord ++ tailWord_4581864).sum := by decide
  have hdescent : baseEnd_4581864 < baseStart_4581864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581867 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 3]
def baseStart_4581867 : Nat := 118140960795 + 4581867 * 2 ^ 59
def prefixEnd_4581867 : Nat := 4983230072969 + 3 ^ 40 * 4581867 * 2
def baseEnd_4581867 : Nat := 2352700065974130157990883

theorem tailTrace_4581867 : CollatzResearch.WordTrace tailWord_4581867 prefixEnd_4581867 2352700065974130157990883 := by
  unfold tailWord_4581867
  simp only [CollatzResearch.WordTrace]
  refine ⟨167114418491685854429063855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111409612327790569619375903 167114418491685854429063855)
  ·
    refine ⟨250671627737528781643595783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167114418491685854429063855 250671627737528781643595783)
    ·
      refine ⟨376007441606293172465393675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250671627737528781643595783 376007441606293172465393675)
      ·
        refine ⟨564011162409439758698090513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376007441606293172465393675 564011162409439758698090513)
        ·
          refine ⟨423008371807079819023567885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564011162409439758698090513 423008371807079819023567885)
          ·
            refine ⟨158628139427654932133837957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 423008371807079819023567885 158628139427654932133837957)
            ·
              refine ⟨29742776142685299775094617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158628139427654932133837957 29742776142685299775094617)
              ·
                refine ⟨22307082107013974831320963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29742776142685299775094617 22307082107013974831320963)
                ·
                  refine ⟨33460623160520962246981445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22307082107013974831320963 33460623160520962246981445)
                  ·
                    refine ⟨6273866842597680421309021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33460623160520962246981445 6273866842597680421309021)
                    ·
                      refine ⟨2352700065974130157990883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6273866842597680421309021 2352700065974130157990883)
                      ·
                        rfl

theorem cell23_4581867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 3].length) (baseStart_4581867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581867 prefixEnd_4581867 := by exact prefixLift 4581867
  have htrace : WordTrace (prefixWord ++ tailWord_4581867) baseStart_4581867 baseEnd_4581867 := by
    simpa [prefixWord, tailWord_4581867, baseEnd_4581867] using wordTrace_append hprefix tailTrace_4581867
  have hstable : (prefixWord ++ tailWord_4581867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581867).length < 2 ^ (prefixWord ++ tailWord_4581867).sum := by decide
  have hdescent : baseEnd_4581867 < baseStart_4581867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581891 : List Nat := [1, 1, 1, 3, 2, 1, 6, 3, 1, 4]
def baseStart_4581891 : Nat := 118140960795 + 4581891 * 2 ^ 59
def prefixEnd_4581891 : Nat := 4983230072969 + 3 ^ 40 * 4581891 * 2
def baseEnd_4581891 : Nat := 784237463169946021363591

theorem tailTrace_4581891 : CollatzResearch.WordTrace tailWord_4581891 prefixEnd_4581891 784237463169946021363591 := by
  unfold tailWord_4581891
  simp only [CollatzResearch.WordTrace]
  refine ⟨167115293843598906527937527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111410195895732604351958351 167115293843598906527937527)
  ·
    refine ⟨250672940765398359791906291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167115293843598906527937527 250672940765398359791906291)
    ·
      refine ⟨376009411148097539687859437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250672940765398359791906291 376009411148097539687859437)
      ·
        refine ⟨141003529180536577382947289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376009411148097539687859437 141003529180536577382947289)
        ·
          refine ⟨105752646885402433037210467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141003529180536577382947289 105752646885402433037210467)
          ·
            refine ⟨158628970328103649555815701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105752646885402433037210467 158628970328103649555815701)
            ·
              refine ⟨7435732984129858572928861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158628970328103649555815701 7435732984129858572928861)
              ·
                refine ⟨2788399869048696964848323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7435732984129858572928861 2788399869048696964848323)
                ·
                  refine ⟨4182599803573045447272485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788399869048696964848323 4182599803573045447272485)
                  ·
                    refine ⟨784237463169946021363591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182599803573045447272485 784237463169946021363591)
                    ·
                      rfl

theorem cell23_4581891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 1, 4].length) (baseStart_4581891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581891 prefixEnd_4581891 := by exact prefixLift 4581891
  have htrace : WordTrace (prefixWord ++ tailWord_4581891) baseStart_4581891 baseEnd_4581891 := by
    simpa [prefixWord, tailWord_4581891, baseEnd_4581891] using wordTrace_append hprefix tailTrace_4581891
  have hstable : (prefixWord ++ tailWord_4581891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581891).length < 2 ^ (prefixWord ++ tailWord_4581891).sum := by decide
  have hdescent : baseEnd_4581891 < baseStart_4581891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581908 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4581908 : Nat := 118140960795 + 4581908 * 2 ^ 59
def prefixEnd_4581908 : Nat := 4983230072969 + 3 ^ 40 * 4581908 * 2
def baseEnd_4581908 : Nat := 784240372893654832526065

theorem tailTrace_4581908 : CollatzResearch.WordTrace tailWord_4581908 prefixEnd_4581908 784240372893654832526065 := by
  unfold tailWord_4581908
  simp only [CollatzResearch.WordTrace]
  refine ⟨83557956942268659215653189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111410609256358212287537585 83557956942268659215653189)
  ·
    refine ⟨15667116926675373602934973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83557956942268659215653189 15667116926675373602934973)
    ·
      refine ⟨5875168847503265101100615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15667116926675373602934973 5875168847503265101100615)
      ·
        refine ⟨8812753271254897651650923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5875168847503265101100615 8812753271254897651650923)
        ·
          refine ⟨13219129906882346477476385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8812753271254897651650923 13219129906882346477476385)
          ·
            refine ⟨9914347430161759858107289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13219129906882346477476385 9914347430161759858107289)
            ·
              refine ⟨7435760572621319893580467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9914347430161759858107289 7435760572621319893580467)
              ·
                refine ⟨11153640858931979840370701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7435760572621319893580467 11153640858931979840370701)
                ·
                  refine ⟨4182615322099492440139013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11153640858931979840370701 4182615322099492440139013)
                  ·
                    refine ⟨784240372893654832526065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182615322099492440139013 784240372893654832526065)
                    ·
                      rfl

theorem cell23_4581908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4581908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581908 prefixEnd_4581908 := by exact prefixLift 4581908
  have htrace : WordTrace (prefixWord ++ tailWord_4581908) baseStart_4581908 baseEnd_4581908 := by
    simpa [prefixWord, tailWord_4581908, baseEnd_4581908] using wordTrace_append hprefix tailTrace_4581908
  have hstable : (prefixWord ++ tailWord_4581908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581908).length < 2 ^ (prefixWord ++ tailWord_4581908).sum := by decide
  have hdescent : baseEnd_4581908 < baseStart_4581908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581941 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_4581941 : Nat := 118140960795 + 4581941 * 2 ^ 59
def prefixEnd_4581941 : Nat := 4983230072969 + 3 ^ 40 * 4581941 * 2
def baseEnd_4581941 : Nat := 2352738063542562868465543

theorem tailTrace_4581941 : CollatzResearch.WordTrace tailWord_4581941 prefixEnd_4581941 2352738063542562868465543 := by
  unfold tailWord_4581941
  simp only [CollatzResearch.WordTrace]
  refine ⟨167117117493417765067257677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111411411662278510044838451 167117117493417765067257677)
  ·
    refine ⟨62668919060031661900221629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167117117493417765067257677 62668919060031661900221629)
    ·
      refine ⟨23500844647511873212583111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62668919060031661900221629 23500844647511873212583111)
      ·
        refine ⟨35251266971267809818874667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23500844647511873212583111 35251266971267809818874667)
        ·
          refine ⟨52876900456901714728312001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35251266971267809818874667 52876900456901714728312001)
          ·
            refine ⟨39657675342676286046234001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52876900456901714728312001 39657675342676286046234001)
            ·
              refine ⟨29743256507007214534675501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39657675342676286046234001 29743256507007214534675501)
              ·
                refine ⟨11153721190127705450503313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29743256507007214534675501 11153721190127705450503313)
                ·
                  refine ⟨8365290892595779087877485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11153721190127705450503313 8365290892595779087877485)
                  ·
                    refine ⟨3136984084723417157954057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8365290892595779087877485 3136984084723417157954057)
                    ·
                      refine ⟨2352738063542562868465543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3136984084723417157954057 2352738063542562868465543)
                      ·
                        rfl

theorem cell23_4581941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_4581941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581941 prefixEnd_4581941 := by exact prefixLift 4581941
  have htrace : WordTrace (prefixWord ++ tailWord_4581941) baseStart_4581941 baseEnd_4581941 := by
    simpa [prefixWord, tailWord_4581941, baseEnd_4581941] using wordTrace_append hprefix tailTrace_4581941
  have hstable : (prefixWord ++ tailWord_4581941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581941).length < 2 ^ (prefixWord ++ tailWord_4581941).sum := by decide
  have hdescent : baseEnd_4581941 < baseStart_4581941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581964 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_4581964 : Nat := 118140960795 + 4581964 * 2 ^ 59
def prefixEnd_4581964 : Nat := 4983230072969 + 3 ^ 40 * 4581964 * 2
def baseEnd_4581964 : Nat := 784249957865872092825979

theorem tailTrace_4581964 : CollatzResearch.WordTrace tailWord_4581964 prefixEnd_4581964 784249957865872092825979 := by
  unfold tailWord_4581964
  simp only [CollatzResearch.WordTrace]
  refine ⟨83558978186167219997672473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111411970914889626663563297 83558978186167219997672473)
  ·
    refine ⟨62669233639625414998254355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83558978186167219997672473 62669233639625414998254355)
    ·
      refine ⟨94003850459438122497381533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62669233639625414998254355 94003850459438122497381533)
      ·
        refine ⟨35251443922289295936518075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94003850459438122497381533 35251443922289295936518075)
        ·
          refine ⟨52877165883433943904777113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35251443922289295936518075 52877165883433943904777113)
          ·
            refine ⟨39657874412575457928582835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52877165883433943904777113 39657874412575457928582835)
            ·
              refine ⟨59486811618863186892874253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39657874412575457928582835 59486811618863186892874253)
              ·
                refine ⟨22307554357073695084827845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59486811618863186892874253 22307554357073695084827845)
                ·
                  refine ⟨4182666441951317828405221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22307554357073695084827845 4182666441951317828405221)
                  ·
                    refine ⟨784249957865872092825979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182666441951317828405221 784249957865872092825979)
                    ·
                      rfl

theorem cell23_4581964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_4581964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581964 prefixEnd_4581964 := by exact prefixLift 4581964
  have htrace : WordTrace (prefixWord ++ tailWord_4581964) baseStart_4581964 baseEnd_4581964 := by
    simpa [prefixWord, tailWord_4581964, baseEnd_4581964] using wordTrace_append hprefix tailTrace_4581964
  have hstable : (prefixWord ++ tailWord_4581964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581964).length < 2 ^ (prefixWord ++ tailWord_4581964).sum := by decide
  have hdescent : baseEnd_4581964 < baseStart_4581964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581965 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_4581965 : Nat := 118140960795 + 4581965 * 2 ^ 59
def prefixEnd_4581965 : Nat := 4983230072969 + 3 ^ 40 * 4581965 * 2
def baseEnd_4581965 : Nat := 2352750387078270774565433

theorem tailTrace_4581965 : CollatzResearch.WordTrace tailWord_4581965 prefixEnd_4581965 2352750387078270774565433 := by
  unfold tailWord_4581965
  simp only [CollatzResearch.WordTrace]
  refine ⟨167117992845330817166131349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111411995230220544777420899 167117992845330817166131349)
  ·
    refine ⟨7833655914624882054662407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 167117992845330817166131349 7833655914624882054662407)
    ·
      refine ⟨11750483871937323081993611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7833655914624882054662407 11750483871937323081993611)
      ·
        refine ⟨17625725807905984622990417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11750483871937323081993611 17625725807905984622990417)
        ·
          refine ⟨13219294355929488467242813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17625725807905984622990417 13219294355929488467242813)
          ·
            refine ⟨4957235383473558175216055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13219294355929488467242813 4957235383473558175216055)
            ·
              refine ⟨7435853075210337262824083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4957235383473558175216055 7435853075210337262824083)
              ·
                refine ⟨11153779612815505894236125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7435853075210337262824083 11153779612815505894236125)
                ·
                  refine ⟨4182667354805814710338547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11153779612815505894236125 4182667354805814710338547)
                  ·
                    refine ⟨6274001032208722065507821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4182667354805814710338547 6274001032208722065507821)
                    ·
                      refine ⟨2352750387078270774565433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6274001032208722065507821 2352750387078270774565433)
                      ·
                        rfl

theorem cell23_4581965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_4581965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581965 prefixEnd_4581965 := by exact prefixLift 4581965
  have htrace : WordTrace (prefixWord ++ tailWord_4581965) baseStart_4581965 baseEnd_4581965 := by
    simpa [prefixWord, tailWord_4581965, baseEnd_4581965] using wordTrace_append hprefix tailTrace_4581965
  have hstable : (prefixWord ++ tailWord_4581965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581965).length < 2 ^ (prefixWord ++ tailWord_4581965).sum := by decide
  have hdescent : baseEnd_4581965 < baseStart_4581965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4581967 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_4581967 : Nat := 118140960795 + 4581967 * 2 ^ 59
def prefixEnd_4581967 : Nat := 4983230072969 + 3 ^ 40 * 4581967 * 2
def baseEnd_4581967 : Nat := 2352751414039579766740423

theorem tailTrace_4581967 : CollatzResearch.WordTrace tailWord_4581967 prefixEnd_4581967 2352751414039579766740423 := by
  unfold tailWord_4581967
  simp only [CollatzResearch.WordTrace]
  refine ⟨167118065791323571507704155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111412043860882381005136103 167118065791323571507704155)
  ·
    refine ⟨250677098686985357261556233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167118065791323571507704155 250677098686985357261556233)
    ·
      refine ⟨188007824015239017946167175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250677098686985357261556233 188007824015239017946167175)
      ·
        refine ⟨282011736022858526919250763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188007824015239017946167175 282011736022858526919250763)
        ·
          refine ⟨423017604034287790378876145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282011736022858526919250763 423017604034287790378876145)
          ·
            refine ⟨317263203025715842784157109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423017604034287790378876145 317263203025715842784157109)
            ·
              refine ⟨29743425283660860261014729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 317263203025715842784157109 29743425283660860261014729)
              ·
                refine ⟨22307568962745645195761047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29743425283660860261014729 22307568962745645195761047)
                ·
                  refine ⟨33461353444118467793641571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22307568962745645195761047 33461353444118467793641571)
                  ·
                    refine ⟨50192030166177701690462357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33461353444118467793641571 50192030166177701690462357)
                    ·
                      refine ⟨2352751414039579766740423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50192030166177701690462357 2352751414039579766740423)
                      ·
                        rfl

theorem cell23_4581967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_4581967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4581967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4581967 prefixEnd_4581967 := by exact prefixLift 4581967
  have htrace : WordTrace (prefixWord ++ tailWord_4581967) baseStart_4581967 baseEnd_4581967 := by
    simpa [prefixWord, tailWord_4581967, baseEnd_4581967] using wordTrace_append hprefix tailTrace_4581967
  have hstable : (prefixWord ++ tailWord_4581967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4581967).length < 2 ^ (prefixWord ++ tailWord_4581967).sum := by decide
  have hdescent : baseEnd_4581967 < baseStart_4581967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4581967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582005 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4582005 : Nat := 118140960795 + 4582005 * 2 ^ 59
def prefixEnd_4582005 : Nat := 4983230072969 + 3 ^ 40 * 4582005 * 2
def baseEnd_4582005 : Nat := 2352770926304450618065249

theorem tailTrace_4582005 : CollatzResearch.WordTrace tailWord_4582005 prefixEnd_4582005 2352770926304450618065249 := by
  unfold tailWord_4582005
  simp only [CollatzResearch.WordTrace]
  refine ⟨167119451765185903997587469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111412967843457269331724979 167119451765185903997587469)
  ·
    refine ⟨62669794411944713999095301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167119451765185903997587469 62669794411944713999095301)
    ·
      refine ⟨11750586452239633874830369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62669794411944713999095301 11750586452239633874830369)
      ·
        refine ⟨8812939839179725406122777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11750586452239633874830369 8812939839179725406122777)
        ·
          refine ⟨6609704879384794054592083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8812939839179725406122777 6609704879384794054592083)
          ·
            refine ⟨9914557319077191081888125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6609704879384794054592083 9914557319077191081888125)
            ·
              refine ⟨3717958994653946655708047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9914557319077191081888125 3717958994653946655708047)
              ·
                refine ⟨5576938491980919983562071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717958994653946655708047 5576938491980919983562071)
                ·
                  refine ⟨8365407737971379975343107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5576938491980919983562071 8365407737971379975343107)
                  ·
                    refine ⟨12548111606957069963014661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8365407737971379975343107 12548111606957069963014661)
                    ·
                      refine ⟨2352770926304450618065249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12548111606957069963014661 2352770926304450618065249)
                      ·
                        rfl

theorem cell23_4582005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4582005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582005 prefixEnd_4582005 := by exact prefixLift 4582005
  have htrace : WordTrace (prefixWord ++ tailWord_4582005) baseStart_4582005 baseEnd_4582005 := by
    simpa [prefixWord, tailWord_4582005, baseEnd_4582005] using wordTrace_append hprefix tailTrace_4582005
  have hstable : (prefixWord ++ tailWord_4582005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582005).length < 2 ^ (prefixWord ++ tailWord_4582005).sum := by decide
  have hdescent : baseEnd_4582005 < baseStart_4582005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582074 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_4582074 : Nat := 118140960795 + 4582074 * 2 ^ 59
def prefixEnd_4582074 : Nat := 4983230072969 + 3 ^ 40 * 4582074 * 2
def baseEnd_4582074 : Nat := 2352806356469610848102431

theorem tailTrace_4582074 : CollatzResearch.WordTrace tailWord_4582074 prefixEnd_4582074 2352806356469610848102431 := by
  unfold tailWord_4582074
  simp only [CollatzResearch.WordTrace]
  refine ⟨41780492100483982195462319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111414645601290619187899517 41780492100483982195462319)
  ·
    refine ⟨62670738150725973293193479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41780492100483982195462319 62670738150725973293193479)
    ·
      refine ⟨94006107226088959939790219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62670738150725973293193479 94006107226088959939790219)
      ·
        refine ⟨141009160839133439909685329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94006107226088959939790219 141009160839133439909685329)
        ·
          refine ⟨105756870629350079932263997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141009160839133439909685329 105756870629350079932263997)
          ·
            refine ⟨39658826486006279974598999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105756870629350079932263997 39658826486006279974598999)
            ·
              refine ⟨59488239729009419961898499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39658826486006279974598999 59488239729009419961898499)
              ·
                refine ⟨89232359593514129942847749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59488239729009419961898499 89232359593514129942847749)
                ·
                  refine ⟨16731067423783899364283953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89232359593514129942847749 16731067423783899364283953)
                  ·
                    refine ⟨12548300567837924523212965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16731067423783899364283953 12548300567837924523212965)
                    ·
                      refine ⟨2352806356469610848102431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12548300567837924523212965 2352806356469610848102431)
                      ·
                        rfl

theorem cell23_4582074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_4582074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582074 prefixEnd_4582074 := by exact prefixLift 4582074
  have htrace : WordTrace (prefixWord ++ tailWord_4582074) baseStart_4582074 baseEnd_4582074 := by
    simpa [prefixWord, tailWord_4582074, baseEnd_4582074] using wordTrace_append hprefix tailTrace_4582074
  have hstable : (prefixWord ++ tailWord_4582074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582074).length < 2 ^ (prefixWord ++ tailWord_4582074).sum := by decide
  have hdescent : baseEnd_4582074 < baseStart_4582074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582124 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_4582124 : Nat := 118140960795 + 4582124 * 2 ^ 59
def prefixEnd_4582124 : Nat := 4983230072969 + 3 ^ 40 * 4582124 * 2
def baseEnd_4582124 : Nat := 2352832030502335652477201

theorem tailTrace_4582124 : CollatzResearch.WordTrace tailWord_4582124 prefixEnd_4582124 2352832030502335652477201 := by
  unfold tailWord_4582124
  simp only [CollatzResearch.WordTrace]
  refine ⟨83561896025877393660584713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111415861367836524880779617 83561896025877393660584713)
  ·
    refine ⟨62671422019408045245438535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83561896025877393660584713 62671422019408045245438535)
    ·
      refine ⟨94007133029112067868157803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62671422019408045245438535 94007133029112067868157803)
      ·
        refine ⟨141010699543668101802236705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94007133029112067868157803 141010699543668101802236705)
        ·
          refine ⟨105758024657751076351677529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141010699543668101802236705 105758024657751076351677529)
          ·
            refine ⟨79318518493313307263758147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105758024657751076351677529 79318518493313307263758147)
            ·
              refine ⟨118977777739969960895637221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79318518493313307263758147 118977777739969960895637221)
              ·
                refine ⟨22308333326244367667931979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118977777739969960895637221 22308333326244367667931979)
                ·
                  refine ⟨33462499989366551501897969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22308333326244367667931979 33462499989366551501897969)
                  ·
                    refine ⟨25096874992024913626423477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33462499989366551501897969 25096874992024913626423477)
                    ·
                      refine ⟨2352832030502335652477201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25096874992024913626423477 2352832030502335652477201)
                      ·
                        rfl

theorem cell23_4582124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_4582124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582124 prefixEnd_4582124 := by exact prefixLift 4582124
  have htrace : WordTrace (prefixWord ++ tailWord_4582124) baseStart_4582124 baseEnd_4582124 := by
    simpa [prefixWord, tailWord_4582124, baseEnd_4582124] using wordTrace_append hprefix tailTrace_4582124
  have hstable : (prefixWord ++ tailWord_4582124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582124).length < 2 ^ (prefixWord ++ tailWord_4582124).sum := by decide
  have hdescent : baseEnd_4582124 < baseStart_4582124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582161 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 3, 4]
def baseStart_4582161 : Nat := 118140960795 + 4582161 * 2 ^ 59
def prefixEnd_4582161 : Nat := 4983230072969 + 3 ^ 40 * 4582161 * 2
def baseEnd_4582161 : Nat := 784283676428850669238177

theorem tailTrace_4582161 : CollatzResearch.WordTrace tailWord_4582161 prefixEnd_4582161 784283676428850669238177 := by
  unfold tailWord_4582161
  simp only [CollatzResearch.WordTrace]
  refine ⟨167125141552620742640266337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111416761035080495093510891 167125141552620742640266337)
  ·
    refine ⟨125343856164465556980199753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167125141552620742640266337 125343856164465556980199753)
    ·
      refine ⟨94007892123349167735149815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125343856164465556980199753 94007892123349167735149815)
      ·
        refine ⟨141011838185023751602724723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94007892123349167735149815 141011838185023751602724723)
        ·
          refine ⟨211517757277535627404087085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141011838185023751602724723 211517757277535627404087085)
          ·
            refine ⟨79319158979075860276532657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211517757277535627404087085 79319158979075860276532657)
            ·
              refine ⟨59489369234306895207399493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79319158979075860276532657 59489369234306895207399493)
              ·
                refine ⟨11154256731432542851387405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59489369234306895207399493 11154256731432542851387405)
                ·
                  refine ⟨4182846274287203569270277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11154256731432542851387405 4182846274287203569270277)
                  ·
                    refine ⟨784283676428850669238177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182846274287203569270277 784283676428850669238177)
                    ·
                      rfl

theorem cell23_4582161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_4582161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582161 prefixEnd_4582161 := by exact prefixLift 4582161
  have htrace : WordTrace (prefixWord ++ tailWord_4582161) baseStart_4582161 baseEnd_4582161 := by
    simpa [prefixWord, tailWord_4582161, baseEnd_4582161] using wordTrace_append hprefix tailTrace_4582161
  have hstable : (prefixWord ++ tailWord_4582161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582161).length < 2 ^ (prefixWord ++ tailWord_4582161).sum := by decide
  have hdescent : baseEnd_4582161 < baseStart_4582161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582195 : List Nat := [1, 1, 1, 2, 6, 2, 1, 4, 1, 4]
def baseStart_4582195 : Nat := 118140960795 + 4582195 * 2 ^ 59
def prefixEnd_4582195 : Nat := 4983230072969 + 3 ^ 40 * 4582195 * 2
def baseEnd_4582195 : Nat := 784289495876268291563125

theorem tailTrace_4582195 : CollatzResearch.WordTrace tailWord_4582195 prefixEnd_4582195 784289495876268291563125 := by
  unfold tailWord_4582195
  simp only [CollatzResearch.WordTrace]
  refine ⟨167126381634497566447004039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111417587756331710964669359 167126381634497566447004039)
  ·
    refine ⟨250689572451746349670506059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167126381634497566447004039 250689572451746349670506059)
    ·
      refine ⟨376034358677619524505759089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250689572451746349670506059 376034358677619524505759089)
      ·
        refine ⟨282025769008214643379319317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376034358677619524505759089 282025769008214643379319317)
        ·
          refine ⟨13219957922260061408405593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 282025769008214643379319317 13219957922260061408405593)
          ·
            refine ⟨9914968441695046056304195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13219957922260061408405593 9914968441695046056304195)
            ·
              refine ⟨14872452662542569084456293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9914968441695046056304195 14872452662542569084456293)
              ·
                refine ⟨2788584874226731703335555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14872452662542569084456293 2788584874226731703335555)
                ·
                  refine ⟨4182877311340097555003333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788584874226731703335555 4182877311340097555003333)
                  ·
                    refine ⟨784289495876268291563125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182877311340097555003333 784289495876268291563125)
                    ·
                      rfl

theorem cell23_4582195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 1, 4].length) (baseStart_4582195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582195 prefixEnd_4582195 := by exact prefixLift 4582195
  have htrace : WordTrace (prefixWord ++ tailWord_4582195) baseStart_4582195 baseEnd_4582195 := by
    simpa [prefixWord, tailWord_4582195, baseEnd_4582195] using wordTrace_append hprefix tailTrace_4582195
  have hstable : (prefixWord ++ tailWord_4582195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582195).length < 2 ^ (prefixWord ++ tailWord_4582195).sum := by decide
  have hdescent : baseEnd_4582195 < baseStart_4582195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582212 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_4582212 : Nat := 118140960795 + 4582212 * 2 ^ 59
def prefixEnd_4582212 : Nat := 4983230072969 + 3 ^ 40 * 4582212 * 2
def baseEnd_4582212 : Nat := 784292405599977102725599

theorem tailTrace_4582212 : CollatzResearch.WordTrace tailWord_4582212 prefixEnd_4582212 784292405599977102725599 := by
  unfold tailWord_4582212
  simp only [CollatzResearch.WordTrace]
  refine ⟨83563500837717989175186445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111418001116957318900248593 83563500837717989175186445)
  ·
    refine ⟨31336312814144245940694917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83563500837717989175186445 31336312814144245940694917)
    ·
      refine ⟨5875558652652046113880297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31336312814144245940694917 5875558652652046113880297)
      ·
        refine ⟨4406668989489034585410223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5875558652652046113880297 4406668989489034585410223)
        ·
          refine ⟨6610003484233551878115335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406668989489034585410223 6610003484233551878115335)
          ·
            refine ⟨9915005226350327817173003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6610003484233551878115335 9915005226350327817173003)
            ·
              refine ⟨14872507839525491725759505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9915005226350327817173003 14872507839525491725759505)
              ·
                refine ⟨11154380879644118794319629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14872507839525491725759505 11154380879644118794319629)
                ·
                  refine ⟨4182892829866544547869861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11154380879644118794319629 4182892829866544547869861)
                  ·
                    refine ⟨784292405599977102725599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182892829866544547869861 784292405599977102725599)
                    ·
                      rfl

theorem cell23_4582212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_4582212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582212 prefixEnd_4582212 := by exact prefixLift 4582212
  have htrace : WordTrace (prefixWord ++ tailWord_4582212) baseStart_4582212 baseEnd_4582212 := by
    simpa [prefixWord, tailWord_4582212, baseEnd_4582212] using wordTrace_append hprefix tailTrace_4582212
  have hstable : (prefixWord ++ tailWord_4582212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582212).length < 2 ^ (prefixWord ++ tailWord_4582212).sum := by decide
  have hdescent : baseEnd_4582212 < baseStart_4582212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582241 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_4582241 : Nat := 118140960795 + 4582241 * 2 ^ 59
def prefixEnd_4582241 : Nat := 4983230072969 + 3 ^ 40 * 4582241 * 2
def baseEnd_4582241 : Nat := 2352892107738911694714163

theorem tailTrace_4582241 : CollatzResearch.WordTrace tailWord_4582241 prefixEnd_4582241 2352892107738911694714163 := by
  unfold tailWord_4582241
  simp only [CollatzResearch.WordTrace]
  refine ⟨167128059392330916303178577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111418706261553944202119051 167128059392330916303178577)
  ·
    refine ⟨125346044544248187227383933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167128059392330916303178577 125346044544248187227383933)
    ·
      refine ⟨47004766704093070210268975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125346044544248187227383933 47004766704093070210268975)
      ·
        refine ⟨70507150056139605315403463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47004766704093070210268975 70507150056139605315403463)
        ·
          refine ⟨105760725084209407973105195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70507150056139605315403463 105760725084209407973105195)
          ·
            refine ⟨158641087626314111959657793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105760725084209407973105195 158641087626314111959657793)
            ·
              refine ⟨118980815719735583969743345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158641087626314111959657793 118980815719735583969743345)
              ·
                refine ⟨89235611789801687977307509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118980815719735583969743345 89235611789801687977307509)
                ·
                  refine ⟨8365838605293908247872579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89235611789801687977307509 8365838605293908247872579)
                  ·
                    refine ⟨12548757907940862371808869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8365838605293908247872579 12548757907940862371808869)
                    ·
                      refine ⟨2352892107738911694714163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12548757907940862371808869 2352892107738911694714163)
                      ·
                        rfl

theorem cell23_4582241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_4582241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582241 prefixEnd_4582241 := by exact prefixLift 4582241
  have htrace : WordTrace (prefixWord ++ tailWord_4582241) baseStart_4582241 baseEnd_4582241 := by
    simpa [prefixWord, tailWord_4582241, baseEnd_4582241] using wordTrace_append hprefix tailTrace_4582241
  have hstable : (prefixWord ++ tailWord_4582241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582241).length < 2 ^ (prefixWord ++ tailWord_4582241).sum := by decide
  have hdescent : baseEnd_4582241 < baseStart_4582241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582242 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 6]
def baseStart_4582242 : Nat := 118140960795 + 4582242 * 2 ^ 59
def prefixEnd_4582242 : Nat := 4983230072969 + 3 ^ 40 * 4582242 * 2
def baseEnd_4582242 : Nat := 261432513468840687866851

theorem tailTrace_4582242 : CollatzResearch.WordTrace tailWord_4582242 prefixEnd_4582242 261432513468840687866851 := by
  unfold tailWord_4582242
  simp only [CollatzResearch.WordTrace]
  refine ⟨41782023966331823368491245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111418730576884862315976653 41782023966331823368491245)
  ·
    refine ⟨15668258987374433763184217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41782023966331823368491245 15668258987374433763184217)
    ·
      refine ⟨11751194240530825322388163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15668258987374433763184217 11751194240530825322388163)
      ·
        refine ⟨17626791360796237983582245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11751194240530825322388163 17626791360796237983582245)
        ·
          refine ⟨3305023380149294621921671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17626791360796237983582245 3305023380149294621921671)
          ·
            refine ⟨4957535070223941932882507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305023380149294621921671 4957535070223941932882507)
            ·
              refine ⟨7436302605335912899323761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4957535070223941932882507 7436302605335912899323761)
              ·
                refine ⟨5577226954001934674492821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7436302605335912899323761 5577226954001934674492821)
                ·
                  refine ⟨261432513468840687866851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5577226954001934674492821 261432513468840687866851)
                  ·
                    rfl

theorem cell23_4582242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_4582242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582242 prefixEnd_4582242 := by exact prefixLift 4582242
  have htrace : WordTrace (prefixWord ++ tailWord_4582242) baseStart_4582242 baseEnd_4582242 := by
    simpa [prefixWord, tailWord_4582242, baseEnd_4582242] using wordTrace_append hprefix tailTrace_4582242
  have hstable : (prefixWord ++ tailWord_4582242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582242).length < 2 ^ (prefixWord ++ tailWord_4582242).sum := by decide
  have hdescent : baseEnd_4582242 < baseStart_4582242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582268 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_4582268 : Nat := 118140960795 + 4582268 * 2 ^ 59
def prefixEnd_4582268 : Nat := 4983230072969 + 3 ^ 40 * 4582268 * 2
def baseEnd_4582268 : Nat := 784301990572194363025513

theorem tailTrace_4582268 : CollatzResearch.WordTrace tailWord_4582268 prefixEnd_4582268 784301990572194363025513 := by
  unfold tailWord_4582268
  simp only [CollatzResearch.WordTrace]
  refine ⟨83564522081616549957205729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111419362775488733276274305 83564522081616549957205729)
  ·
    refine ⟨62673391561212412467904297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83564522081616549957205729 62673391561212412467904297)
    ·
      refine ⟨47005043670909309350928223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62673391561212412467904297 47005043670909309350928223)
      ·
        refine ⟨70507565506363964026392335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47005043670909309350928223 70507565506363964026392335)
        ·
          refine ⟨105761348259545946039588503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70507565506363964026392335 105761348259545946039588503)
          ·
            refine ⟨158642022389318919059382755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105761348259545946039588503 158642022389318919059382755)
            ·
              refine ⟨237963033583978378589074133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158642022389318919059382755 237963033583978378589074133)
              ·
                refine ⟨5577258599624493248181425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 237963033583978378589074133 5577258599624493248181425)
                ·
                  refine ⟨4182943949718369936136069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5577258599624493248181425 4182943949718369936136069)
                  ·
                    refine ⟨784301990572194363025513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182943949718369936136069 784301990572194363025513)
                    ·
                      rfl

theorem cell23_4582268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_4582268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582268 prefixEnd_4582268 := by exact prefixLift 4582268
  have htrace : WordTrace (prefixWord ++ tailWord_4582268) baseStart_4582268 baseEnd_4582268 := by
    simpa [prefixWord, tailWord_4582268, baseEnd_4582268] using wordTrace_append hprefix tailTrace_4582268
  have hstable : (prefixWord ++ tailWord_4582268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582268).length < 2 ^ (prefixWord ++ tailWord_4582268).sum := by decide
  have hdescent : baseEnd_4582268 < baseStart_4582268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582275 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 3, 2, 2]
def baseStart_4582275 : Nat := 118140960795 + 4582275 * 2 ^ 59
def prefixEnd_4582275 : Nat := 4983230072969 + 3 ^ 40 * 4582275 * 2
def baseEnd_4582275 : Nat := 2352909566081164561689007

theorem tailTrace_4582275 : CollatzResearch.WordTrace tailWord_4582275 prefixEnd_4582275 2352909566081164561689007 := by
  unfold tailWord_4582275
  simp only [CollatzResearch.WordTrace]
  refine ⟨167129299474207740109916279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111419532982805160073277519 167129299474207740109916279)
  ·
    refine ⟨250693949211311610164874419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167129299474207740109916279 250693949211311610164874419)
    ·
      refine ⟨376040923816967415247311629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250693949211311610164874419 376040923816967415247311629)
      ·
        refine ⟨141015346431362780717741861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376040923816967415247311629 141015346431362780717741861)
        ·
          refine ⟨26440377455880521384576599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141015346431362780717741861 26440377455880521384576599)
          ·
            refine ⟨39660566183820782076864899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26440377455880521384576599 39660566183820782076864899)
            ·
              refine ⟨59490849275731173115297349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39660566183820782076864899 59490849275731173115297349)
              ·
                refine ⟨11154534239199594959118253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59490849275731173115297349 11154534239199594959118253)
                ·
                  refine ⟨4182950339699848109669345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11154534239199594959118253 4182950339699848109669345)
                  ·
                    refine ⟨3137212754774886082252009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4182950339699848109669345 3137212754774886082252009)
                    ·
                      refine ⟨2352909566081164561689007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3137212754774886082252009 2352909566081164561689007)
                      ·
                        rfl

theorem cell23_4582275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_4582275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582275 prefixEnd_4582275 := by exact prefixLift 4582275
  have htrace : WordTrace (prefixWord ++ tailWord_4582275) baseStart_4582275 baseEnd_4582275 := by
    simpa [prefixWord, tailWord_4582275, baseEnd_4582275] using wordTrace_append hprefix tailTrace_4582275
  have hstable : (prefixWord ++ tailWord_4582275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582275).length < 2 ^ (prefixWord ++ tailWord_4582275).sum := by decide
  have hdescent : baseEnd_4582275 < baseStart_4582275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582281 : List Nat := [1, 2, 1, 1, 5, 3, 1, 9]
def baseStart_4582281 : Nat := 118140960795 + 4582281 * 2 ^ 59
def prefixEnd_4582281 : Nat := 4983230072969 + 3 ^ 40 * 4582281 * 2
def baseEnd_4582281 : Nat := 87144912850558945859777

theorem tailTrace_4582281 : CollatzResearch.WordTrace tailWord_4582281 prefixEnd_4582281 87144912850558945859777 := by
  unfold tailWord_4582281
  simp only [CollatzResearch.WordTrace]
  refine ⟨167129518312186003134634697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111419678874790668756423131 167129518312186003134634697)
  ·
    refine ⟨125347138734139502350976023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167129518312186003134634697 125347138734139502350976023)
    ·
      refine ⟨188020708101209253526464035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125347138734139502350976023 188020708101209253526464035)
      ·
        refine ⟨282031062151813880289696053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188020708101209253526464035 282031062151813880289696053)
        ·
          refine ⟨26440412076732551277159005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 282031062151813880289696053 26440412076732551277159005)
          ·
            refine ⟨9915154528774706728934627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26440412076732551277159005 9915154528774706728934627)
            ·
              refine ⟨14872731793162060093401941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9915154528774706728934627 14872731793162060093401941)
              ·
                refine ⟨87144912850558945859777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14872731793162060093401941 87144912850558945859777)
                ·
                  rfl

theorem cell23_4582281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 9].length) (baseStart_4582281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582281 prefixEnd_4582281 := by exact prefixLift 4582281
  have htrace : WordTrace (prefixWord ++ tailWord_4582281) baseStart_4582281 baseEnd_4582281 := by
    simpa [prefixWord, tailWord_4582281, baseEnd_4582281] using wordTrace_append hprefix tailTrace_4582281
  have hstable : (prefixWord ++ tailWord_4582281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582281).length < 2 ^ (prefixWord ++ tailWord_4582281).sum := by decide
  have hdescent : baseEnd_4582281 < baseStart_4582281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582298 : List Nat := [3, 1, 1, 4, 3, 2, 9]
def baseStart_4582298 : Nat := 118140960795 + 4582298 * 2 ^ 59
def prefixEnd_4582298 : Nat := 4983230072969 + 3 ^ 40 * 4582298 * 2
def baseEnd_4582298 : Nat := 29048412051064419403721

theorem tailTrace_4582298 : CollatzResearch.WordTrace tailWord_4582298 prefixEnd_4582298 29048412051064419403721 := by
  unfold tailWord_4582298
  simp only [CollatzResearch.WordTrace]
  refine ⟨41782534588281103759500887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111420092235416276692002365 41782534588281103759500887)
  ·
    refine ⟨62673801882421655639251331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41782534588281103759500887 62673801882421655639251331)
    ·
      refine ⟨94010702823632483458876997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62673801882421655639251331 94010702823632483458876997)
      ·
        refine ⟨17627006779431090648539437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94010702823632483458876997 17627006779431090648539437)
        ·
          refine ⟨6610127542286658993202289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17627006779431090648539437 6610127542286658993202289)
          ·
            refine ⟨4957595656714994244901717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6610127542286658993202289 4957595656714994244901717)
            ·
              refine ⟨29048412051064419403721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4957595656714994244901717 29048412051064419403721)
              ·
                rfl

theorem cell23_4582298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 9].length) (baseStart_4582298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582298 prefixEnd_4582298 := by exact prefixLift 4582298
  have htrace : WordTrace (prefixWord ++ tailWord_4582298) baseStart_4582298 baseEnd_4582298 := by
    simpa [prefixWord, tailWord_4582298, baseEnd_4582298] using wordTrace_append hprefix tailTrace_4582298
  have hstable : (prefixWord ++ tailWord_4582298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582298).length < 2 ^ (prefixWord ++ tailWord_4582298).sum := by decide
  have hdescent : baseEnd_4582298 < baseStart_4582298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582335 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 1, 3, 2]
def baseStart_4582335 : Nat := 118140960795 + 4582335 * 2 ^ 59
def prefixEnd_4582335 : Nat := 4983230072969 + 3 ^ 40 * 4582335 * 2
def baseEnd_4582335 : Nat := 2352940374920434326938731

theorem tailTrace_4582335 : CollatzResearch.WordTrace tailWord_4582335 prefixEnd_4582335 2352940374920434326938731 := by
  unfold tailWord_4582335
  simp only [CollatzResearch.WordTrace]
  refine ⟨167131487853990370357100459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111420991902660246904733639 167131487853990370357100459)
  ·
    refine ⟨250697231780985555535650689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167131487853990370357100459 250697231780985555535650689)
    ·
      refine ⟨188022923835739166651738017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250697231780985555535650689 188022923835739166651738017)
      ·
        refine ⟨141017192876804374988803513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188022923835739166651738017 141017192876804374988803513)
        ·
          refine ⟨105762894657603281241602635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141017192876804374988803513 105762894657603281241602635)
          ·
            refine ⟨158644341986404921862403953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105762894657603281241602635 158644341986404921862403953)
            ·
              refine ⟨118983256489803691396802965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158644341986404921862403953 118983256489803691396802965)
              ·
                refine ⟨5577340147959548034225139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118983256489803691396802965 5577340147959548034225139)
                ·
                  refine ⟨8366010221939322051337709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5577340147959548034225139 8366010221939322051337709)
                  ·
                    refine ⟨3137253833227245769251641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8366010221939322051337709 3137253833227245769251641)
                    ·
                      refine ⟨2352940374920434326938731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3137253833227245769251641 2352940374920434326938731)
                      ·
                        rfl

theorem cell23_4582335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_4582335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582335 prefixEnd_4582335 := by exact prefixLift 4582335
  have htrace : WordTrace (prefixWord ++ tailWord_4582335) baseStart_4582335 baseEnd_4582335 := by
    simpa [prefixWord, tailWord_4582335, baseEnd_4582335] using wordTrace_append hprefix tailTrace_4582335
  have hstable : (prefixWord ++ tailWord_4582335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582335).length < 2 ^ (prefixWord ++ tailWord_4582335).sum := by decide
  have hdescent : baseEnd_4582335 < baseStart_4582335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582378 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_4582378 : Nat := 118140960795 + 4582378 * 2 ^ 59
def prefixEnd_4582378 : Nat := 4983230072969 + 3 ^ 40 * 4582378 * 2
def baseEnd_4582378 : Nat := 2352962454588577658701033

theorem tailTrace_4582378 : CollatzResearch.WordTrace tailWord_4582378 prefixEnd_4582378 2352962454588577658701033 := by
  unfold tailWord_4582378
  simp only [CollatzResearch.WordTrace]
  refine ⟨41783264048208647175228947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111422037461889725800610525 41783264048208647175228947)
  ·
    refine ⟨62674896072312970762843421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41783264048208647175228947 62674896072312970762843421)
    ·
      refine ⟨23503086027117364036066283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62674896072312970762843421 23503086027117364036066283)
      ·
        refine ⟨35254629040676046054099425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23503086027117364036066283 35254629040676046054099425)
        ·
          refine ⟨26440971780507034540574569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35254629040676046054099425 26440971780507034540574569)
          ·
            refine ⟨19830728835380275905430927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26440971780507034540574569 19830728835380275905430927)
            ·
              refine ⟨29746093253070413858146391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19830728835380275905430927 29746093253070413858146391)
              ·
                refine ⟨44619139879605620787219587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29746093253070413858146391 44619139879605620787219587)
                ·
                  refine ⟨66928709819408431180829381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44619139879605620787219587 66928709819408431180829381)
                  ·
                    refine ⟨12549133091139080846405509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66928709819408431180829381 12549133091139080846405509)
                    ·
                      refine ⟨2352962454588577658701033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12549133091139080846405509 2352962454588577658701033)
                      ·
                        rfl

theorem cell23_4582378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_4582378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582378 prefixEnd_4582378 := by exact prefixLift 4582378
  have htrace : WordTrace (prefixWord ++ tailWord_4582378) baseStart_4582378 baseEnd_4582378 := by
    simpa [prefixWord, tailWord_4582378, baseEnd_4582378] using wordTrace_append hprefix tailTrace_4582378
  have hstable : (prefixWord ++ tailWord_4582378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582378).length < 2 ^ (prefixWord ++ tailWord_4582378).sum := by decide
  have hdescent : baseEnd_4582378 < baseStart_4582378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582405 : List Nat := [1, 3, 1, 1, 2, 3, 4, 3, 5]
def baseStart_4582405 : Nat := 118140960795 + 4582405 * 2 ^ 59
def prefixEnd_4582405 : Nat := 4983230072969 + 3 ^ 40 * 4582405 * 2
def baseEnd_4582405 : Nat := 261441813174027672562601

theorem tailTrace_4582405 : CollatzResearch.WordTrace tailWord_4582405 prefixEnd_4582405 261441813174027672562601 := by
  unfold tailWord_4582405
  simp only [CollatzResearch.WordTrace]
  refine ⟨167134040963736772312148669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111422693975824514874765779 167134040963736772312148669)
  ·
    refine ⟨62675265361401289617055751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167134040963736772312148669 62675265361401289617055751)
    ·
      refine ⟨94012898042101934425583627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62675265361401289617055751 94012898042101934425583627)
      ·
        refine ⟨141019347063152901638375441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94012898042101934425583627 141019347063152901638375441)
        ·
          refine ⟨105764510297364676228781581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141019347063152901638375441 105764510297364676228781581)
          ·
            refine ⟨39661691361511753585793093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105764510297364676228781581 39661691361511753585793093)
            ·
              refine ⟨7436567130283453797336205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39661691361511753585793093 7436567130283453797336205)
              ·
                refine ⟨2788712673856295174001077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7436567130283453797336205 2788712673856295174001077)
                ·
                  refine ⟨261441813174027672562601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2788712673856295174001077 261441813174027672562601)
                  ·
                    rfl

theorem cell23_4582405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_4582405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582405 prefixEnd_4582405 := by exact prefixLift 4582405
  have htrace : WordTrace (prefixWord ++ tailWord_4582405) baseStart_4582405 baseEnd_4582405 := by
    simpa [prefixWord, tailWord_4582405, baseEnd_4582405] using wordTrace_append hprefix tailTrace_4582405
  have hstable : (prefixWord ++ tailWord_4582405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582405).length < 2 ^ (prefixWord ++ tailWord_4582405).sum := by decide
  have hdescent : baseEnd_4582405 < baseStart_4582405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582478 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_4582478 : Nat := 118140960795 + 4582478 * 2 ^ 59
def prefixEnd_4582478 : Nat := 4983230072969 + 3 ^ 40 * 4582478 * 2
def baseEnd_4582478 : Nat := 261445978072669696383397

theorem tailTrace_4582478 : CollatzResearch.WordTrace tailWord_4582478 prefixEnd_4582478 261445978072669696383397 := by
  unfold tailWord_4582478
  simp only [CollatzResearch.WordTrace]
  refine ⟨20892087936559038222444511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111424468994981537186370725 20892087936559038222444511)
  ·
    refine ⟨31338131904838557333666767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20892087936559038222444511 31338131904838557333666767)
    ·
      refine ⟨47007197857257836000500151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31338131904838557333666767 47007197857257836000500151)
      ·
        refine ⟨70510796785886754000750227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47007197857257836000500151 70510796785886754000750227)
        ·
          refine ⟨105766195178830131001125341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70510796785886754000750227 105766195178830131001125341)
          ·
            refine ⟨39662323192061299125422003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105766195178830131001125341 39662323192061299125422003)
            ·
              refine ⟨59493484788091948688133005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39662323192061299125422003 59493484788091948688133005)
              ·
                refine ⟨22310056795534480758049877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59493484788091948688133005 22310056795534480758049877)
                ·
                  refine ⟨261445978072669696383397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22310056795534480758049877 261445978072669696383397)
                  ·
                    rfl

theorem cell23_4582478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_4582478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582478 prefixEnd_4582478 := by exact prefixLift 4582478
  have htrace : WordTrace (prefixWord ++ tailWord_4582478) baseStart_4582478 baseEnd_4582478 := by
    simpa [prefixWord, tailWord_4582478, baseEnd_4582478] using wordTrace_append hprefix tailTrace_4582478
  have hstable : (prefixWord ++ tailWord_4582478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582478).length < 2 ^ (prefixWord ++ tailWord_4582478).sum := by decide
  have hdescent : baseEnd_4582478 < baseStart_4582478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582482 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_4582482 : Nat := 118140960795 + 4582482 * 2 ^ 59
def prefixEnd_4582482 : Nat := 4983230072969 + 3 ^ 40 * 4582482 * 2
def baseEnd_4582482 : Nat := 784338618858881750600185

theorem tailTrace_4582482 : CollatzResearch.WordTrace tailWord_4582482 prefixEnd_4582482 784338618858881750600185 := by
  unfold tailWord_4582482
  simp only [CollatzResearch.WordTrace]
  refine ⟨41784212346114453615675425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111424566256305209641801133 41784212346114453615675425)
  ·
    refine ⟨31338159259585840211756569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41784212346114453615675425 31338159259585840211756569)
    ·
      refine ⟨23503619444689380158817427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31338159259585840211756569 23503619444689380158817427)
      ·
        refine ⟨35255429167034070238226141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23503619444689380158817427 35255429167034070238226141)
        ·
          refine ⟨13220785937637776339334803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35255429167034070238226141 13220785937637776339334803)
          ·
            refine ⟨19831178906456664509002205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13220785937637776339334803 19831178906456664509002205)
            ·
              refine ⟨7436692089921249190875827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19831178906456664509002205 7436692089921249190875827)
              ·
                refine ⟨11155038134881873786313741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7436692089921249190875827 11155038134881873786313741)
                ·
                  refine ⟨4183139300580702669867653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11155038134881873786313741 4183139300580702669867653)
                  ·
                    refine ⟨784338618858881750600185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4183139300580702669867653 784338618858881750600185)
                    ·
                      rfl

theorem cell23_4582482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_4582482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582482 prefixEnd_4582482 := by exact prefixLift 4582482
  have htrace : WordTrace (prefixWord ++ tailWord_4582482) baseStart_4582482 baseEnd_4582482 := by
    simpa [prefixWord, tailWord_4582482, baseEnd_4582482] using wordTrace_append hprefix tailTrace_4582482
  have hstable : (prefixWord ++ tailWord_4582482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582482).length < 2 ^ (prefixWord ++ tailWord_4582482).sum := by decide
  have hdescent : baseEnd_4582482 < baseStart_4582482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582533 : List Nat := [1, 3, 1, 1, 7, 1, 2, 2, 1, 4]
def baseStart_4582533 : Nat := 118140960795 + 4582533 * 2 ^ 59
def prefixEnd_4582533 : Nat := 4983230072969 + 3 ^ 40 * 4582533 * 2
def baseEnd_4582533 : Nat := 784347348030008184087607

theorem tailTrace_4582533 : CollatzResearch.WordTrace tailWord_4582533 prefixEnd_4582533 784347348030008184087607 := by
  unfold tailWord_4582533
  simp only [CollatzResearch.WordTrace]
  refine ⟨167138709507273050172808253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111425806338182033448538835 167138709507273050172808253)
  ·
    refine ⟨62677016065227393814803095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167138709507273050172808253 62677016065227393814803095)
    ·
      refine ⟨94015524097841090722204643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62677016065227393814803095 94015524097841090722204643)
      ·
        refine ⟨141023286146761636083306965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94015524097841090722204643 141023286146761636083306965)
        ·
          refine ⟨3305233269064725845702507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 141023286146761636083306965 3305233269064725845702507)
          ·
            refine ⟨4957849903597088768553761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305233269064725845702507 4957849903597088768553761)
            ·
              refine ⟨3718387427697816576415321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4957849903597088768553761 3718387427697816576415321)
              ·
                refine ⟨2788790570773362432311491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3718387427697816576415321 2788790570773362432311491)
                ·
                  refine ⟨4183185856160043648467237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788790570773362432311491 4183185856160043648467237)
                  ·
                    refine ⟨784347348030008184087607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4183185856160043648467237 784347348030008184087607)
                    ·
                      rfl

theorem cell23_4582533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_4582533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582533 prefixEnd_4582533 := by exact prefixLift 4582533
  have htrace : WordTrace (prefixWord ++ tailWord_4582533) baseStart_4582533 baseEnd_4582533 := by
    simpa [prefixWord, tailWord_4582533, baseEnd_4582533] using wordTrace_append hprefix tailTrace_4582533
  have hstable : (prefixWord ++ tailWord_4582533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582533).length < 2 ^ (prefixWord ++ tailWord_4582533).sum := by decide
  have hdescent : baseEnd_4582533 < baseStart_4582533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582573 : List Nat := [1, 5, 2, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_4582573 : Nat := 118140960795 + 4582573 * 2 ^ 59
def prefixEnd_4582573 : Nat := 4983230072969 + 3 ^ 40 * 4582573 * 2
def baseEnd_4582573 : Nat := 2353062583316204395762637

theorem tailTrace_4582573 : CollatzResearch.WordTrace tailWord_4582573 prefixEnd_4582573 2353062583316204395762637 := by
  unfold tailWord_4582573
  simp only [CollatzResearch.WordTrace]
  refine ⟨167140168427128137004264373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111426778951418758002842915 167140168427128137004264373)
  ·
    refine ⟨15669390790043262844149785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167140168427128137004264373 15669390790043262844149785)
    ·
      refine ⟨11752043092532447133112339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15669390790043262844149785 11752043092532447133112339)
      ·
        refine ⟨17628064638798670699668509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11752043092532447133112339 17628064638798670699668509)
        ·
          refine ⟨6610524239549501512375691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17628064638798670699668509 6610524239549501512375691)
          ·
            refine ⟨9915786359324252268563537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6610524239549501512375691 9915786359324252268563537)
            ·
              refine ⟨7436839769493189201422653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9915786359324252268563537 7436839769493189201422653)
              ·
                refine ⟨2788814913559945950533495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7436839769493189201422653 2788814913559945950533495)
                ·
                  refine ⟨4183222370339918925800243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788814913559945950533495 4183222370339918925800243)
                  ·
                    refine ⟨6274833555509878388700365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4183222370339918925800243 6274833555509878388700365)
                    ·
                      refine ⟨2353062583316204395762637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6274833555509878388700365 2353062583316204395762637)
                      ·
                        rfl

theorem cell23_4582573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_4582573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582573 prefixEnd_4582573 := by exact prefixLift 4582573
  have htrace : WordTrace (prefixWord ++ tailWord_4582573) baseStart_4582573 baseEnd_4582573 := by
    simpa [prefixWord, tailWord_4582573, baseEnd_4582573] using wordTrace_append hprefix tailTrace_4582573
  have hstable : (prefixWord ++ tailWord_4582573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582573).length < 2 ^ (prefixWord ++ tailWord_4582573).sum := by decide
  have hdescent : baseEnd_4582573 < baseStart_4582573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582575 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 4]
def baseStart_4582575 : Nat := 118140960795 + 4582575 * 2 ^ 59
def prefixEnd_4582575 : Nat := 4983230072969 + 3 ^ 40 * 4582575 * 2
def baseEnd_4582575 : Nat := 2353063610277513387937627

theorem tailTrace_4582575 : CollatzResearch.WordTrace tailWord_4582575 prefixEnd_4582575 2353063610277513387937627 := by
  unfold tailWord_4582575
  simp only [CollatzResearch.WordTrace]
  refine ⟨167140241373120891345837179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111426827582080594230558119 167140241373120891345837179)
  ·
    refine ⟨250710362059681337018755769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167140241373120891345837179 250710362059681337018755769)
    ·
      refine ⟨188032771544761002764066827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250710362059681337018755769 188032771544761002764066827)
      ·
        refine ⟨282049157317141504146100241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188032771544761002764066827 282049157317141504146100241)
        ·
          refine ⟨211536867987856128109575181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282049157317141504146100241 211536867987856128109575181)
          ·
            refine ⟨79326325495446048041090693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211536867987856128109575181 79326325495446048041090693)
            ·
              refine ⟨14873686030396134007704505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79326325495446048041090693 14873686030396134007704505)
              ·
                refine ⟨11155264522797100505778379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14873686030396134007704505 11155264522797100505778379)
                ·
                  refine ⟨16732896784195650758667569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11155264522797100505778379 16732896784195650758667569)
                  ·
                    refine ⟨12549672588146738069000677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16732896784195650758667569 12549672588146738069000677)
                    ·
                      refine ⟨2353063610277513387937627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12549672588146738069000677 2353063610277513387937627)
                      ·
                        rfl

theorem cell23_4582575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_4582575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582575 prefixEnd_4582575 := by exact prefixLift 4582575
  have htrace : WordTrace (prefixWord ++ tailWord_4582575) baseStart_4582575 baseEnd_4582575 := by
    simpa [prefixWord, tailWord_4582575, baseEnd_4582575] using wordTrace_append hprefix tailTrace_4582575
  have hstable : (prefixWord ++ tailWord_4582575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582575).length < 2 ^ (prefixWord ++ tailWord_4582575).sum := by decide
  have hdescent : baseEnd_4582575 < baseStart_4582575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582606 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_4582606 : Nat := 118140960795 + 4582606 * 2 ^ 59
def prefixEnd_4582606 : Nat := 4983230072969 + 3 ^ 40 * 4582606 * 2
def baseEnd_4582606 : Nat := 784359842725934255549995

theorem tailTrace_4582606 : CollatzResearch.WordTrace tailWord_4582606 prefixEnd_4582606 784359842725934255549995 := by
  unfold tailWord_4582606
  simp only [CollatzResearch.WordTrace]
  refine ⟨20892671504501072955026959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111427581357339055760143781 20892671504501072955026959)
  ·
    refine ⟨31339007256751609432540439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20892671504501072955026959 31339007256751609432540439)
    ·
      refine ⟨47008510885127414148810659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31339007256751609432540439 47008510885127414148810659)
      ·
        refine ⟨70512766327691121223215989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47008510885127414148810659 70512766327691121223215989)
        ·
          refine ⟨6610571843221042614676499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70512766327691121223215989 6610571843221042614676499)
          ·
            refine ⟨9915857764831563922014749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6610571843221042614676499 9915857764831563922014749)
            ·
              refine ⟨3718446661811836470755531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9915857764831563922014749 3718446661811836470755531)
              ·
                refine ⟨5577669992717754706133297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718446661811836470755531 5577669992717754706133297)
                ·
                  refine ⟨4183252494538316029599973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5577669992717754706133297 4183252494538316029599973)
                  ·
                    refine ⟨784359842725934255549995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4183252494538316029599973 784359842725934255549995)
                    ·
                      rfl

theorem cell23_4582606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_4582606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582606 prefixEnd_4582606 := by exact prefixLift 4582606
  have htrace : WordTrace (prefixWord ++ tailWord_4582606) baseStart_4582606 baseEnd_4582606 := by
    simpa [prefixWord, tailWord_4582606, baseEnd_4582606] using wordTrace_append hprefix tailTrace_4582606
  have hstable : (prefixWord ++ tailWord_4582606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582606).length < 2 ^ (prefixWord ++ tailWord_4582606).sum := by decide
  have hdescent : baseEnd_4582606 < baseStart_4582606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582625 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_4582625 : Nat := 118140960795 + 4582625 * 2 ^ 59
def prefixEnd_4582625 : Nat := 4983230072969 + 3 ^ 40 * 4582625 * 2
def baseEnd_4582625 : Nat := 2353089284310238192312397

theorem tailTrace_4582625 : CollatzResearch.WordTrace tailWord_4582625 prefixEnd_4582625 2353089284310238192312397 := by
  unfold tailWord_4582625
  simp only [CollatzResearch.WordTrace]
  refine ⟨167142065022939749885157329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111428043348626499923438219 167142065022939749885157329)
  ·
    refine ⟨125356548767204812413867997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167142065022939749885157329 125356548767204812413867997)
    ·
      refine ⟨47008705787701804655200499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125356548767204812413867997 47008705787701804655200499)
      ·
        refine ⟨70513058681552706982800749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47008705787701804655200499 70513058681552706982800749)
        ·
          refine ⟨26442397005582265118550281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70513058681552706982800749 26442397005582265118550281)
          ·
            refine ⟨19831797754186698838912711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26442397005582265118550281 19831797754186698838912711)
            ·
              refine ⟨29747696631280048258369067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19831797754186698838912711 29747696631280048258369067)
              ·
                refine ⟨44621544946920072387553601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29747696631280048258369067 44621544946920072387553601)
                ·
                  refine ⟨33466158710190054290665201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44621544946920072387553601 33466158710190054290665201)
                  ·
                    refine ⟨25099619032642540717998901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33466158710190054290665201 25099619032642540717998901)
                    ·
                      refine ⟨2353089284310238192312397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25099619032642540717998901 2353089284310238192312397)
                      ·
                        rfl

theorem cell23_4582625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_4582625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582625 prefixEnd_4582625 := by exact prefixLift 4582625
  have htrace : WordTrace (prefixWord ++ tailWord_4582625) baseStart_4582625 baseEnd_4582625 := by
    simpa [prefixWord, tailWord_4582625, baseEnd_4582625] using wordTrace_append hprefix tailTrace_4582625
  have hstable : (prefixWord ++ tailWord_4582625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582625).length < 2 ^ (prefixWord ++ tailWord_4582625).sum := by decide
  have hdescent : baseEnd_4582625 < baseStart_4582625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582665 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_4582665 : Nat := 118140960795 + 4582665 * 2 ^ 59
def prefixEnd_4582665 : Nat := 4983230072969 + 3 ^ 40 * 4582665 * 2
def baseEnd_4582665 : Nat := 2353109823536418035812213

theorem tailTrace_4582665 : CollatzResearch.WordTrace tailWord_4582665 prefixEnd_4582665 2353109823536418035812213 := by
  unfold tailWord_4582665
  simp only [CollatzResearch.WordTrace]
  refine ⟨167143523942794836716613449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111429015961863224477742299 167143523942794836716613449)
  ·
    refine ⟨125357642957096127537460087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167143523942794836716613449 125357642957096127537460087)
    ·
      refine ⟨188036464435644191306190131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125357642957096127537460087 188036464435644191306190131)
      ·
        refine ⟨282054696653466286959285197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188036464435644191306190131 282054696653466286959285197)
        ·
          refine ⟨105770511245049857609731949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282054696653466286959285197 105770511245049857609731949)
          ·
            refine ⟨39663941716893696603649481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105770511245049857609731949 39663941716893696603649481)
            ·
              refine ⟨29747956287670272452737111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39663941716893696603649481 29747956287670272452737111)
              ·
                refine ⟨44621934431505408679105667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29747956287670272452737111 44621934431505408679105667)
                ·
                  refine ⟨66932901647258113018658501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44621934431505408679105667 66932901647258113018658501)
                  ·
                    refine ⟨12549919058860896190998469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66932901647258113018658501 12549919058860896190998469)
                    ·
                      refine ⟨2353109823536418035812213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12549919058860896190998469 2353109823536418035812213)
                      ·
                        rfl

theorem cell23_4582665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_4582665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582665 prefixEnd_4582665 := by exact prefixLift 4582665
  have htrace : WordTrace (prefixWord ++ tailWord_4582665) baseStart_4582665 baseEnd_4582665 := by
    simpa [prefixWord, tailWord_4582665, baseEnd_4582665] using wordTrace_append hprefix tailTrace_4582665
  have hstable : (prefixWord ++ tailWord_4582665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582665).length < 2 ^ (prefixWord ++ tailWord_4582665).sum := by decide
  have hdescent : baseEnd_4582665 < baseStart_4582665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582709 : List Nat := [1, 3, 3, 1, 2, 3, 1, 4, 5]
def baseStart_4582709 : Nat := 118140960795 + 4582709 * 2 ^ 59
def prefixEnd_4582709 : Nat := 4983230072969 + 3 ^ 40 * 4582709 * 2
def baseEnd_4582709 : Nat := 261459157409468429295779

theorem tailTrace_4582709 : CollatzResearch.WordTrace tailWord_4582709 prefixEnd_4582709 261459157409468429295779 := by
  unfold tailWord_4582709
  simp only [CollatzResearch.WordTrace]
  refine ⟨167145128754635432231215181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111430085836423621487476787 167145128754635432231215181)
  ·
    refine ⟨62679423282988287086705693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167145128754635432231215181 62679423282988287086705693)
    ·
      refine ⟨23504783731120607657514635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62679423282988287086705693 23504783731120607657514635)
      ·
        refine ⟨35257175596680911486271953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23504783731120607657514635 35257175596680911486271953)
        ·
          refine ⟨26442881697510683614703965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35257175596680911486271953 26442881697510683614703965)
          ·
            refine ⟨9916080636566506355513987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26442881697510683614703965 9916080636566506355513987)
            ·
              refine ⟨14874120954849759533270981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9916080636566506355513987 14874120954849759533270981)
              ·
                refine ⟨2788897679034329912488309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14874120954849759533270981 2788897679034329912488309)
                ·
                  refine ⟨261459157409468429295779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2788897679034329912488309 261459157409468429295779)
                  ·
                    rfl

theorem cell23_4582709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_4582709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582709 prefixEnd_4582709 := by exact prefixLift 4582709
  have htrace : WordTrace (prefixWord ++ tailWord_4582709) baseStart_4582709 baseEnd_4582709 := by
    simpa [prefixWord, tailWord_4582709, baseEnd_4582709] using wordTrace_append hprefix tailTrace_4582709
  have hstable : (prefixWord ++ tailWord_4582709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582709).length < 2 ^ (prefixWord ++ tailWord_4582709).sum := by decide
  have hdescent : baseEnd_4582709 < baseStart_4582709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582877 : List Nat := [1, 4, 3, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_4582877 : Nat := 118140960795 + 4582877 * 2 ^ 59
def prefixEnd_4582877 : Nat := 4983230072969 + 3 ^ 40 * 4582877 * 2
def baseEnd_4582877 : Nat := 2353218681435171206361239

theorem tailTrace_4582877 : CollatzResearch.WordTrace tailWord_4582877 prefixEnd_4582877 2353218681435171206361239 := by
  unfold tailWord_4582877
  simp only [CollatzResearch.WordTrace]
  refine ⟨167151256218026796923330885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111434170812017864615553923 167151256218026796923330885)
  ·
    refine ⟨31340860540880024423124541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167151256218026796923330885 31340860540880024423124541)
    ·
      refine ⟨11752822702830009158671703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31340860540880024423124541 11752822702830009158671703)
      ·
        refine ⟨17629234054245013738007555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11752822702830009158671703 17629234054245013738007555)
        ·
          refine ⟨26443851081367520607011333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17629234054245013738007555 26443851081367520607011333)
          ·
            refine ⟨4958222077756410113814625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26443851081367520607011333 4958222077756410113814625)
            ·
              refine ⟨3718666558317307585360969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4958222077756410113814625 3718666558317307585360969)
              ·
                refine ⟨2788999918737980689020727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3718666558317307585360969 2788999918737980689020727)
                ·
                  refine ⟨4183499878106971033531091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788999918737980689020727 4183499878106971033531091)
                  ·
                    refine ⟨6275249817160456550296637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4183499878106971033531091 6275249817160456550296637)
                    ·
                      refine ⟨2353218681435171206361239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6275249817160456550296637 2353218681435171206361239)
                      ·
                        rfl

theorem cell23_4582877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_4582877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582877 prefixEnd_4582877 := by exact prefixLift 4582877
  have htrace : WordTrace (prefixWord ++ tailWord_4582877) baseStart_4582877 baseEnd_4582877 := by
    simpa [prefixWord, tailWord_4582877, baseEnd_4582877] using wordTrace_append hprefix tailTrace_4582877
  have hstable : (prefixWord ++ tailWord_4582877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582877).length < 2 ^ (prefixWord ++ tailWord_4582877).sum := by decide
  have hdescent : baseEnd_4582877 < baseStart_4582877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582933 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_4582933 : Nat := 118140960795 + 4582933 * 2 ^ 59
def prefixEnd_4582933 : Nat := 4983230072969 + 3 ^ 40 * 4582933 * 2
def baseEnd_4582933 : Nat := 2353247436351822987260981

theorem tailTrace_4582933 : CollatzResearch.WordTrace tailWord_4582933 prefixEnd_4582933 2353247436351822987260981 := by
  unfold tailWord_4582933
  simp only [CollatzResearch.WordTrace]
  refine ⟨167153298705823918487369453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111435532470549278991579635 167153298705823918487369453)
  ·
    refine ⟨62682487014683969432763545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167153298705823918487369453 62682487014683969432763545)
    ·
      refine ⟨47011865261012977074572659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62682487014683969432763545 47011865261012977074572659)
      ·
        refine ⟨70517797891519465611858989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47011865261012977074572659 70517797891519465611858989)
        ·
          refine ⟨26444174209319799604447121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70517797891519465611858989 26444174209319799604447121)
          ·
            refine ⟨19833130656989849703335341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26444174209319799604447121 19833130656989849703335341)
            ·
              refine ⟨7437423996371193638750753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19833130656989849703335341 7437423996371193638750753)
              ·
                refine ⟨5578067997278395229063065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7437423996371193638750753 5578067997278395229063065)
                ·
                  refine ⟨4183550997958796421797299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5578067997278395229063065 4183550997958796421797299)
                  ·
                    refine ⟨6275326496938194632695949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4183550997958796421797299 6275326496938194632695949)
                    ·
                      refine ⟨2353247436351822987260981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6275326496938194632695949 2353247436351822987260981)
                      ·
                        rfl

theorem cell23_4582933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_4582933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582933 prefixEnd_4582933 := by exact prefixLift 4582933
  have htrace : WordTrace (prefixWord ++ tailWord_4582933) baseStart_4582933 baseEnd_4582933 := by
    simpa [prefixWord, tailWord_4582933, baseEnd_4582933] using wordTrace_append hprefix tailTrace_4582933
  have hstable : (prefixWord ++ tailWord_4582933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582933).length < 2 ^ (prefixWord ++ tailWord_4582933).sum := by decide
  have hdescent : baseEnd_4582933 < baseStart_4582933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4582939 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 10, 2]
def baseStart_4582939 : Nat := 118140960795 + 4582939 * 2 ^ 59
def prefixEnd_4582939 : Nat := 4983230072969 + 3 ^ 40 * 4582939 * 2
def baseEnd_4582939 : Nat := 2353250517235749963785953

theorem tailTrace_4582939 : CollatzResearch.WordTrace tailWord_4582939 prefixEnd_4582939 2353250517235749963785953 := by
  unfold tailWord_4582939
  simp only [CollatzResearch.WordTrace]
  refine ⟨167153517543802181512087871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111435678362534787674725247 167153517543802181512087871)
  ·
    refine ⟨250730276315703272268131807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167153517543802181512087871 250730276315703272268131807)
    ·
      refine ⟨376095414473554908402197711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250730276315703272268131807 376095414473554908402197711)
      ·
        refine ⟨564143121710332362603296567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376095414473554908402197711 564143121710332362603296567)
        ·
          refine ⟨846214682565498543904944851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564143121710332362603296567 846214682565498543904944851)
          ·
            refine ⟨1269322023848247815857417277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846214682565498543904944851 1269322023848247815857417277)
            ·
              refine ⟨475995758943092930946531479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1269322023848247815857417277 475995758943092930946531479)
              ·
                refine ⟨713993638414639396419797219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475995758943092930946531479 713993638414639396419797219)
                ·
                  refine ⟨1070990457621959094629695829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713993638414639396419797219 1070990457621959094629695829)
                  ·
                    refine ⟨3137667356314333285047937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1070990457621959094629695829 3137667356314333285047937)
                    ·
                      refine ⟨2353250517235749963785953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3137667356314333285047937 2353250517235749963785953)
                      ·
                        rfl

theorem cell23_4582939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 10, 2].length) (baseStart_4582939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4582939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4582939 prefixEnd_4582939 := by exact prefixLift 4582939
  have htrace : WordTrace (prefixWord ++ tailWord_4582939) baseStart_4582939 baseEnd_4582939 := by
    simpa [prefixWord, tailWord_4582939, baseEnd_4582939] using wordTrace_append hprefix tailTrace_4582939
  have hstable : (prefixWord ++ tailWord_4582939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4582939).length < 2 ^ (prefixWord ++ tailWord_4582939).sum := by decide
  have hdescent : baseEnd_4582939 < baseStart_4582939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4582939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583009 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 4, 5]
def baseStart_4583009 : Nat := 118140960795 + 4583009 * 2 ^ 59
def prefixEnd_4583009 : Nat := 4983230072969 + 3 ^ 40 * 4583009 * 2
def baseEnd_4583009 : Nat := 784428820293854896636877

theorem tailTrace_4583009 : CollatzResearch.WordTrace tailWord_4583009 prefixEnd_4583009 784428820293854896636877 := by
  unfold tailWord_4583009
  simp only [CollatzResearch.WordTrace]
  refine ⟨167156070653548583467136081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111437380435699055644757387 167156070653548583467136081)
  ·
    refine ⟨125367052990161437600352061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167156070653548583467136081 125367052990161437600352061)
    ·
      refine ⟨47012644871310539100132023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125367052990161437600352061 47012644871310539100132023)
      ·
        refine ⟨70518967306965808650198035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47012644871310539100132023 70518967306965808650198035)
        ·
          refine ⟨105778450960448712975297053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70518967306965808650198035 105778450960448712975297053)
          ·
            refine ⟨39666919110168267365736395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105778450960448712975297053 39666919110168267365736395)
            ·
              refine ⟨59500378665252401048604593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39666919110168267365736395 59500378665252401048604593)
              ·
                refine ⟨44625283998939300786453445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59500378665252401048604593 44625283998939300786453445)
                ·
                  refine ⟨8367240749801118897460021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44625283998939300786453445 8367240749801118897460021)
                  ·
                    refine ⟨784428820293854896636877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8367240749801118897460021 784428820293854896636877)
                    ·
                      rfl

theorem cell23_4583009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_4583009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583009 prefixEnd_4583009 := by exact prefixLift 4583009
  have htrace : WordTrace (prefixWord ++ tailWord_4583009) baseStart_4583009 baseEnd_4583009 := by
    simpa [prefixWord, tailWord_4583009, baseEnd_4583009] using wordTrace_append hprefix tailTrace_4583009
  have hstable : (prefixWord ++ tailWord_4583009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583009).length < 2 ^ (prefixWord ++ tailWord_4583009).sum := by decide
  have hdescent : baseEnd_4583009 < baseStart_4583009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583026 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_4583026 : Nat := 118140960795 + 4583026 * 2 ^ 59
def prefixEnd_4583026 : Nat := 4983230072969 + 3 ^ 40 * 4583026 * 2
def baseEnd_4583026 : Nat := 784431730017563707799351

theorem tailTrace_4583026 : CollatzResearch.WordTrace tailWord_4583026 prefixEnd_4583026 784431730017563707799351 := by
  unfold tailWord_4583026
  simp only [CollatzResearch.WordTrace]
  refine ⟨41789172673621748842626233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111437793796324663580336621 41789172673621748842626233)
  ·
    refine ⟨31341879505216311631969675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41789172673621748842626233 31341879505216311631969675)
    ·
      refine ⟨47012819257824467447954513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31341879505216311631969675 47012819257824467447954513)
      ·
        refine ⟨35259614443368350585965885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47012819257824467447954513 35259614443368350585965885)
        ·
          refine ⟨13222355416263131469737207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35259614443368350585965885 13222355416263131469737207)
          ·
            refine ⟨19833533124394697204605811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13222355416263131469737207 19833533124394697204605811)
            ·
              refine ⟨29750299686592045806908717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19833533124394697204605811 29750299686592045806908717)
              ·
                refine ⟨11156362382472017177590769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29750299686592045806908717 11156362382472017177590769)
                ·
                  refine ⟨8367271786854012883193077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11156362382472017177590769 8367271786854012883193077)
                  ·
                    refine ⟨784431730017563707799351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8367271786854012883193077 784431730017563707799351)
                    ·
                      rfl

theorem cell23_4583026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_4583026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583026 prefixEnd_4583026 := by exact prefixLift 4583026
  have htrace : WordTrace (prefixWord ++ tailWord_4583026) baseStart_4583026 baseEnd_4583026 := by
    simpa [prefixWord, tailWord_4583026, baseEnd_4583026] using wordTrace_append hprefix tailTrace_4583026
  have hstable : (prefixWord ++ tailWord_4583026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583026).length < 2 ^ (prefixWord ++ tailWord_4583026).sum := by decide
  have hdescent : baseEnd_4583026 < baseStart_4583026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583063 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 2, 4, 2]
def baseStart_4583063 : Nat := 118140960795 + 4583063 * 2 ^ 59
def prefixEnd_4583063 : Nat := 4983230072969 + 3 ^ 40 * 4583063 * 2
def baseEnd_4583063 : Nat := 2353314188836907478635383

theorem tailTrace_4583063 : CollatzResearch.WordTrace tailWord_4583063 prefixEnd_4583063 2353314188836907478635383 := by
  unfold tailWord_4583063
  simp only [CollatzResearch.WordTrace]
  refine ⟨167158040195352950689601843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111438693463568633793067895 167158040195352950689601843)
  ·
    refine ⟨250737060293029426034402765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167158040195352950689601843 250737060293029426034402765)
    ·
      refine ⟨94026397609886034762901037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250737060293029426034402765 94026397609886034762901037)
      ·
        refine ⟨35259899103707263036087889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94026397609886034762901037 35259899103707263036087889)
        ·
          refine ⟨26444924327780447277065917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35259899103707263036087889 26444924327780447277065917)
          ·
            refine ⟨9916846622917667728899719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26444924327780447277065917 9916846622917667728899719)
            ·
              refine ⟨14875269934376501593349579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9916846622917667728899719 14875269934376501593349579)
              ·
                refine ⟨22312904901564752390024369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14875269934376501593349579 22312904901564752390024369)
                ·
                  refine ⟨16734678676173564292518277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22312904901564752390024369 16734678676173564292518277)
                  ·
                    refine ⟨3137752251782543304847177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16734678676173564292518277 3137752251782543304847177)
                    ·
                      refine ⟨2353314188836907478635383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3137752251782543304847177 2353314188836907478635383)
                      ·
                        rfl

theorem cell23_4583063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_4583063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583063 prefixEnd_4583063 := by exact prefixLift 4583063
  have htrace : WordTrace (prefixWord ++ tailWord_4583063) baseStart_4583063 baseEnd_4583063 := by
    simpa [prefixWord, tailWord_4583063, baseEnd_4583063] using wordTrace_append hprefix tailTrace_4583063
  have hstable : (prefixWord ++ tailWord_4583063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583063).length < 2 ^ (prefixWord ++ tailWord_4583063).sum := by decide
  have hdescent : baseEnd_4583063 < baseStart_4583063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583069 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 10]
def baseStart_4583069 : Nat := 118140960795 + 4583069 * 2 ^ 59
def prefixEnd_4583069 : Nat := 4983230072969 + 3 ^ 40 * 4583069 * 2
def baseEnd_4583069 : Nat := 261479696635648272795595

theorem tailTrace_4583069 : CollatzResearch.WordTrace tailWord_4583069 prefixEnd_4583069 261479696635648272795595 := by
  unfold tailWord_4583069
  simp only [CollatzResearch.WordTrace]
  refine ⟨167158259033331213714320261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111438839355554142476213507 167158259033331213714320261)
  ·
    refine ⟨31342173568749602571435049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167158259033331213714320261 31342173568749602571435049)
    ·
      refine ⟨23506630176562201928576287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31342173568749602571435049 23506630176562201928576287)
      ·
        refine ⟨35259945264843302892864431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23506630176562201928576287 35259945264843302892864431)
        ·
          refine ⟨52889917897264954339296647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35259945264843302892864431 52889917897264954339296647)
          ·
            refine ⟨79334876845897431508944971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52889917897264954339296647 79334876845897431508944971)
            ·
              refine ⟨119002315268846147263417457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79334876845897431508944971 119002315268846147263417457)
              ·
                refine ⟨89251736451634610447563093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119002315268846147263417457 89251736451634610447563093)
                ·
                  refine ⟨261479696635648272795595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89251736451634610447563093 261479696635648272795595)
                  ·
                    rfl

theorem cell23_4583069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_4583069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583069 prefixEnd_4583069 := by exact prefixLift 4583069
  have htrace : WordTrace (prefixWord ++ tailWord_4583069) baseStart_4583069 baseEnd_4583069 := by
    simpa [prefixWord, tailWord_4583069, baseEnd_4583069] using wordTrace_append hprefix tailTrace_4583069
  have hstable : (prefixWord ++ tailWord_4583069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583069).length < 2 ^ (prefixWord ++ tailWord_4583069).sum := by decide
  have hdescent : baseEnd_4583069 < baseStart_4583069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583073 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 3, 4]
def baseStart_4583073 : Nat := 118140960795 + 4583073 * 2 ^ 59
def prefixEnd_4583073 : Nat := 4983230072969 + 3 ^ 40 * 4583073 * 2
def baseEnd_4583073 : Nat := 784439774547817479836779

theorem tailTrace_4583073 : CollatzResearch.WordTrace tailWord_4583073 prefixEnd_4583073 784439774547817479836779 := by
  unfold tailWord_4583073
  simp only [CollatzResearch.WordTrace]
  refine ⟨167158404925316722397465873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111438936616877814931643915 167158404925316722397465873)
  ·
    refine ⟨125368803693987541798099405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167158404925316722397465873 125368803693987541798099405)
    ·
      refine ⟨47013301385245328174287277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125368803693987541798099405 47013301385245328174287277)
      ·
        refine ⟨17629988019466998065357729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47013301385245328174287277 17629988019466998065357729)
        ·
          refine ⟨13222491014600248549018297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17629988019466998065357729 13222491014600248549018297)
          ·
            refine ⟨9916868260950186411763723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13222491014600248549018297 9916868260950186411763723)
            ·
              refine ⟨14875302391425279617645585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9916868260950186411763723 14875302391425279617645585)
              ·
                refine ⟨11156476793568959713234189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14875302391425279617645585 11156476793568959713234189)
                ·
                  refine ⟨4183678797588359892462821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11156476793568959713234189 4183678797588359892462821)
                  ·
                    refine ⟨784439774547817479836779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4183678797588359892462821 784439774547817479836779)
                    ·
                      rfl

theorem cell23_4583073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_4583073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583073 prefixEnd_4583073 := by exact prefixLift 4583073
  have htrace : WordTrace (prefixWord ++ tailWord_4583073) baseStart_4583073 baseEnd_4583073 := by
    simpa [prefixWord, tailWord_4583073, baseEnd_4583073] using wordTrace_append hprefix tailTrace_4583073
  have hstable : (prefixWord ++ tailWord_4583073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583073).length < 2 ^ (prefixWord ++ tailWord_4583073).sum := by decide
  have hdescent : baseEnd_4583073 < baseStart_4583073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583109 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_4583109 : Nat := 118140960795 + 4583109 * 2 ^ 59
def prefixEnd_4583109 : Nat := 4983230072969 + 3 ^ 40 * 4583109 * 2
def baseEnd_4583109 : Nat := 2353337808947014298660171

theorem tailTrace_4583109 : CollatzResearch.WordTrace tailWord_4583109 prefixEnd_4583109 2353337808947014298660171 := by
  unfold tailWord_4583109
  simp only [CollatzResearch.WordTrace]
  refine ⟨167159717953186300545776381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111439811968790867030517587 167159717953186300545776381)
  ·
    refine ⟨62684894232444862704666143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167159717953186300545776381 62684894232444862704666143)
    ·
      refine ⟨94027341348667294056999215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62684894232444862704666143 94027341348667294056999215)
      ·
        refine ⟨141041012023000941085498823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94027341348667294056999215 141041012023000941085498823)
        ·
          refine ⟨211561518034501411628248235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141041012023000941085498823 211561518034501411628248235)
          ·
            refine ⟨317342277051752117442372353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211561518034501411628248235 317342277051752117442372353)
            ·
              refine ⟨238006707788814088081779265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317342277051752117442372353 238006707788814088081779265)
              ·
                refine ⟨178505030841610566061334449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238006707788814088081779265 178505030841610566061334449)
                ·
                  refine ⟨133878773131207924546000837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178505030841610566061334449 133878773131207924546000837)
                  ·
                    refine ⟨25102269962101485852375157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133878773131207924546000837 25102269962101485852375157)
                    ·
                      refine ⟨2353337808947014298660171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25102269962101485852375157 2353337808947014298660171)
                      ·
                        rfl

theorem cell23_4583109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_4583109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583109 prefixEnd_4583109 := by exact prefixLift 4583109
  have htrace : WordTrace (prefixWord ++ tailWord_4583109) baseStart_4583109 baseEnd_4583109 := by
    simpa [prefixWord, tailWord_4583109, baseEnd_4583109] using wordTrace_append hprefix tailTrace_4583109
  have hstable : (prefixWord ++ tailWord_4583109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583109).length < 2 ^ (prefixWord ++ tailWord_4583109).sum := by decide
  have hdescent : baseEnd_4583109 < baseStart_4583109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583136 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 4]
def baseStart_4583136 : Nat := 118140960795 + 4583136 * 2 ^ 59
def prefixEnd_4583136 : Nat := 4983230072969 + 3 ^ 40 * 4583136 * 2
def baseEnd_4583136 : Nat := 2353351672924685693022547

theorem tailTrace_4583136 : CollatzResearch.WordTrace tailWord_4583136 prefixEnd_4583136 2353351672924685693022547 := by
  unfold tailWord_4583136
  simp only [CollatzResearch.WordTrace]
  refine ⟨83580351362044242078504631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111440468482725656104672841 83580351362044242078504631)
  ·
    refine ⟨125370527043066363117756947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83580351362044242078504631 125370527043066363117756947)
    ·
      refine ⟨188055790564599544676635421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125370527043066363117756947 188055790564599544676635421)
      ·
        refine ⟨70520921461724829253738283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188055790564599544676635421 70520921461724829253738283)
        ·
          refine ⟨105781382192587243880607425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70520921461724829253738283 105781382192587243880607425)
          ·
            refine ⟨79336036644440432910455569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105781382192587243880607425 79336036644440432910455569)
            ·
              refine ⟨59502027483330324682841677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79336036644440432910455569 59502027483330324682841677)
              ·
                refine ⟨22313260306248871756065629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59502027483330324682841677 22313260306248871756065629)
                ·
                  refine ⟨8367472614843326908524611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22313260306248871756065629 8367472614843326908524611)
                  ·
                    refine ⟨12551208922264990362786917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8367472614843326908524611 12551208922264990362786917)
                    ·
                      refine ⟨2353351672924685693022547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12551208922264990362786917 2353351672924685693022547)
                      ·
                        rfl

theorem cell23_4583136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_4583136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583136 prefixEnd_4583136 := by exact prefixLift 4583136
  have htrace : WordTrace (prefixWord ++ tailWord_4583136) baseStart_4583136 baseEnd_4583136 := by
    simpa [prefixWord, tailWord_4583136, baseEnd_4583136] using wordTrace_append hprefix tailTrace_4583136
  have hstable : (prefixWord ++ tailWord_4583136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583136).length < 2 ^ (prefixWord ++ tailWord_4583136).sum := by decide
  have hdescent : baseEnd_4583136 < baseStart_4583136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583146 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_4583146 : Nat := 118140960795 + 4583146 * 2 ^ 59
def prefixEnd_4583146 : Nat := 4983230072969 + 3 ^ 40 * 4583146 * 2
def baseEnd_4583146 : Nat := 784452269243743551299167

theorem tailTrace_4583146 : CollatzResearch.WordTrace tailWord_4583146 prefixEnd_4583146 784452269243743551299167 := by
  unfold tailWord_4583146
  simp only [CollatzResearch.WordTrace]
  refine ⟨41790266863513063966218323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111440711636034837243248861 41790266863513063966218323)
  ·
    refine ⟨62685400295269595949327485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41790266863513063966218323 62685400295269595949327485)
    ·
      refine ⟨23507025110726098480997807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62685400295269595949327485 23507025110726098480997807)
      ·
        refine ⟨35260537666089147721496711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23507025110726098480997807 35260537666089147721496711)
        ·
          refine ⟨52890806499133721582245067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35260537666089147721496711 52890806499133721582245067)
          ·
            refine ⟨79336209748700582373367601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52890806499133721582245067 79336209748700582373367601)
            ·
              refine ⟨59502157311525436780025701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79336209748700582373367601 59502157311525436780025701)
              ·
                refine ⟨11156654495911019396254819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59502157311525436780025701 11156654495911019396254819)
                ·
                  refine ⟨16734981743866529094382229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11156654495911019396254819 16734981743866529094382229)
                  ·
                    refine ⟨784452269243743551299167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16734981743866529094382229 784452269243743551299167)
                    ·
                      rfl

theorem cell23_4583146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_4583146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583146 prefixEnd_4583146 := by exact prefixLift 4583146
  have htrace : WordTrace (prefixWord ++ tailWord_4583146) baseStart_4583146 baseEnd_4583146 := by
    simpa [prefixWord, tailWord_4583146, baseEnd_4583146] using wordTrace_append hprefix tailTrace_4583146
  have hstable : (prefixWord ++ tailWord_4583146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583146).length < 2 ^ (prefixWord ++ tailWord_4583146).sum := by decide
  have hdescent : baseEnd_4583146 < baseStart_4583146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583153 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 4]
def baseStart_4583153 : Nat := 118140960795 + 4583153 * 2 ^ 59
def prefixEnd_4583153 : Nat := 4983230072969 + 3 ^ 40 * 4583153 * 2
def baseEnd_4583153 : Nat := 2353360402095812126509969

theorem tailTrace_4583153 : CollatzResearch.WordTrace tailWord_4583153 prefixEnd_4583153 2353360402095812126509969 := by
  unfold tailWord_4583153
  simp only [CollatzResearch.WordTrace]
  refine ⟨167161322765026896060378113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111440881843351264040252075 167161322765026896060378113)
  ·
    refine ⟨125370992073770172045283585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167161322765026896060378113 125370992073770172045283585)
    ·
      refine ⟨94028244055327629033962689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125370992073770172045283585 94028244055327629033962689)
      ·
        refine ⟨70521183041495721775472017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94028244055327629033962689 70521183041495721775472017)
        ·
          refine ⟨52890887281121791331604013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70521183041495721775472017 52890887281121791331604013)
          ·
            refine ⟨19834082730420671749351505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52890887281121791331604013 19834082730420671749351505)
            ·
              refine ⟨14875562047815503812013629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19834082730420671749351505 14875562047815503812013629)
              ·
                refine ⟨5578335767930813929505111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14875562047815503812013629 5578335767930813929505111)
                ·
                  refine ⟨8367503651896220894257667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5578335767930813929505111 8367503651896220894257667)
                  ·
                    refine ⟨12551255477844331341386501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8367503651896220894257667 12551255477844331341386501)
                    ·
                      refine ⟨2353360402095812126509969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12551255477844331341386501 2353360402095812126509969)
                      ·
                        rfl

theorem cell23_4583153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_4583153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583153 prefixEnd_4583153 := by exact prefixLift 4583153
  have htrace : WordTrace (prefixWord ++ tailWord_4583153) baseStart_4583153 baseEnd_4583153 := by
    simpa [prefixWord, tailWord_4583153, baseEnd_4583153] using wordTrace_append hprefix tailTrace_4583153
  have hstable : (prefixWord ++ tailWord_4583153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583153).length < 2 ^ (prefixWord ++ tailWord_4583153).sum := by decide
  have hdescent : baseEnd_4583153 < baseStart_4583153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583159 : List Nat := [1, 1, 3, 1, 1, 1, 15]
def baseStart_4583159 : Nat := 118140960795 + 4583159 * 2 ^ 59
def prefixEnd_4583159 : Nat := 4983230072969 + 3 ^ 40 * 4583159 * 2
def baseEnd_4583159 : Nat := 29053870160243692630061

theorem tailTrace_4583159 : CollatzResearch.WordTrace tailWord_4583159 prefixEnd_4583159 29053870160243692630061 := by
  unfold tailWord_4583159
  simp only [CollatzResearch.WordTrace]
  refine ⟨167161541603005159085096531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111441027735336772723397687 167161541603005159085096531)
  ·
    refine ⟨250742312404507738627644797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167161541603005159085096531 250742312404507738627644797)
    ·
      refine ⟨94028367151690401985366799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250742312404507738627644797 94028367151690401985366799)
      ·
        refine ⟨141042550727535602978050199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94028367151690401985366799 141042550727535602978050199)
        ·
          refine ⟨211563826091303404467075299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141042550727535602978050199 211563826091303404467075299)
          ·
            refine ⟨317345739136955106700612949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211563826091303404467075299 317345739136955106700612949)
            ·
              refine ⟨29053870160243692630061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 317345739136955106700612949 29053870160243692630061)
              ·
                rfl

theorem cell23_4583159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 15].length) (baseStart_4583159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583159 prefixEnd_4583159 := by exact prefixLift 4583159
  have htrace : WordTrace (prefixWord ++ tailWord_4583159) baseStart_4583159 baseEnd_4583159 := by
    simpa [prefixWord, tailWord_4583159, baseEnd_4583159] using wordTrace_append hprefix tailTrace_4583159
  have hstable : (prefixWord ++ tailWord_4583159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583159).length < 2 ^ (prefixWord ++ tailWord_4583159).sum := by decide
  have hdescent : baseEnd_4583159 < baseStart_4583159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583176 : List Nat := [2, 1, 3, 2, 2, 1, 4, 8]
def baseStart_4583176 : Nat := 118140960795 + 4583176 * 2 ^ 59
def prefixEnd_4583176 : Nat := 4983230072969 + 3 ^ 40 * 4583176 * 2
def baseEnd_4583176 : Nat := 87161933783365390241569

theorem tailTrace_4583176 : CollatzResearch.WordTrace tailWord_4583176 prefixEnd_4583176 87161933783365390241569 := by
  unfold tailWord_4583176
  simp only [CollatzResearch.WordTrace]
  refine ⟨83581080821971785494232691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111441441095962380658976921 83581080821971785494232691)
  ·
    refine ⟨125371621232957678241349037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83581080821971785494232691 125371621232957678241349037)
    ·
      refine ⟨47014357962359129340505889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125371621232957678241349037 47014357962359129340505889)
      ·
        refine ⟨35260768471769347005379417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47014357962359129340505889 35260768471769347005379417)
        ·
          refine ⟨26445576353827010254034563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35260768471769347005379417 26445576353827010254034563)
          ·
            refine ⟨39668364530740515381051845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26445576353827010254034563 39668364530740515381051845)
            ·
              refine ⟨7437818349513846633947221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39668364530740515381051845 7437818349513846633947221)
              ·
                refine ⟨87161933783365390241569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7437818349513846633947221 87161933783365390241569)
                ·
                  rfl

theorem cell23_4583176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 8].length) (baseStart_4583176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583176 prefixEnd_4583176 := by exact prefixLift 4583176
  have htrace : WordTrace (prefixWord ++ tailWord_4583176) baseStart_4583176 baseEnd_4583176 := by
    simpa [prefixWord, tailWord_4583176, baseEnd_4583176] using wordTrace_append hprefix tailTrace_4583176
  have hstable : (prefixWord ++ tailWord_4583176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583176).length < 2 ^ (prefixWord ++ tailWord_4583176).sum := by decide
  have hdescent : baseEnd_4583176 < baseStart_4583176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583180 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 2, 4]
def baseStart_4583180 : Nat := 118140960795 + 4583180 * 2 ^ 59
def prefixEnd_4583180 : Nat := 4983230072969 + 3 ^ 40 * 4583180 * 2
def baseEnd_4583180 : Nat := 784458088691161173624115

theorem tailTrace_4583180 : CollatzResearch.WordTrace tailWord_4583180 prefixEnd_4583180 784458088691161173624115 := by
  unfold tailWord_4583180
  simp only [CollatzResearch.WordTrace]
  refine ⟨83581153767964539835805497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111441538357286053114407329 83581153767964539835805497)
  ·
    refine ⟨62685865325973404876854123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83581153767964539835805497 62685865325973404876854123)
    ·
      refine ⟨94028797988960107315281185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62685865325973404876854123 94028797988960107315281185)
      ·
        refine ⟨70521598491720080486460889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94028797988960107315281185 70521598491720080486460889)
        ·
          refine ⟨52891198868790060364845667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70521598491720080486460889 52891198868790060364845667)
          ·
            refine ⟨79336798303185090547268501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52891198868790060364845667 79336798303185090547268501)
            ·
              refine ⟨3718912420461801119403211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79336798303185090547268501 3718912420461801119403211)
              ·
                refine ⟨5578368630692701679104817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718912420461801119403211 5578368630692701679104817)
                ·
                  refine ⟨4183776473019526259328613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5578368630692701679104817 4183776473019526259328613)
                  ·
                    refine ⟨784458088691161173624115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4183776473019526259328613 784458088691161173624115)
                    ·
                      rfl

theorem cell23_4583180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_4583180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583180 prefixEnd_4583180 := by exact prefixLift 4583180
  have htrace : WordTrace (prefixWord ++ tailWord_4583180) baseStart_4583180 baseEnd_4583180 := by
    simpa [prefixWord, tailWord_4583180, baseEnd_4583180] using wordTrace_append hprefix tailTrace_4583180
  have hstable : (prefixWord ++ tailWord_4583180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583180).length < 2 ^ (prefixWord ++ tailWord_4583180).sum := by decide
  have hdescent : baseEnd_4583180 < baseStart_4583180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583203 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 6, 1, 3]
def baseStart_4583203 : Nat := 118140960795 + 4583203 * 2 ^ 59
def prefixEnd_4583203 : Nat := 4983230072969 + 3 ^ 40 * 4583203 * 2
def baseEnd_4583203 : Nat := 2353386076128536930884739

theorem tailTrace_4583203 : CollatzResearch.WordTrace tailWord_4583203 prefixEnd_4583203 2353386076128536930884739 := by
  unfold tailWord_4583203
  simp only [CollatzResearch.WordTrace]
  refine ⟨167163146414845754599698263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111442097609897169733132175 167163146414845754599698263)
  ·
    refine ⟨250744719622268631899547395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167163146414845754599698263 250744719622268631899547395)
    ·
      refine ⟨376117079433402947849321093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250744719622268631899547395 376117079433402947849321093)
      ·
        refine ⟨70521952393763052721747705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 376117079433402947849321093 70521952393763052721747705)
        ·
          refine ⟨52891464295322289541310779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70521952393763052721747705 52891464295322289541310779)
          ·
            refine ⟨79337196442983434311966169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52891464295322289541310779 79337196442983434311966169)
            ·
              refine ⟨59502897332237575733974627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79337196442983434311966169 59502897332237575733974627)
              ·
                refine ⟨89254345998356363600961941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59502897332237575733974627 89254345998356363600961941)
                ·
                  refine ⟨4183797468672954543795091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89254345998356363600961941 4183797468672954543795091)
                  ·
                    refine ⟨6275696203009431815692637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4183797468672954543795091 6275696203009431815692637)
                    ·
                      refine ⟨2353386076128536930884739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6275696203009431815692637 2353386076128536930884739)
                      ·
                        rfl

theorem cell23_4583203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_4583203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583203 prefixEnd_4583203 := by exact prefixLift 4583203
  have htrace : WordTrace (prefixWord ++ tailWord_4583203) baseStart_4583203 baseEnd_4583203 := by
    simpa [prefixWord, tailWord_4583203, baseEnd_4583203] using wordTrace_append hprefix tailTrace_4583203
  have hstable : (prefixWord ++ tailWord_4583203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583203).length < 2 ^ (prefixWord ++ tailWord_4583203).sum := by decide
  have hdescent : baseEnd_4583203 < baseStart_4583203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583264 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 1, 3, 2]
def baseStart_4583264 : Nat := 118140960795 + 4583264 * 2 ^ 59
def prefixEnd_4583264 : Nat := 4983230072969 + 3 ^ 40 * 4583264 * 2
def baseEnd_4583264 : Nat := 2353417398448461192221959

theorem tailTrace_4583264 : CollatzResearch.WordTrace tailWord_4583264 prefixEnd_4583264 2353417398448461192221959 := by
  unfold tailWord_4583264
  simp only [CollatzResearch.WordTrace]
  refine ⟨83582685633812381008834423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111443580845083174678445897 83582685633812381008834423)
  ·
    refine ⟨125374028450718571513251635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83582685633812381008834423 125374028450718571513251635)
    ·
      refine ⟨188061042676077857269877453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125374028450718571513251635 188061042676077857269877453)
      ·
        refine ⟨70522891003529196476204045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188061042676077857269877453 70522891003529196476204045)
        ·
          refine ⟨26446084126323448678576517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70522891003529196476204045 26446084126323448678576517)
          ·
            refine ⟨4958640773685646627233097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26446084126323448678576517 4958640773685646627233097)
            ·
              refine ⟨3718980580264234970424823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4958640773685646627233097 3718980580264234970424823)
              ·
                refine ⟨5578470870396352455637235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718980580264234970424823 5578470870396352455637235)
                ·
                  refine ⟨8367706305594528683455853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5578470870396352455637235 8367706305594528683455853)
                  ·
                    refine ⟨3137889864597948256295945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8367706305594528683455853 3137889864597948256295945)
                    ·
                      refine ⟨2353417398448461192221959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3137889864597948256295945 2353417398448461192221959)
                      ·
                        rfl

theorem cell23_4583264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_4583264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583264 prefixEnd_4583264 := by exact prefixLift 4583264
  have htrace : WordTrace (prefixWord ++ tailWord_4583264) baseStart_4583264 baseEnd_4583264 := by
    simpa [prefixWord, tailWord_4583264, baseEnd_4583264] using wordTrace_append hprefix tailTrace_4583264
  have hstable : (prefixWord ++ tailWord_4583264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583264).length < 2 ^ (prefixWord ++ tailWord_4583264).sum := by decide
  have hdescent : baseEnd_4583264 < baseStart_4583264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583294 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4583294 : Nat := 118140960795 + 4583294 * 2 ^ 59
def prefixEnd_4583294 : Nat := 4983230072969 + 3 ^ 40 * 4583294 * 2
def baseEnd_4583294 : Nat := 2353432802868096074846821

theorem tailTrace_4583294 : CollatzResearch.WordTrace tailWord_4583294 prefixEnd_4583294 2353432802868096074846821 := by
  unfold tailWord_4583294
  simp only [CollatzResearch.WordTrace]
  refine ⟨20895808182189509642657617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111444310305010718094173957 20895808182189509642657617)
  ·
    refine ⟨15671856136642132231993213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20895808182189509642657617 15671856136642132231993213)
    ·
      refine ⟨5876946051240799586997455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15671856136642132231993213 5876946051240799586997455)
      ·
        refine ⟨8815419076861199380496183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5876946051240799586997455 8815419076861199380496183)
        ·
          refine ⟨13223128615291799070744275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8815419076861199380496183 13223128615291799070744275)
          ·
            refine ⟨19834692922937698606116413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13223128615291799070744275 19834692922937698606116413)
            ·
              refine ⟨7438009846101636977293655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19834692922937698606116413 7438009846101636977293655)
              ·
                refine ⟨11157014769152455465940483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7438009846101636977293655 11157014769152455465940483)
                ·
                  refine ⟨16735522153728683198910725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11157014769152455465940483 16735522153728683198910725)
                  ·
                    refine ⟨3137910403824128099795761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16735522153728683198910725 3137910403824128099795761)
                    ·
                      refine ⟨2353432802868096074846821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3137910403824128099795761 2353432802868096074846821)
                      ·
                        rfl

theorem cell23_4583294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4583294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583294 prefixEnd_4583294 := by exact prefixLift 4583294
  have htrace : WordTrace (prefixWord ++ tailWord_4583294) baseStart_4583294 baseEnd_4583294 := by
    simpa [prefixWord, tailWord_4583294, baseEnd_4583294] using wordTrace_append hprefix tailTrace_4583294
  have hstable : (prefixWord ++ tailWord_4583294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583294).length < 2 ^ (prefixWord ++ tailWord_4583294).sum := by decide
  have hdescent : baseEnd_4583294 < baseStart_4583294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583296 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 3, 7]
def baseStart_4583296 : Nat := 118140960795 + 4583296 * 2 ^ 59
def prefixEnd_4583296 : Nat := 4983230072969 + 3 ^ 40 * 4583296 * 2
def baseEnd_4583296 : Nat := 784477943276468355673937

theorem tailTrace_4583296 : CollatzResearch.WordTrace tailWord_4583296 prefixEnd_4583296 784477943276468355673937 := by
  unfold tailWord_4583296
  simp only [CollatzResearch.WordTrace]
  refine ⟨83583269201754415741416871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111444358935672554321889161 83583269201754415741416871)
  ·
    refine ⟨125374903802631623612125307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83583269201754415741416871 125374903802631623612125307)
    ·
      refine ⟨188062355703947435418187961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125374903802631623612125307 188062355703947435418187961)
      ·
        refine ⟨141046766777960576563640971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188062355703947435418187961 141046766777960576563640971)
        ·
          refine ⟨211570150166940864845461457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141046766777960576563640971 211570150166940864845461457)
          ·
            refine ⟨158677612625205648634096093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211570150166940864845461457 158677612625205648634096093)
            ·
              refine ⟨59504104734452118237786035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158677612625205648634096093 59504104734452118237786035)
              ·
                refine ⟨89256157101678177356679053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59504104734452118237786035 89256157101678177356679053)
                ·
                  refine ⟨33471058913129316508754645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89256157101678177356679053 33471058913129316508754645)
                  ·
                    refine ⟨784477943276468355673937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33471058913129316508754645 784477943276468355673937)
                    ·
                      rfl

theorem cell23_4583296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_4583296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583296 prefixEnd_4583296 := by exact prefixLift 4583296
  have htrace : WordTrace (prefixWord ++ tailWord_4583296) baseStart_4583296 baseEnd_4583296 := by
    simpa [prefixWord, tailWord_4583296, baseEnd_4583296] using wordTrace_append hprefix tailTrace_4583296
  have hstable : (prefixWord ++ tailWord_4583296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583296).length < 2 ^ (prefixWord ++ tailWord_4583296).sum := by decide
  have hdescent : baseEnd_4583296 < baseStart_4583296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583370 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_4583370 : Nat := 118140960795 + 4583370 * 2 ^ 59
def prefixEnd_4583370 : Nat := 4983230072969 + 3 ^ 40 * 4583370 * 2
def baseEnd_4583370 : Nat := 2353471827397837777496471

theorem tailTrace_4583370 : CollatzResearch.WordTrace tailWord_4583370 prefixEnd_4583370 2353471827397837777496471 := by
  unfold tailWord_4583370
  simp only [CollatzResearch.WordTrace]
  refine ⟨41792309351310185530256891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111446158270160494747351709 41792309351310185530256891)
  ·
    refine ⟨62688464026965278295385337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41792309351310185530256891 62688464026965278295385337)
    ·
      refine ⟨47016348020223958721539003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62688464026965278295385337 47016348020223958721539003)
      ·
        refine ⟨70524522030335938082308505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47016348020223958721539003 70524522030335938082308505)
        ·
          refine ⟨52893391522751953561731379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70524522030335938082308505 52893391522751953561731379)
          ·
            refine ⟨79340087284127930342597069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52893391522751953561731379 79340087284127930342597069)
            ·
              refine ⟨29752532731547973878473901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79340087284127930342597069 29752532731547973878473901)
              ·
                refine ⟨11157199774330490204427713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29752532731547973878473901 11157199774330490204427713)
                ·
                  refine ⟨8367899830747867653320785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11157199774330490204427713 8367899830747867653320785)
                  ·
                    refine ⟨6275924873060900739990589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8367899830747867653320785 6275924873060900739990589)
                    ·
                      refine ⟨2353471827397837777496471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6275924873060900739990589 2353471827397837777496471)
                      ·
                        rfl

theorem cell23_4583370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_4583370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583370 prefixEnd_4583370 := by exact prefixLift 4583370
  have htrace : WordTrace (prefixWord ++ tailWord_4583370) baseStart_4583370 baseEnd_4583370 := by
    simpa [prefixWord, tailWord_4583370, baseEnd_4583370] using wordTrace_append hprefix tailTrace_4583370
  have hstable : (prefixWord ++ tailWord_4583370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583370).length < 2 ^ (prefixWord ++ tailWord_4583370).sum := by decide
  have hdescent : baseEnd_4583370 < baseStart_4583370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583417 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 3, 1, 3]
def baseStart_4583417 : Nat := 118140960795 + 4583417 * 2 ^ 59
def prefixEnd_4583417 : Nat := 4983230072969 + 3 ^ 40 * 4583417 * 2
def baseEnd_4583417 : Nat := 2353495960988599093608755

theorem tailTrace_4583417 : CollatzResearch.WordTrace tailWord_4583417 prefixEnd_4583417 2353495960988599093608755 := by
  unfold tailWord_4583417
  simp only [CollatzResearch.WordTrace]
  refine ⟨167170951636070469147988505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111447301090713646098659003 167170951636070469147988505)
  ·
    refine ⟨125378213727052851860991379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167170951636070469147988505 125378213727052851860991379)
    ·
      refine ⟨188067320590579277791487069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125378213727052851860991379 188067320590579277791487069)
      ·
        refine ⟨70525245221467229171807651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188067320590579277791487069 70525245221467229171807651)
        ·
          refine ⟨105787867832200843757711477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70525245221467229171807651 105787867832200843757711477)
          ·
            refine ⟨9917612609268829102285451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105787867832200843757711477 9917612609268829102285451)
            ·
              refine ⟨14876418913903243653428177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9917612609268829102285451 14876418913903243653428177)
              ·
                refine ⟨11157314185427432740071133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14876418913903243653428177 11157314185427432740071133)
                ·
                  refine ⟨4183992819535287277526675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11157314185427432740071133 4183992819535287277526675)
                  ·
                    refine ⟨6275989229302930916290013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4183992819535287277526675 6275989229302930916290013)
                    ·
                      refine ⟨2353495960988599093608755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6275989229302930916290013 2353495960988599093608755)
                      ·
                        rfl

theorem cell23_4583417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_4583417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583417 prefixEnd_4583417 := by exact prefixLift 4583417
  have htrace : WordTrace (prefixWord ++ tailWord_4583417) baseStart_4583417 baseEnd_4583417 := by
    simpa [prefixWord, tailWord_4583417, baseEnd_4583417] using wordTrace_append hprefix tailTrace_4583417
  have hstable : (prefixWord ++ tailWord_4583417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583417).length < 2 ^ (prefixWord ++ tailWord_4583417).sum := by decide
  have hdescent : baseEnd_4583417 < baseStart_4583417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583420 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_4583420 : Nat := 118140960795 + 4583420 * 2 ^ 59
def prefixEnd_4583420 : Nat := 4983230072969 + 3 ^ 40 * 4583420 * 2
def baseEnd_4583420 : Nat := 784499167143520860623747

theorem tailTrace_4583420 : CollatzResearch.WordTrace tailWord_4583420 prefixEnd_4583420 784499167143520860623747 := by
  unfold tailWord_4583420
  simp only [CollatzResearch.WordTrace]
  refine ⟨83585530527529800330173857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111447374036706400440231809 83585530527529800330173857)
  ·
    refine ⟨62689147895647350247630393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83585530527529800330173857 62689147895647350247630393)
    ·
      refine ⟨47016860921735512685722795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62689147895647350247630393 47016860921735512685722795)
      ·
        refine ⟨70525291382603269028584193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47016860921735512685722795 70525291382603269028584193)
        ·
          refine ⟨52893968536952451771438145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70525291382603269028584193 52893968536952451771438145)
          ·
            refine ⟨39670476402714338828578609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52893968536952451771438145 39670476402714338828578609)
            ·
              refine ⟨29752857302035754121433957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39670476402714338828578609 29752857302035754121433957)
              ·
                refine ⟨5578660744131703897768867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29752857302035754121433957 5578660744131703897768867)
                ·
                  refine ⟨8367991116197555846653301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5578660744131703897768867 8367991116197555846653301)
                  ·
                    refine ⟨784499167143520860623747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8367991116197555846653301 784499167143520860623747)
                    ·
                      rfl

theorem cell23_4583420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_4583420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583420 prefixEnd_4583420 := by exact prefixLift 4583420
  have htrace : WordTrace (prefixWord ++ tailWord_4583420) baseStart_4583420 baseEnd_4583420 := by
    simpa [prefixWord, tailWord_4583420, baseEnd_4583420] using wordTrace_append hprefix tailTrace_4583420
  have hstable : (prefixWord ++ tailWord_4583420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583420).length < 2 ^ (prefixWord ++ tailWord_4583420).sum := by decide
  have hdescent : baseEnd_4583420 < baseStart_4583420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583440 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 4]
def baseStart_4583440 : Nat := 118140960795 + 4583440 * 2 ^ 59
def prefixEnd_4583440 : Nat := 4983230072969 + 3 ^ 40 * 4583440 * 2
def baseEnd_4583440 : Nat := 2353507771043652503621149

theorem tailTrace_4583440 : CollatzResearch.WordTrace tailWord_4583440 prefixEnd_4583440 2353507771043652503621149 := by
  unfold tailWord_4583440
  simp only [CollatzResearch.WordTrace]
  refine ⟨83585895257493572038037887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111447860343324762717383849 83585895257493572038037887)
  ·
    refine ⟨125378842886240358057056831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83585895257493572038037887 125378842886240358057056831)
    ·
      refine ⟨188068264329360537085585247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125378842886240358057056831 188068264329360537085585247)
      ·
        refine ⟨282102396494040805628377871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188068264329360537085585247 282102396494040805628377871)
        ·
          refine ⟨423153594741061208442566807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282102396494040805628377871 423153594741061208442566807)
          ·
            refine ⟨634730392111591812663850211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423153594741061208442566807 634730392111591812663850211)
            ·
              refine ⟨952095588167387718995775317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634730392111591812663850211 952095588167387718995775317)
              ·
                refine ⟨5578685086918287415990871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 952095588167387718995775317 5578685086918287415990871)
                ·
                  refine ⟨8368027630377431123986307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5578685086918287415990871 8368027630377431123986307)
                  ·
                    refine ⟨12552041445566146685979461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8368027630377431123986307 12552041445566146685979461)
                    ·
                      refine ⟨2353507771043652503621149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12552041445566146685979461 2353507771043652503621149)
                      ·
                        rfl

theorem cell23_4583440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 4].length) (baseStart_4583440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583440 prefixEnd_4583440 := by exact prefixLift 4583440
  have htrace : WordTrace (prefixWord ++ tailWord_4583440) baseStart_4583440 baseEnd_4583440 := by
    simpa [prefixWord, tailWord_4583440, baseEnd_4583440] using wordTrace_append hprefix tailTrace_4583440
  have hstable : (prefixWord ++ tailWord_4583440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583440).length < 2 ^ (prefixWord ++ tailWord_4583440).sum := by decide
  have hdescent : baseEnd_4583440 < baseStart_4583440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583474 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2]
def baseStart_4583474 : Nat := 118140960795 + 4583474 * 2 ^ 59
def prefixEnd_4583474 : Nat := 4983230072969 + 3 ^ 40 * 4583474 * 2
def baseEnd_4583474 : Nat := 2353525229385905370595993

theorem tailTrace_4583474 : CollatzResearch.WordTrace tailWord_4583474 prefixEnd_4583474 2353525229385905370595993 := by
  unfold tailWord_4583474
  simp only [CollatzResearch.WordTrace]
  refine ⟨41793257649215991970703369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111448687064575978588542317 41793257649215991970703369)
  ·
    refine ⟨31344943236911993978027527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41793257649215991970703369 31344943236911993978027527)
    ·
      refine ⟨47017414855367990967041291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31344943236911993978027527 47017414855367990967041291)
      ·
        refine ⟨70526122283051986450561937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47017414855367990967041291 70526122283051986450561937)
        ·
          refine ⟨52894591712288989837921453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70526122283051986450561937 52894591712288989837921453)
          ·
            refine ⟨19835471892108371189220545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52894591712288989837921453 19835471892108371189220545)
            ·
              refine ⟨14876603919081278391915409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19835471892108371189220545 14876603919081278391915409)
              ·
                refine ⟨11157452939310958793936557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14876603919081278391915409 11157452939310958793936557)
                ·
                  refine ⟨4184044852241609547726209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11157452939310958793936557 4184044852241609547726209)
                  ·
                    refine ⟨3138033639181207160794657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4184044852241609547726209 3138033639181207160794657)
                    ·
                      refine ⟨2353525229385905370595993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138033639181207160794657 2353525229385905370595993)
                      ·
                        rfl

theorem cell23_4583474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_4583474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583474 prefixEnd_4583474 := by exact prefixLift 4583474
  have htrace : WordTrace (prefixWord ++ tailWord_4583474) baseStart_4583474 baseEnd_4583474 := by
    simpa [prefixWord, tailWord_4583474, baseEnd_4583474] using wordTrace_append hprefix tailTrace_4583474
  have hstable : (prefixWord ++ tailWord_4583474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583474).length < 2 ^ (prefixWord ++ tailWord_4583474).sum := by decide
  have hdescent : baseEnd_4583474 < baseStart_4583474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583477 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_4583477 : Nat := 118140960795 + 4583477 * 2 ^ 59
def prefixEnd_4583477 : Nat := 4983230072969 + 3 ^ 40 * 4583477 * 2
def baseEnd_4583477 : Nat := 2353526769827868858858479

theorem tailTrace_4583477 : CollatzResearch.WordTrace tailWord_4583477 prefixEnd_4583477 2353526769827868858858479 := by
  unfold tailWord_4583477
  simp only [CollatzResearch.WordTrace]
  refine ⟨167173140015853099395172685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111448760010568732930115123 167173140015853099395172685)
  ·
    refine ⟨62689927505944912273189757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167173140015853099395172685 62689927505944912273189757)
    ·
      refine ⟨23508722814729342102446159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62689927505944912273189757 23508722814729342102446159)
      ·
        refine ⟨35263084222094013153669239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23508722814729342102446159 35263084222094013153669239)
        ·
          refine ⟨52894626333141019730503859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35263084222094013153669239 52894626333141019730503859)
          ·
            refine ⟨79341939499711529595755789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52894626333141019730503859 79341939499711529595755789)
            ·
              refine ⟨29753227312391823598408421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79341939499711529595755789 29753227312391823598408421)
              ·
                refine ⟨5578730121073466924701579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29753227312391823598408421 5578730121073466924701579)
                ·
                  refine ⟨8368095181610200387052369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5578730121073466924701579 8368095181610200387052369)
                  ·
                    refine ⟨6276071386207650290289277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8368095181610200387052369 6276071386207650290289277)
                    ·
                      refine ⟨2353526769827868858858479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6276071386207650290289277 2353526769827868858858479)
                      ·
                        rfl

theorem cell23_4583477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_4583477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583477 prefixEnd_4583477 := by exact prefixLift 4583477
  have htrace : WordTrace (prefixWord ++ tailWord_4583477) baseStart_4583477 baseEnd_4583477 := by
    simpa [prefixWord, tailWord_4583477, baseEnd_4583477] using wordTrace_append hprefix tailTrace_4583477
  have hstable : (prefixWord ++ tailWord_4583477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583477).length < 2 ^ (prefixWord ++ tailWord_4583477).sum := by decide
  have hdescent : baseEnd_4583477 < baseStart_4583477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583480 : List Nat := [2, 1, 2, 1, 6, 1, 1, 9]
def baseStart_4583480 : Nat := 118140960795 + 4583480 * 2 ^ 59
def prefixEnd_4583480 : Nat := 4983230072969 + 3 ^ 40 * 4583480 * 2
def baseEnd_4583480 : Nat := 87167715195178975819295

theorem tailTrace_4583480 : CollatzResearch.WordTrace tailWord_4583480 prefixEnd_4583480 87167715195178975819295 := by
  unfold tailWord_4583480
  simp only [CollatzResearch.WordTrace]
  refine ⟨83586624717421115453765947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111448832956561487271687929 83586624717421115453765947)
  ·
    refine ⟨125379937076131673180648921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83586624717421115453765947 125379937076131673180648921)
    ·
      refine ⟨94034952807098754885486691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125379937076131673180648921 94034952807098754885486691)
      ·
        refine ⟨141052429210648132328230037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94034952807098754885486691 141052429210648132328230037)
        ·
          refine ⟨6611832619249131202885783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 141052429210648132328230037 6611832619249131202885783)
          ·
            refine ⟨9917748928873696804328675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6611832619249131202885783 9917748928873696804328675)
            ·
              refine ⟨14876623393310545206493013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9917748928873696804328675 14876623393310545206493013)
              ·
                refine ⟨87167715195178975819295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14876623393310545206493013 87167715195178975819295)
                ·
                  rfl

theorem cell23_4583480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 9].length) (baseStart_4583480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583480 prefixEnd_4583480 := by exact prefixLift 4583480
  have htrace : WordTrace (prefixWord ++ tailWord_4583480) baseStart_4583480 baseEnd_4583480 := by
    simpa [prefixWord, tailWord_4583480, baseEnd_4583480] using wordTrace_append hprefix tailTrace_4583480
  have hstable : (prefixWord ++ tailWord_4583480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583480).length < 2 ^ (prefixWord ++ tailWord_4583480).sum := by decide
  have hdescent : baseEnd_4583480 < baseStart_4583480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583493 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_4583493 : Nat := 118140960795 + 4583493 * 2 ^ 59
def prefixEnd_4583493 : Nat := 4983230072969 + 3 ^ 40 * 4583493 * 2
def baseEnd_4583493 : Nat := 784511661839446932086135

theorem tailTrace_4583493 : CollatzResearch.WordTrace tailWord_4583493 prefixEnd_4583493 784511661839446932086135 := by
  unfold tailWord_4583493
  simp only [CollatzResearch.WordTrace]
  refine ⟨167173723583795134127755133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111449149055863422751836755 167173723583795134127755133)
  ·
    refine ⟨62690146343923175297908175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167173723583795134127755133 62690146343923175297908175)
    ·
      refine ⟨94035219515884762946862263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62690146343923175297908175 94035219515884762946862263)
      ·
        refine ⟨141052829273827144420293395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94035219515884762946862263 141052829273827144420293395)
        ·
          refine ⟨211579243910740716630440093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141052829273827144420293395 211579243910740716630440093)
          ·
            refine ⟨79342216466527768736415035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211579243910740716630440093 79342216466527768736415035)
            ·
              refine ⟨119013324699791653104622553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79342216466527768736415035 119013324699791653104622553)
              ·
                refine ⟨89259993524843739828466915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119013324699791653104622553 89259993524843739828466915)
                ·
                  refine ⟨133889990287265609742700373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89259993524843739828466915 133889990287265609742700373)
                  ·
                    refine ⟨784511661839446932086135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 133889990287265609742700373 784511661839446932086135)
                    ·
                      rfl

theorem cell23_4583493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_4583493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583493 prefixEnd_4583493 := by exact prefixLift 4583493
  have htrace : WordTrace (prefixWord ++ tailWord_4583493) baseStart_4583493 baseEnd_4583493 := by
    simpa [prefixWord, tailWord_4583493, baseEnd_4583493] using wordTrace_append hprefix tailTrace_4583493
  have hstable : (prefixWord ++ tailWord_4583493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583493).length < 2 ^ (prefixWord ++ tailWord_4583493).sum := by decide
  have hdescent : baseEnd_4583493 < baseStart_4583493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583494 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_4583494 : Nat := 118140960795 + 4583494 * 2 ^ 59
def prefixEnd_4583494 : Nat := 4983230072969 + 3 ^ 40 * 4583494 * 2
def baseEnd_4583494 : Nat := 2353535498998995292345901

theorem tailTrace_4583494 : CollatzResearch.WordTrace tailWord_4583494 prefixEnd_4583494 2353535498998995292345901 := by
  unfold tailWord_4583494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5224180001774734728079423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111449173371194340865694357 5224180001774734728079423)
  ·
    refine ⟨7836270002662102092119135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5224180001774734728079423 7836270002662102092119135)
    ·
      refine ⟨11754405003993153138178703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7836270002662102092119135 11754405003993153138178703)
      ·
        refine ⟨17631607505989729707268055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11754405003993153138178703 17631607505989729707268055)
        ·
          refine ⟨26447411258984594560902083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17631607505989729707268055 26447411258984594560902083)
          ·
            refine ⟨39671116888476891841353125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26447411258984594560902083 39671116888476891841353125)
            ·
              refine ⟨7438334416589417220253711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39671116888476891841353125 7438334416589417220253711)
              ·
                refine ⟨11157501624884125830380567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7438334416589417220253711 11157501624884125830380567)
                ·
                  refine ⟨16736252437326188745570851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11157501624884125830380567 16736252437326188745570851)
                  ·
                    refine ⟨25104378655989283118356277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16736252437326188745570851 25104378655989283118356277)
                    ·
                      refine ⟨2353535498998995292345901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25104378655989283118356277 2353535498998995292345901)
                      ·
                        rfl

theorem cell23_4583494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_4583494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583494 prefixEnd_4583494 := by exact prefixLift 4583494
  have htrace : WordTrace (prefixWord ++ tailWord_4583494) baseStart_4583494 baseEnd_4583494 := by
    simpa [prefixWord, tailWord_4583494, baseEnd_4583494] using wordTrace_append hprefix tailTrace_4583494
  have hstable : (prefixWord ++ tailWord_4583494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583494).length < 2 ^ (prefixWord ++ tailWord_4583494).sum := by decide
  have hdescent : baseEnd_4583494 < baseStart_4583494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583518 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_4583518 : Nat := 118140960795 + 4583518 * 2 ^ 59
def prefixEnd_4583518 : Nat := 4983230072969 + 3 ^ 40 * 4583518 * 2
def baseEnd_4583518 : Nat := 784515940844901066148597

theorem tailTrace_4583518 : CollatzResearch.WordTrace tailWord_4583518 prefixEnd_4583518 784515940844901066148597 := by
  unfold tailWord_4583518
  simp only [CollatzResearch.WordTrace]
  refine ⟨20896829426088070424676901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111449756939136375598276805 20896829426088070424676901)
  ·
    refine ⟨3918155517391513204626919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20896829426088070424676901 3918155517391513204626919)
    ·
      refine ⟨5877233276087269806940379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3918155517391513204626919 5877233276087269806940379)
      ·
        refine ⟨8815849914130904710410569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5877233276087269806940379 8815849914130904710410569)
        ·
          refine ⟨6611887435598178532807927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8815849914130904710410569 6611887435598178532807927)
          ·
            refine ⟨9917831153397267799211891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6611887435598178532807927 9917831153397267799211891)
            ·
              refine ⟨14876746730095901698817837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9917831153397267799211891 14876746730095901698817837)
              ·
                refine ⟨5578780023785963137056689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14876746730095901698817837 5578780023785963137056689)
                ·
                  refine ⟨4184085017839472352792517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5578780023785963137056689 4184085017839472352792517)
                  ·
                    refine ⟨784515940844901066148597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4184085017839472352792517 784515940844901066148597)
                    ·
                      rfl

theorem cell23_4583518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_4583518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583518 prefixEnd_4583518 := by exact prefixLift 4583518
  have htrace : WordTrace (prefixWord ++ tailWord_4583518) baseStart_4583518 baseEnd_4583518 := by
    simpa [prefixWord, tailWord_4583518, baseEnd_4583518] using wordTrace_append hprefix tailTrace_4583518
  have hstable : (prefixWord ++ tailWord_4583518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583518).length < 2 ^ (prefixWord ++ tailWord_4583518).sum := by decide
  have hdescent : baseEnd_4583518 < baseStart_4583518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583534 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_4583534 : Nat := 118140960795 + 4583534 * 2 ^ 59
def prefixEnd_4583534 : Nat := 4983230072969 + 3 ^ 40 * 4583534 * 2
def baseEnd_4583534 : Nat := 2353556038225175135845717

theorem tailTrace_4583534 : CollatzResearch.WordTrace tailWord_4583534 prefixEnd_4583534 2353556038225175135845717 := by
  unfold tailWord_4583534
  simp only [CollatzResearch.WordTrace]
  refine ⟨20896902372080824766249707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111450145984431065419998437 20896902372080824766249707)
  ·
    refine ⟨31345353558121237149374561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20896902372080824766249707 31345353558121237149374561)
    ·
      refine ⟨23509015168590927862030921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31345353558121237149374561 23509015168590927862030921)
      ·
        refine ⟨17631761376443195896523191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23509015168590927862030921 17631761376443195896523191)
        ·
          refine ⟨26447642064664793844784787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17631761376443195896523191 26447642064664793844784787)
          ·
            refine ⟨39671463096997190767177181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26447642064664793844784787 39671463096997190767177181)
            ·
              refine ⟨14876798661373946537691443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39671463096997190767177181 14876798661373946537691443)
              ·
                refine ⟨22315197992060919806537165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14876798661373946537691443 22315197992060919806537165)
                ·
                  refine ⟨8368199247022844927451437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22315197992060919806537165 8368199247022844927451437)
                  ·
                    refine ⟨3138074717633566847794289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8368199247022844927451437 3138074717633566847794289)
                    ·
                      refine ⟨2353556038225175135845717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138074717633566847794289 2353556038225175135845717)
                      ·
                        rfl

theorem cell23_4583534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_4583534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583534 prefixEnd_4583534 := by exact prefixLift 4583534
  have htrace : WordTrace (prefixWord ++ tailWord_4583534) baseStart_4583534 baseEnd_4583534 := by
    simpa [prefixWord, tailWord_4583534, baseEnd_4583534] using wordTrace_append hprefix tailTrace_4583534
  have hstable : (prefixWord ++ tailWord_4583534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583534).length < 2 ^ (prefixWord ++ tailWord_4583534).sum := by decide
  have hdescent : baseEnd_4583534 < baseStart_4583534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583581 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_4583581 : Nat := 118140960795 + 4583581 * 2 ^ 59
def prefixEnd_4583581 : Nat := 4983230072969 + 3 ^ 40 * 4583581 * 2
def baseEnd_4583581 : Nat := 2353580171815936451958001

theorem tailTrace_4583581 : CollatzResearch.WordTrace tailWord_4583581 prefixEnd_4583581 2353580171815936451958001 := by
  unfold tailWord_4583581
  simp only [CollatzResearch.WordTrace]
  refine ⟨167176933207476325156958597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111451288804984216771305731 167176933207476325156958597)
  ·
    refine ⟨31345674976401810966929737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167176933207476325156958597 31345674976401810966929737)
    ·
      refine ⟨23509256232301358225197303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31345674976401810966929737 23509256232301358225197303)
      ·
        refine ⟨35263884348452037337795955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23509256232301358225197303 35263884348452037337795955)
        ·
          refine ⟨52895826522678056006693933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35263884348452037337795955 52895826522678056006693933)
          ·
            refine ⟨19835934946004271002510225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52895826522678056006693933 19835934946004271002510225)
            ·
              refine ⟨14876951209503203251882669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19835934946004271002510225 14876951209503203251882669)
              ·
                refine ⟨5578856703563701219456001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14876951209503203251882669 5578856703563701219456001)
                ·
                  refine ⟨4184142527672775914592001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5578856703563701219456001 4184142527672775914592001)
                  ·
                    refine ⟨3138106895754581935944001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4184142527672775914592001 3138106895754581935944001)
                    ·
                      refine ⟨2353580171815936451958001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138106895754581935944001 2353580171815936451958001)
                      ·
                        rfl

theorem cell23_4583581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_4583581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583581 prefixEnd_4583581 := by exact prefixLift 4583581
  have htrace : WordTrace (prefixWord ++ tailWord_4583581) baseStart_4583581 baseEnd_4583581 := by
    simpa [prefixWord, tailWord_4583581, baseEnd_4583581] using wordTrace_append hprefix tailTrace_4583581
  have hstable : (prefixWord ++ tailWord_4583581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583581).length < 2 ^ (prefixWord ++ tailWord_4583581).sum := by decide
  have hdescent : baseEnd_4583581 < baseStart_4583581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583610 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_4583610 : Nat := 118140960795 + 4583610 * 2 ^ 59
def prefixEnd_4583610 : Nat := 4983230072969 + 3 ^ 40 * 4583610 * 2
def baseEnd_4583610 : Nat := 2353595062754916838495367

theorem tailTrace_4583610 : CollatzResearch.WordTrace tailWord_4583610 prefixEnd_4583610 2353595062754916838495367 := by
  unfold tailWord_4583610
  simp only [CollatzResearch.WordTrace]
  refine ⟨41794497731092815777441071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111451993949580842073176189 41794497731092815777441071)
  ·
    refine ⟨62691746596639223666161607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41794497731092815777441071 62691746596639223666161607)
    ·
      refine ⟨94037619894958835499242411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62691746596639223666161607 94037619894958835499242411)
      ·
        refine ⟨141056429842438253248863617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94037619894958835499242411 141056429842438253248863617)
        ·
          refine ⟨105792322381828689936647713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141056429842438253248863617 105792322381828689936647713)
          ·
            refine ⟨79344241786371517452485785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105792322381828689936647713 79344241786371517452485785)
            ·
              refine ⟨59508181339778638089364339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79344241786371517452485785 59508181339778638089364339)
              ·
                refine ⟨89262272009667957134046509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59508181339778638089364339 89262272009667957134046509)
                ·
                  refine ⟨33473352003625483925267441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89262272009667957134046509 33473352003625483925267441)
                  ·
                    refine ⟨25105014002719112943950581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33473352003625483925267441 25105014002719112943950581)
                    ·
                      refine ⟨2353595062754916838495367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25105014002719112943950581 2353595062754916838495367)
                      ·
                        rfl

theorem cell23_4583610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_4583610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583610 prefixEnd_4583610 := by exact prefixLift 4583610
  have htrace : WordTrace (prefixWord ++ tailWord_4583610) baseStart_4583610 baseEnd_4583610 := by
    simpa [prefixWord, tailWord_4583610, baseEnd_4583610] using wordTrace_append hprefix tailTrace_4583610
  have hstable : (prefixWord ++ tailWord_4583610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583610).length < 2 ^ (prefixWord ++ tailWord_4583610).sum := by decide
  have hdescent : baseEnd_4583610 < baseStart_4583610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583660 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 10]
def baseStart_4583660 : Nat := 118140960795 + 4583660 * 2 ^ 59
def prefixEnd_4583660 : Nat := 4983230072969 + 3 ^ 40 * 4583660 * 2
def baseEnd_4583660 : Nat := 261513415198626849207793

theorem tailTrace_4583660 : CollatzResearch.WordTrace tailWord_4583660 prefixEnd_4583660 261513415198626849207793 := by
  unfold tailWord_4583660
  simp only [CollatzResearch.WordTrace]
  refine ⟨83589907287095060824542217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111453209716126747766056289 83589907287095060824542217)
  ·
    refine ⟨62692430465321295618406663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83589907287095060824542217 62692430465321295618406663)
    ·
      refine ⟨94038645697981943427609995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62692430465321295618406663 94038645697981943427609995)
      ·
        refine ⟨141057968546972915141414993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94038645697981943427609995 141057968546972915141414993)
        ·
          refine ⟨105793476410229686356061245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141057968546972915141414993 105793476410229686356061245)
          ·
            refine ⟨39672553653836132383522967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105793476410229686356061245 39672553653836132383522967)
            ·
              refine ⟨59508830480754198575284451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39672553653836132383522967 59508830480754198575284451)
              ·
                refine ⟨89263245721131297862926677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59508830480754198575284451 89263245721131297862926677)
                ·
                  refine ⟨261513415198626849207793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89263245721131297862926677 261513415198626849207793)
                  ·
                    rfl

theorem cell23_4583660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_4583660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583660 prefixEnd_4583660 := by exact prefixLift 4583660
  have htrace : WordTrace (prefixWord ++ tailWord_4583660) baseStart_4583660 baseEnd_4583660 := by
    simpa [prefixWord, tailWord_4583660, baseEnd_4583660] using wordTrace_append hprefix tailTrace_4583660
  have hstable : (prefixWord ++ tailWord_4583660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583660).length < 2 ^ (prefixWord ++ tailWord_4583660).sum := by decide
  have hdescent : baseEnd_4583660 < baseStart_4583660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583674 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3]
def baseStart_4583674 : Nat := 118140960795 + 4583674 * 2 ^ 59
def prefixEnd_4583674 : Nat := 4983230072969 + 3 ^ 40 * 4583674 * 2
def baseEnd_4583674 : Nat := 2353627925516804588095073

theorem tailTrace_4583674 : CollatzResearch.WordTrace tailWord_4583674 prefixEnd_4583674 2353627925516804588095073 := by
  unfold tailWord_4583674
  simp only [CollatzResearch.WordTrace]
  refine ⟨41795081299034850510023519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111453550130759601360062717 41795081299034850510023519)
  ·
    refine ⟨62692621948552275765035279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41795081299034850510023519 62692621948552275765035279)
    ·
      refine ⟨94038932922828413647552919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62692621948552275765035279 94038932922828413647552919)
      ·
        refine ⟨141058399384242620471329379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94038932922828413647552919 141058399384242620471329379)
        ·
          refine ⟨211587599076363930706994069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141058399384242620471329379 211587599076363930706994069)
          ·
            refine ⟨9918168706704559251890347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211587599076363930706994069 9918168706704559251890347)
            ·
              refine ⟨14877253060056838877835521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9918168706704559251890347 14877253060056838877835521)
              ·
                refine ⟨11157939795042629158376641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14877253060056838877835521 11157939795042629158376641)
                ·
                  refine ⟨8368454846281971868782481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11157939795042629158376641 8368454846281971868782481)
                  ·
                    refine ⟨6276341134711478901586861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8368454846281971868782481 6276341134711478901586861)
                    ·
                      refine ⟨2353627925516804588095073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6276341134711478901586861 2353627925516804588095073)
                      ·
                        rfl

theorem cell23_4583674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_4583674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583674 prefixEnd_4583674 := by exact prefixLift 4583674
  have htrace : WordTrace (prefixWord ++ tailWord_4583674) baseStart_4583674 baseEnd_4583674 := by
    simpa [prefixWord, tailWord_4583674, baseEnd_4583674] using wordTrace_append hprefix tailTrace_4583674
  have hstable : (prefixWord ++ tailWord_4583674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583674).length < 2 ^ (prefixWord ++ tailWord_4583674).sum := by decide
  have hdescent : baseEnd_4583674 < baseStart_4583674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583680 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_4583680 : Nat := 118140960795 + 4583680 * 2 ^ 59
def prefixEnd_4583680 : Nat := 4983230072969 + 3 ^ 40 * 4583680 * 2
def baseEnd_4583680 : Nat := 2353631006400731564620045

theorem tailTrace_4583680 : CollatzResearch.WordTrace tailWord_4583680 prefixEnd_4583680 2353631006400731564620045 := by
  unfold tailWord_4583680
  simp only [CollatzResearch.WordTrace]
  refine ⟨83590272017058832532406247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111453696022745110043208329 83590272017058832532406247)
  ·
    refine ⟨125385408025588248798609371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83590272017058832532406247 125385408025588248798609371)
    ·
      refine ⟨188078112038382373197914057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125385408025588248798609371 188078112038382373197914057)
      ·
        refine ⟨141058584028786779898435543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188078112038382373197914057 141058584028786779898435543)
        ·
          refine ⟨211587876043180169847653315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141058584028786779898435543 211587876043180169847653315)
          ·
            refine ⟨317381814064770254771479973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211587876043180169847653315 317381814064770254771479973)
            ·
              refine ⟨59509090137144422769652495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 317381814064770254771479973 59509090137144422769652495)
              ·
                refine ⟨89263635205716634154478743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59509090137144422769652495 89263635205716634154478743)
                ·
                  refine ⟨133895452808574951231718115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89263635205716634154478743 133895452808574951231718115)
                  ·
                    refine ⟨200843179212862426847577173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133895452808574951231718115 200843179212862426847577173)
                    ·
                      refine ⟨2353631006400731564620045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 200843179212862426847577173 2353631006400731564620045)
                      ·
                        rfl

theorem cell23_4583680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_4583680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583680 prefixEnd_4583680 := by exact prefixLift 4583680
  have htrace : WordTrace (prefixWord ++ tailWord_4583680) baseStart_4583680 baseEnd_4583680 := by
    simpa [prefixWord, tailWord_4583680, baseEnd_4583680] using wordTrace_append hprefix tailTrace_4583680
  have hstable : (prefixWord ++ tailWord_4583680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583680).length < 2 ^ (prefixWord ++ tailWord_4583680).sum := by decide
  have hdescent : baseEnd_4583680 < baseStart_4583680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583704 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 5, 1, 3]
def baseStart_4583704 : Nat := 118140960795 + 4583704 * 2 ^ 59
def prefixEnd_4583704 : Nat := 4983230072969 + 3 ^ 40 * 4583704 * 2
def baseEnd_4583704 : Nat := 2353643329936439470719935

theorem tailTrace_4583704 : CollatzResearch.WordTrace tailWord_4583704 prefixEnd_4583704 2353643329936439470719935 := by
  unfold tailWord_4583704
  simp only [CollatzResearch.WordTrace]
  refine ⟨83590709693015358581843083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111454279590687144775790777 83590709693015358581843083)
  ·
    refine ⟨125386064539523037872764625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83590709693015358581843083 125386064539523037872764625)
    ·
      refine ⟨94039548404642278404573469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125386064539523037872764625 94039548404642278404573469)
      ·
        refine ⟨35264830651740854401715051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94039548404642278404573469 35264830651740854401715051)
        ·
          refine ⟨52897245977611281602572577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35264830651740854401715051 52897245977611281602572577)
          ·
            refine ⟨39672934483208461201929433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52897245977611281602572577 39672934483208461201929433)
            ·
              refine ⟨29754700862406345901447075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39672934483208461201929433 29754700862406345901447075)
              ·
                refine ⟨44632051293609518852170613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29754700862406345901447075 44632051293609518852170613)
                ·
                  refine ⟨4184254808775892392390995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44632051293609518852170613 4184254808775892392390995)
                  ·
                    refine ⟨6276382213163838588586493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4184254808775892392390995 6276382213163838588586493)
                    ·
                      refine ⟨2353643329936439470719935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6276382213163838588586493 2353643329936439470719935)
                      ·
                        rfl

theorem cell23_4583704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_4583704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583704 prefixEnd_4583704 := by exact prefixLift 4583704
  have htrace : WordTrace (prefixWord ++ tailWord_4583704) baseStart_4583704 baseEnd_4583704 := by
    simpa [prefixWord, tailWord_4583704, baseEnd_4583704] using wordTrace_append hprefix tailTrace_4583704
  have hstable : (prefixWord ++ tailWord_4583704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583704).length < 2 ^ (prefixWord ++ tailWord_4583704).sum := by decide
  have hdescent : baseEnd_4583704 < baseStart_4583704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583738 : List Nat := [3, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3]
def baseStart_4583738 : Nat := 118140960795 + 4583738 * 2 ^ 59
def prefixEnd_4583738 : Nat := 4983230072969 + 3 ^ 40 * 4583738 * 2
def baseEnd_4583738 : Nat := 2353660788278692337694779

theorem tailTrace_4583738 : CollatzResearch.WordTrace tailWord_4583738 prefixEnd_4583738 2353660788278692337694779 := by
  unfold tailWord_4583738
  simp only [CollatzResearch.WordTrace]
  refine ⟨41795664866976885242605967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111455106311938360646949245 41795664866976885242605967)
  ·
    refine ⟨62693497300465327863908951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41795664866976885242605967 62693497300465327863908951)
    ·
      refine ⟨94040245950697991795863427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62693497300465327863908951 94040245950697991795863427)
      ·
        refine ⟨141060368926046987693795141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94040245950697991795863427 141060368926046987693795141)
        ·
          refine ⟨26448819173633810192586589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141060368926046987693795141 26448819173633810192586589)
          ·
            refine ⟨9918307190112678822219971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26448819173633810192586589 9918307190112678822219971)
            ·
              refine ⟨14877460785169018233329957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9918307190112678822219971 14877460785169018233329957)
              ·
                refine ⟨2789523897219190918749367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14877460785169018233329957 2789523897219190918749367)
                ·
                  refine ⟨4184285845828786378124051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2789523897219190918749367 4184285845828786378124051)
                  ·
                    refine ⟨6276428768743179567186077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4184285845828786378124051 6276428768743179567186077)
                    ·
                      refine ⟨2353660788278692337694779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6276428768743179567186077 2353660788278692337694779)
                      ·
                        rfl

theorem cell23_4583738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3].length) (baseStart_4583738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583738 prefixEnd_4583738 := by exact prefixLift 4583738
  have htrace : WordTrace (prefixWord ++ tailWord_4583738) baseStart_4583738 baseEnd_4583738 := by
    simpa [prefixWord, tailWord_4583738, baseEnd_4583738] using wordTrace_append hprefix tailTrace_4583738
  have hstable : (prefixWord ++ tailWord_4583738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583738).length < 2 ^ (prefixWord ++ tailWord_4583738).sum := by decide
  have hdescent : baseEnd_4583738 < baseStart_4583738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583747 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 5]
def baseStart_4583747 : Nat := 118140960795 + 4583747 * 2 ^ 59
def prefixEnd_4583747 : Nat := 4983230072969 + 3 ^ 40 * 4583747 * 2
def baseEnd_4583747 : Nat := 2353665409604582802482237

theorem tailTrace_4583747 : CollatzResearch.WordTrace tailWord_4583747 prefixEnd_4583747 2353665409604582802482237 := by
  unfold tailWord_4583747
  simp only [CollatzResearch.WordTrace]
  refine ⟨167182987724874935507501495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111455325149916623671667663 167182987724874935507501495)
  ·
    refine ⟨250774481587312403261252243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167182987724874935507501495 250774481587312403261252243)
    ·
      refine ⟨376161722380968604891878365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250774481587312403261252243 376161722380968604891878365)
      ·
        refine ⟨141060645892863226834454387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376161722380968604891878365 141060645892863226834454387)
        ·
          refine ⟨211590968839294840251681581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141060645892863226834454387 211590968839294840251681581)
          ·
            refine ⟨79346613314735565094380593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211590968839294840251681581 79346613314735565094380593)
            ·
              refine ⟨59509959986051673820785445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79346613314735565094380593 59509959986051673820785445)
              ·
                refine ⟨11158117497384688841397271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59509959986051673820785445 11158117497384688841397271)
                ·
                  refine ⟨16737176246077033262095907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11158117497384688841397271 16737176246077033262095907)
                  ·
                    refine ⟨25105764369115549893143861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16737176246077033262095907 25105764369115549893143861)
                    ·
                      refine ⟨2353665409604582802482237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25105764369115549893143861 2353665409604582802482237)
                      ·
                        rfl

theorem cell23_4583747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_4583747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583747 prefixEnd_4583747 := by exact prefixLift 4583747
  have htrace : WordTrace (prefixWord ++ tailWord_4583747) baseStart_4583747 baseEnd_4583747 := by
    simpa [prefixWord, tailWord_4583747, baseEnd_4583747] using wordTrace_append hprefix tailTrace_4583747
  have hstable : (prefixWord ++ tailWord_4583747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583747).length < 2 ^ (prefixWord ++ tailWord_4583747).sum := by decide
  have hdescent : baseEnd_4583747 < baseStart_4583747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583761 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 5, 2, 2]
def baseStart_4583761 : Nat := 118140960795 + 4583761 * 2 ^ 59
def prefixEnd_4583761 : Nat := 4983230072969 + 3 ^ 40 * 4583761 * 2
def baseEnd_4583761 : Nat := 2353672598333745747707173

theorem tailTrace_4583761 : CollatzResearch.WordTrace tailWord_4583761 prefixEnd_4583761 2353672598333745747707173 := by
  unfold tailWord_4583761
  simp only [CollatzResearch.WordTrace]
  refine ⟨167183498346824215898511137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111455665564549477265674091 167183498346824215898511137)
  ·
    refine ⟨125387623760118161923883353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167183498346824215898511137 125387623760118161923883353)
    ·
      refine ⟨94040717820088621442912515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125387623760118161923883353 94040717820088621442912515)
      ·
        refine ⟨141061076730132932164368773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94040717820088621442912515 141061076730132932164368773)
        ·
          refine ⟨26448951886899924780819145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141061076730132932164368773 26448951886899924780819145)
          ·
            refine ⟨19836713915174943585614359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26448951886899924780819145 19836713915174943585614359)
            ·
              refine ⟨29755070872762415378421539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19836713915174943585614359 29755070872762415378421539)
              ·
                refine ⟨44632606309143623067632309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29755070872762415378421539 44632606309143623067632309)
                ·
                  refine ⟨4184306841482214662590529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44632606309143623067632309 4184306841482214662590529)
                  ·
                    refine ⟨3138230131111660996942897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4184306841482214662590529 3138230131111660996942897)
                    ·
                      refine ⟨2353672598333745747707173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138230131111660996942897 2353672598333745747707173)
                      ·
                        rfl

theorem cell23_4583761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_4583761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583761 prefixEnd_4583761 := by exact prefixLift 4583761
  have htrace : WordTrace (prefixWord ++ tailWord_4583761) baseStart_4583761 baseEnd_4583761 := by
    simpa [prefixWord, tailWord_4583761, baseEnd_4583761] using wordTrace_append hprefix tailTrace_4583761
  have hstable : (prefixWord ++ tailWord_4583761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583761).length < 2 ^ (prefixWord ++ tailWord_4583761).sum := by decide
  have hdescent : baseEnd_4583761 < baseStart_4583761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583765 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 2, 3, 2]
def baseStart_4583765 : Nat := 118140960795 + 4583765 * 2 ^ 59
def prefixEnd_4583765 : Nat := 4983230072969 + 3 ^ 40 * 4583765 * 2
def baseEnd_4583765 : Nat := 2353674652256363732057155

theorem tailTrace_4583765 : CollatzResearch.WordTrace tailWord_4583765 prefixEnd_4583765 2353674652256363732057155 := by
  unfold tailWord_4583765
  simp only [CollatzResearch.WordTrace]
  refine ⟨167183644238809724581656749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111455762825873149721104499 167183644238809724581656749)
  ·
    refine ⟨62693866589553646718121281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167183644238809724581656749 62693866589553646718121281)
    ·
      refine ⟨47020399942165235038590961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62693866589553646718121281 47020399942165235038590961)
      ·
        refine ⟨35265299956623926278943221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47020399942165235038590961 35265299956623926278943221)
        ·
          refine ⟨3306121870933493088650927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35265299956623926278943221 3306121870933493088650927)
          ·
            refine ⟨4959182806400239632976391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306121870933493088650927 4959182806400239632976391)
            ·
              refine ⟨7438774209600359449464587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959182806400239632976391 7438774209600359449464587)
              ·
                refine ⟨11158161314400539174196881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7438774209600359449464587 11158161314400539174196881)
                ·
                  refine ⟨8368620985800404380647661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11158161314400539174196881 8368620985800404380647661)
                  ·
                    refine ⟨3138232869675151642742873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8368620985800404380647661 3138232869675151642742873)
                    ·
                      refine ⟨2353674652256363732057155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138232869675151642742873 2353674652256363732057155)
                      ·
                        rfl

theorem cell23_4583765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_4583765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583765 prefixEnd_4583765 := by exact prefixLift 4583765
  have htrace : WordTrace (prefixWord ++ tailWord_4583765) baseStart_4583765 baseEnd_4583765 := by
    simpa [prefixWord, tailWord_4583765, baseEnd_4583765] using wordTrace_append hprefix tailTrace_4583765
  have hstable : (prefixWord ++ tailWord_4583765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583765).length < 2 ^ (prefixWord ++ tailWord_4583765).sum := by decide
  have hdescent : baseEnd_4583765 < baseStart_4583765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
